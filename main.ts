// main.ts is mend, the CLI SPEC.md specifies. Node 22, the standard library alone; run it as
// `node main.ts [options] [PATCH]`.
//
// It implements all of SPEC.md: the command line, output and exit codes, safe paths, format
// detection, three-tier line matching (section 5), unified diffs (section 6), SEARCH/REPLACE
// blocks (section 7), V4A patches (section 8), JSON edits (section 9) and all-or-nothing
// application (section 10).
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set, and then this file
// hands over to runner.ts (the last lines below): keep that hand-over and runner.ts as they are.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** A file as lines: its own break, its lines, whether it ends with a break (SPEC.md section 3). */
interface FileState {
  br: string;
  lines: string[];
  fin: boolean;
}

function splitFile(text: string): FileState {
  if (text === '') return { br: '\n', lines: [], fin: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const parts = text.split(br);
  const fin = text.endsWith(br);
  if (fin) parts.pop();
  return { br, lines: parts, fin };
}

function joinFile(f: FileState): string {
  if (f.lines.length === 0) return '';
  return f.lines.join(f.br) + (f.fin ? f.br : '');
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  readonly moves: Array<[string, string]> = [];
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
  recordMove(oldP: string, newP: string): void {
    this.moves.push([oldP, newP]);
  }
}

type Edit = (tree: Tree) => void;

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

// ---------------------------------------------------------------------------
// Section 5: matching lines at three tiers.
// ---------------------------------------------------------------------------

function lineKey(line: string, tier: number): string {
  if (tier === 0) return line;
  let end = line.length;
  while (end > 0 && (line[end - 1] === ' ' || line[end - 1] === '\t')) end -= 1;
  if (tier === 1) return line.slice(0, end);
  let start = 0;
  while (start < end && (line[start] === ' ' || line[start] === '\t')) start += 1;
  return line.slice(start, end);
}

function leadingWs(line: string): string {
  let i = 0;
  while (i < line.length && (line[i] === ' ' || line[i] === '\t')) i += 1;
  return line.slice(0, i);
}

function onlyWs(line: string): boolean {
  for (let i = 0; i < line.length; i += 1) {
    if (line[i] !== ' ' && line[i] !== '\t') return false;
  }
  return true;
}

/** All 0-based positions where O occurs in fileLines at the given tier. */
function occurrencesAt(fileLines: string[], oKeys: string[], tier: number): number[] {
  const out: number[] = [];
  const k = oKeys.length;
  const n = fileLines.length;
  for (let i = 0; i + k <= n; i += 1) {
    let m = true;
    for (let j = 0; j < k; j += 1) {
      if (lineKey(fileLines[i + j]!, tier) !== oKeys[j]) {
        m = false;
        break;
      }
    }
    if (m) out.push(i);
  }
  return out;
}

interface Found {
  tier: number;
  occ: number[];
}

/**
 * The first tier (0, then 1, then 2; only 0 when strict) at which O occurs in fileLines at
 * or after `from`, restricted to occurrences satisfying `keep` when given.
 */
function findTier(
  fileLines: string[],
  oldLines: string[],
  strict: boolean,
  from: number,
  keep?: (pos: number) => boolean,
): Found | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    const keys = oldLines.map((l) => lineKey(l, t));
    let occ = occurrencesAt(fileLines, keys, t);
    occ = occ.filter((p) => p >= from && (keep === undefined || keep(p)));
    if (occ.length > 0) return { tier: t, occ };
  }
  return null;
}

/** One old line: its text, and whether it is a context line (also in N). */
interface OldItem {
  text: string;
  ctx: boolean;
}
/** One new line: its text, and the index into O of the context line it is, or -1. */
interface NewItem {
  text: string;
  oIndex: number;
}

/**
 * The lines that replace a match at `pos`: context lines are the file's own matched lines,
 * other lines are re-indented at tier 2 (SPEC.md section 5).
 */
function buildReplacement(fileLines: string[], pos: number, o: OldItem[], n: NewItem[], tier: number): string[] {
  const out: string[] = [];
  let p = '';
  let f = '';
  if (tier === 2 && o.length > 0) {
    p = leadingWs(o[0]!.text);
    f = leadingWs(fileLines[pos]!);
  }
  for (const item of n) {
    if (item.oIndex >= 0) {
      out.push(fileLines[pos + item.oIndex]!);
      continue;
    }
    let t = item.text;
    if (tier === 2 && t !== '' && !onlyWs(t) && t.startsWith(p)) t = f + t.slice(p.length);
    out.push(t);
  }
  return out;
}

// ---------------------------------------------------------------------------
// Section 9: JSON edits (as the kit's starter had them).
// ---------------------------------------------------------------------------

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, lines.length === 0 ? '' : lines.join(br) + (final ? br : ''));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

// ---------------------------------------------------------------------------
// Section 6: unified diffs.
// ---------------------------------------------------------------------------

interface HunkItem {
  kind: ' ' | '-' | '+';
  text: string;
  bs: boolean;
}

interface Hunk {
  a: number;
  items: HunkItem[];
}

interface Section {
  oldPath: string | null;
  newPath: string | null;
  isCreate: boolean;
  isDelete: boolean;
  hunks: Hunk[];
}

/** A `--- ` / `+++ ` path: text after the four characters, up to the first tab, trimmed. */
function uniPath(raw: string): string | null {
  let p = raw.split('\t')[0]!.trim();
  if (p === '/dev/null') return null;
  if (p.startsWith('a/')) p = p.slice(2);
  else if (p.startsWith('b/')) p = p.slice(2);
  return p;
}

function parseDiffGit(line: string): [string, string] | null {
  const rest = line.slice('diff --git '.length).trimEnd();
  if (!rest.startsWith('a/')) return null;
  const sep = rest.indexOf(' b/', 2);
  if (sep < 0) return null;
  const x = rest.slice(2, sep);
  const y = rest.slice(sep + 3);
  if (x === '' || y === '') return null;
  return [x, y];
}

function parseHunkHeader(line: string): number | null {
  const m = /^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@/.exec(line);
  if (m === null) return null;
  return Number(m[1]);
}

function parseUnified(lines: string[]): Section[] {
  const sections: Section[] = [];
  let cur: Section | null = null;
  let inHeader = false;
  // Per side, where the path came from: 'git' (diff --git), 'dash' (---/+++), 'rename'.
  let oldSrc = '';
  let newSrc = '';
  let i = 0;
  while (i < lines.length) {
    const line = lines[i]!;
    if (line.startsWith('diff --git ')) {
      const paths = parseDiffGit(line);
      if (paths === null) throw new Exit2(`error: parse ${i + 1}`);
      cur = { oldPath: paths[0], newPath: paths[1], isCreate: false, isDelete: false, hunks: [] };
      sections.push(cur);
      oldSrc = 'git';
      newSrc = 'git';
      inHeader = true;
      i += 1;
      continue;
    }
    if (line.startsWith('@@')) {
      if (cur === null) throw new Exit2(`error: parse ${i + 1}`);
      const a = parseHunkHeader(line);
      if (a === null) throw new Exit2(`error: parse ${i + 1}`);
      inHeader = false;
      const items: HunkItem[] = [];
      let j = i + 1;
      while (j < lines.length) {
        const bl = lines[j]!;
        if (bl.startsWith('--- ') && (lines[j + 1] ?? '').startsWith('+++ ')) break;
        if (bl === '' || bl.startsWith(' ') || bl.startsWith('-') || bl.startsWith('+')) {
          items.push({ kind: bl === '' ? ' ' : (bl[0] as ' ' | '-' | '+'), text: bl === '' ? '' : bl.slice(1), bs: false });
          j += 1;
        } else if (bl.startsWith('\\')) {
          if (items.length > 0) items[items.length - 1]!.bs = true;
          j += 1;
        } else break;
      }
      while (items.length > 0) {
        const last = items[items.length - 1]!;
        if (last.kind === ' ' && last.text === '') items.pop();
        else break;
      }
      cur.hunks.push({ a, items });
      i = j;
      continue;
    }
    if (cur !== null && inHeader && line.startsWith('--- ')) {
      const next = lines[i + 1];
      if (next === undefined || !next.startsWith('+++ ')) throw new Exit2(`error: parse ${i + 2}`);
      cur.oldPath = uniPath(line.slice(4));
      cur.newPath = uniPath(next.slice(4));
      oldSrc = 'dash';
      newSrc = 'dash';
      i += 2;
      continue;
    }
    if (cur !== null && inHeader && line.startsWith('+++ ')) {
      cur.newPath = uniPath(line.slice(4));
      newSrc = 'dash';
      i += 1;
      continue;
    }
    if (cur !== null && inHeader && line.startsWith('rename from ')) {
      if (oldSrc !== 'dash') {
        cur.oldPath = line.slice('rename from '.length).trim();
        oldSrc = 'rename';
      }
      i += 1;
      continue;
    }
    if (cur !== null && inHeader && line.startsWith('rename to ')) {
      if (newSrc !== 'dash') {
        cur.newPath = line.slice('rename to '.length).trim();
        newSrc = 'rename';
      }
      i += 1;
      continue;
    }
    if (cur !== null && inHeader && line.startsWith('new file mode')) {
      cur.isCreate = true;
      i += 1;
      continue;
    }
    if (cur !== null && inHeader && line.startsWith('deleted file mode')) {
      cur.isDelete = true;
      i += 1;
      continue;
    }
    if (line.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      cur = { oldPath: uniPath(line.slice(4)), newPath: uniPath(lines[i + 1]!.slice(4)), isCreate: false, isDelete: false, hunks: [] };
      sections.push(cur);
      oldSrc = 'dash';
      newSrc = 'dash';
      inHeader = true;
      i += 2;
      continue;
    }
    i += 1;
  }
  return sections;
}

/** Apply a section's hunks in order to a file's text; throws Fail('no-match', path). */
function applyHunks(before: string, hunks: Hunk[], strict: boolean, path: string): string {
  const fs = splitFile(before);
  let d = 0;
  for (const h of hunks) {
    const o: OldItem[] = [];
    const n: NewItem[] = [];
    for (const it of h.items) {
      if (it.kind === ' ') {
        const idx = o.length;
        o.push({ text: it.text, ctx: true });
        n.push({ text: it.text, oIndex: idx });
      } else if (it.kind === '-') {
        o.push({ text: it.text, ctx: false });
      } else {
        n.push({ text: it.text, oIndex: -1 });
      }
    }
    let lastBs = false;
    for (let k = h.items.length - 1; k >= 0; k -= 1) {
      const it = h.items[k]!;
      if (it.kind === ' ' || it.kind === '+') {
        lastBs = it.bs;
        break;
      }
    }
    if (o.length === 0) {
      const pos = Math.max(0, Math.min(h.a + d, fs.lines.length));
      const rep = n.map((x) => x.text);
      const atEnd = pos === fs.lines.length;
      fs.lines.splice(pos, 0, ...rep);
      if (atEnd) fs.fin = !lastBs;
    } else {
      const found = findTier(fs.lines, o.map((x) => x.text), strict, 0);
      if (found === null) throw new Fail('no-match', path);
      const target = h.a - 1 + d;
      let best = found.occ[0]!;
      let bestDist = Math.abs(best - target);
      for (const p of found.occ) {
        const dist = Math.abs(p - target);
        if (dist < bestDist) {
          best = p;
          bestDist = dist;
        }
      }
      const rep = buildReplacement(fs.lines, best, o, n, found.tier);
      const atEnd = best + o.length === fs.lines.length;
      fs.lines.splice(best, o.length, ...rep);
      if (atEnd) fs.fin = !lastBs;
    }
    d += n.length - o.length;
  }
  return joinFile(fs);
}

function unifiedEdits(lines: string[], strict: boolean): Edit[] {
  const sections = parseUnified(lines);
  if (sections.length === 0) throw new Exit2('error: parse 1');
  return sections.map((sec) => {
    const oldP = sec.oldPath;
    const newP = sec.newPath;
    return (tree: Tree): void => {
      if (oldP !== null && !safe(oldP)) throw new Fail('unsafe', oldP);
      if (newP !== null && !safe(newP)) throw new Fail('unsafe', newP);
      if (sec.isCreate || oldP === null) {
        if (newP === null) return;
        if (tree.get(newP) !== null) throw new Fail('exists', newP);
        const plus: string[] = [];
        let lastBs = false;
        let hasPlus = false;
        for (const h of sec.hunks) {
          for (const it of h.items) {
            if (it.kind === '+') {
              plus.push(it.text);
              lastBs = it.bs;
              hasPlus = true;
            }
          }
        }
        const fin = hasPlus ? !lastBs : true;
        tree.now.set(newP, plus.length === 0 ? '' : plus.join('\n') + (fin ? '\n' : ''));
        return;
      }
      if (sec.isDelete || newP === null) {
        if (tree.get(oldP) === null) throw new Fail('missing', oldP);
        tree.now.set(oldP, null);
        return;
      }
      if (oldP !== newP) {
        const before = tree.get(oldP);
        if (before === null) throw new Fail('missing', oldP);
        if (tree.get(newP) !== null) throw new Fail('exists', newP);
        const result = applyHunks(before, sec.hunks, strict, oldP);
        tree.now.set(oldP, null);
        tree.now.set(newP, result);
        tree.recordMove(oldP, newP);
        return;
      }
      const before = tree.get(oldP);
      if (before === null) throw new Fail('missing', oldP);
      tree.now.set(oldP, applyHunks(before, sec.hunks, strict, oldP));
    };
  });
}

// ---------------------------------------------------------------------------
// Section 7: SEARCH/REPLACE blocks.
// ---------------------------------------------------------------------------

function searchReplaceEdits(lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  let lastPath: string | null = null;
  let boundary = 0;
  let i = 0;
  while (i < lines.length) {
    let s = -1;
    for (let j = i; j < lines.length; j += 1) {
      if (lines[j]!.trimEnd() === '<<<<<<< SEARCH') {
        s = j;
        break;
      }
    }
    if (s < 0) break;
    let path: string | null = null;
    for (let j = s - 1; j >= boundary; j -= 1) {
      const t = lines[j]!.trim();
      if (t === '') continue;
      if (t.startsWith('```')) continue;
      path = t;
      break;
    }
    if (path === null) {
      if (lastPath === null) throw new Exit2(`error: parse ${s + 1}`);
      path = lastPath;
    }
    let eq = -1;
    for (let j = s + 1; j < lines.length; j += 1) {
      const t = lines[j]!.trimEnd();
      if (t === '=======') {
        eq = j;
        break;
      }
      if (t === '>>>>>>> REPLACE' || t === '<<<<<<< SEARCH') break;
    }
    if (eq < 0) throw new Exit2(`error: parse ${s + 1}`);
    let rep = -1;
    for (let j = eq + 1; j < lines.length; j += 1) {
      const t = lines[j]!.trimEnd();
      if (t === '>>>>>>> REPLACE') {
        rep = j;
        break;
      }
      if (t === '<<<<<<< SEARCH') break;
    }
    if (rep < 0) throw new Exit2(`error: parse ${s + 1}`);
    const oldLines = lines.slice(s + 1, eq);
    const newLines = lines.slice(eq + 1, rep);
    const p = path;
    edits.push((tree: Tree): void => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (oldLines.length === 0) {
        if (tree.get(p) !== null) throw new Fail('exists', p);
        tree.now.set(p, newLines.length === 0 ? '' : newLines.join('\n') + '\n');
        return;
      }
      const before = tree.get(p);
      if (before === null) throw new Fail('missing', p);
      const fs = splitFile(before);
      const found = findTier(fs.lines, oldLines, strict, 0);
      if (found === null) throw new Fail('no-match', p);
      if (found.occ.length > 1) throw new Fail('ambiguous', p);
      const pos = found.occ[0]!;
      const o: OldItem[] = oldLines.map((t) => ({ text: t, ctx: false }));
      const n: NewItem[] = newLines.map((t) => ({ text: t, oIndex: -1 }));
      const repLines = buildReplacement(fs.lines, pos, o, n, found.tier);
      fs.lines.splice(pos, oldLines.length, ...repLines);
      tree.now.set(p, joinFile(fs));
    });
    lastPath = p;
    boundary = rep + 1;
    i = rep + 1;
  }
  if (edits.length === 0) throw new Exit2('error: parse 1');
  return edits;
}

// ---------------------------------------------------------------------------
// Section 8: V4A patches.
// ---------------------------------------------------------------------------

interface VChunk {
  anchor: string | null;
  eof: boolean;
  o: OldItem[];
  n: NewItem[];
}

function v4aEdits(lines: string[], strict: boolean): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = -1;
  for (let k = lines.length - 1; k >= 0; k -= 1) {
    if (!blank(lines[k]!)) {
      last = k;
      break;
    }
  }
  if (lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const edits: Edit[] = [];
  let i = first + 1;
  while (i <= last) {
    const line = lines[i]!;
    if (blank(line)) {
      i += 1;
      continue;
    }
    if (line.trim() === '*** End Patch') {
      i += 1;
      continue;
    }
    let kind: 'add' | 'delete' | 'update' | null = null;
    let path = '';
    if (line.startsWith('*** Add File: ')) {
      kind = 'add';
      path = line.slice(14).trim();
    } else if (line.startsWith('*** Delete File: ')) {
      kind = 'delete';
      path = line.slice(17).trim();
    } else if (line.startsWith('*** Update File: ')) {
      kind = 'update';
      path = line.slice(17).trim();
    } else {
      throw new Exit2(`error: parse ${i + 1}`);
    }
    const startLine = i + 1;
    i += 1;
    const secIdx: number[] = [];
    while (i <= last) {
      const l = lines[i]!;
      if (l.trim() === '*** End Patch') break;
      if (l.startsWith('*** Add File: ') || l.startsWith('*** Delete File: ') || l.startsWith('*** Update File: ')) break;
      secIdx.push(i);
      i += 1;
    }
    while (secIdx.length > 0 && blank(lines[secIdx[secIdx.length - 1]!]!)) secIdx.pop();
    if (kind === 'add') {
      const fileLines: string[] = [];
      for (const idx of secIdx) {
        const l = lines[idx]!;
        if (l === '') fileLines.push('');
        else if (l.startsWith('+')) fileLines.push(l.slice(1));
        else throw new Exit2(`error: parse ${idx + 1}`);
      }
      const p = path;
      edits.push((tree: Tree): void => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) !== null) throw new Fail('exists', p);
        tree.now.set(p, fileLines.length === 0 ? '' : fileLines.join('\n') + '\n');
      });
    } else if (kind === 'delete') {
      if (secIdx.length > 0) throw new Exit2(`error: parse ${secIdx[0]! + 1}`);
      const p = path;
      edits.push((tree: Tree): void => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) === null) throw new Fail('missing', p);
        tree.now.set(p, null);
      });
    } else {
      let moveTo: string | null = null;
      let q = 0;
      if (q < secIdx.length && lines[secIdx[q]!]!.startsWith('*** Move to: ')) {
        moveTo = lines[secIdx[q]!]!.slice(13).trim();
        q += 1;
      }
      const chunks: VChunk[] = [];
      let cur: VChunk | null = null;
      const addBody = (chunk: VChunk, bl: string): void => {
        if (bl === '') {
          const idx = chunk.o.length;
          chunk.o.push({ text: '', ctx: true });
          chunk.n.push({ text: '', oIndex: idx });
        } else if (bl.startsWith(' ')) {
          const idx = chunk.o.length;
          chunk.o.push({ text: bl.slice(1), ctx: true });
          chunk.n.push({ text: bl.slice(1), oIndex: idx });
        } else if (bl.startsWith('-')) {
          chunk.o.push({ text: bl.slice(1), ctx: false });
        } else {
          chunk.n.push({ text: bl.slice(1), oIndex: -1 });
        }
      };
      const isBody = (bl: string): boolean => bl === '' || bl.startsWith(' ') || bl.startsWith('-') || bl.startsWith('+');
      while (q < secIdx.length) {
        const li = secIdx[q]!;
        const l = lines[li]!;
        if (l.startsWith('@@')) {
          cur = { anchor: l.slice(2).trim() || null, eof: false, o: [], n: [] };
          chunks.push(cur);
          q += 1;
          while (q < secIdx.length && isBody(lines[secIdx[q]!]!)) {
            addBody(cur, lines[secIdx[q]!]!);
            q += 1;
          }
        } else if (l === '*** End of File') {
          if (cur === null) throw new Exit2(`error: parse ${li + 1}`);
          cur.eof = true;
          cur = null;
          q += 1;
        } else if (cur === null && chunks.length === 0 && isBody(l)) {
          cur = { anchor: null, eof: false, o: [], n: [] };
          chunks.push(cur);
          while (q < secIdx.length && isBody(lines[secIdx[q]!]!)) {
            addBody(cur, lines[secIdx[q]!]!);
            q += 1;
          }
        } else {
          throw new Exit2(`error: parse ${li + 1}`);
        }
      }
      if (chunks.length === 0 && moveTo === null) throw new Exit2(`error: parse ${startLine}`);
      const p = path;
      const mv = moveTo;
      edits.push((tree: Tree): void => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (mv !== null && !safe(mv)) throw new Fail('unsafe', mv);
        const before = tree.get(p);
        if (before === null) throw new Fail('missing', p);
        if (mv !== null && tree.get(mv) !== null) throw new Fail('exists', mv);
        const fs = splitFile(before);
        let cursor = 0;
        for (const ch of chunks) {
          if (ch.anchor !== null) {
            const f = findTier(fs.lines, [ch.anchor], strict, cursor);
            if (f === null) throw new Fail('no-match', p);
            cursor = f.occ[0]! + 1;
          }
          if (ch.o.length === 0) {
            const pos = ch.eof ? fs.lines.length : cursor;
            const rep = ch.n.map((x) => x.text);
            fs.lines.splice(pos, 0, ...rep);
            cursor = pos + rep.length;
          } else {
            const keep = ch.eof ? (pos: number): boolean => pos + ch.o.length === fs.lines.length : undefined;
            const found = findTier(fs.lines, ch.o.map((x) => x.text), strict, cursor, keep);
            if (found === null) throw new Fail('no-match', p);
            const pos = found.occ[0]!;
            const rep = buildReplacement(fs.lines, pos, ch.o, ch.n, found.tier);
            fs.lines.splice(pos, ch.o.length, ...rep);
            cursor = pos + rep.length;
          }
        }
        const text = joinFile(fs);
        if (mv !== null) {
          tree.now.set(p, null);
          tree.now.set(mv, text);
          tree.recordMove(p, mv);
        } else {
          tree.now.set(p, text);
        }
      });
    }
  }
  if (edits.length === 0) throw new Exit2('error: parse 1');
  return edits;
}

// ---------------------------------------------------------------------------
// Sections 1, 2 and 10: invocation, output and exit codes, order and atomicity.
// ---------------------------------------------------------------------------

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    if (kind === 'json') edits = jsonEdits(text, lines);
    else if (kind === 'unified') edits = unifiedEdits(lines, strict);
    else if (kind === 'search-replace') edits = searchReplaceEdits(lines, strict);
    else edits = v4aEdits(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    const beforeMoves = tree.moves.length;
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      tree.moves.length = beforeMoves;
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  const rows: Array<{ key: string; text: string }> = [];
  const paired = new Set<string>();
  for (const [oldP, newP] of tree.moves) {
    if (tree.original(oldP) !== null && tree.get(oldP) === null && tree.original(newP) === null && tree.get(newP) !== null) {
      rows.push({ key: newP, text: `R ${oldP} -> ${newP}` });
      paired.add(oldP);
      paired.add(newP);
    }
  }
  for (const p of [...tree.now.keys()].sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)))) {
    if (paired.has(p)) continue;
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    rows.push({ key: p, text: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
  }
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.key), Buffer.from(b.key)));
  if (!check) {
    for (const p of [...tree.now.keys()].sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)))) {
      const was = tree.original(p);
      const now = tree.now.get(p)!;
      if (was === now) continue;
      if (now === null) rmSync(p, { force: true });
      else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
      }
    }
  }
  const out = rows.map((r) => r.text);
  return { code: 0, out: [...out, `ok: ${out.length} ${out.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
