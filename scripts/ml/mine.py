"""Mine proof-shortening pairs from a git history: theorems whose statement is unchanged and whose
text got shorter between a commit and its parent. Writes JSON lines {source, commit, name, before, after}."""
import json, re, subprocess, sys
repo, out, label = sys.argv[1], sys.argv[2], sys.argv[3]
grep = sys.argv[4] if len(sys.argv) > 4 else None
import os
ALL = os.environ.get('ALL_CHANGES') == '1'
KINDS = r'theorem|lemma'
start = re.compile(r'^((?:@\[[^\n]*?\]\s*)?(?:(?:private|protected|nonrec)\s+)*)(' + KINDS + r')\s+([^\s:({\[⦃]+)', re.M)
cmd = re.compile(r'^(?=[^\s])', re.M)
def blank_comments(t):
    t = re.sub(r'/-.*?-/', lambda m: re.sub(r'[^\n]', ' ', m.group(0)), t, flags=re.S)
    return re.sub(r'--[^\n]*', lambda m: ' ' * len(m.group(0)), t)
def decls(text):
    nc = blank_comments(text)
    starts = [m.start() for m in cmd.finditer(nc)] + [len(nc)]
    ns, out = [], {}
    for a, b in zip(starts, starts[1:]):
        seg = nc[a:b]; w = seg.split()
        if not w: continue
        if w[0] == 'namespace' and len(w) > 1: ns.append(w[1]); continue
        if w[0] == 'section': ns.append(None); continue
        if w[0] == 'end':
            if ns: ns.pop()
            continue
        m = start.match(seg)
        if not m: continue
        body = seg.rstrip()
        i = body.find(':=')
        if i < 0: continue
        stmt = re.sub(r'\s+', ' ', body[m.end(3):i]).strip()
        full = '.'.join([x for x in ns if x] + [m.group(3)])
        # the original text, without a leading docstring (comments in the proof kept)
        out[full] = (stmt, text[a:a + len(body)])
    return out
def run(*args):
    return subprocess.run(['git', '-C', repo] + list(args), capture_output=True, text=True).stdout
cat = subprocess.Popen(['git', '-C', repo, 'cat-file', '--batch'], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
def show(rev, path):
    cat.stdin.write(f'{rev}:{path}\n'.encode()); cat.stdin.flush()
    header = cat.stdout.readline().split()
    if len(header) < 3 or header[1] != b'blob': return None
    data = cat.stdout.read(int(header[2])); cat.stdout.read(1)
    return data.decode('utf-8', 'replace')
args = ['log', '--no-merges', '--format=%H %P']
if grep: args += ['-i', f'--grep={grep}']
commits = [l.split() for l in run(*args).splitlines() if len(l.split()) >= 2]
n = 0; seen = set()
with open(out, 'w') as f:
    for k, (c, p, *_) in enumerate(commits):
        files = [x for x in run('diff-tree', '--no-commit-id', '-r', '--name-only', p, c).splitlines() if x.endswith('.lean')]
        for path in files[:40]:
            old, new = show(p, path), show(c, path)
            if not old or not new: continue
            do, dn = decls(old), decls(new)
            for name, (s0, t0) in do.items():
                if name not in dn: continue
                s1, t1 = dn[name]
                # With ALL_CHANGES=1, every change that keeps the statement, for pairs21.py.
                if s0 != s1 or t0 == t1: continue
                if not ALL and len(t1.encode()) >= len(t0.encode()): continue
                if (t0, t1) in seen: continue
                seen.add((t0, t1))
                f.write(json.dumps({'source': label, 'commit': c[:10], 'path': path, 'name': name, 'before': t0, 'after': t1}) + '\n'); n += 1
        if k % 500 == 0: print(k, len(commits), n, file=sys.stderr, flush=True)
print(label, 'commits', len(commits), 'pairs', n)
