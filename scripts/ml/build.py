"""Build the fine-tuning set: chat examples that give a declaration, with the related statements above it in its
file (see context.py), and ask for a shorter proof of the same statement.

    python3 -I build.py HELD_OUT_MODULES PAIRS.jsonl...

HELD_OUT_MODULES is a comma-separated list of RH modules (paths under HELD_OUT_ROOT) kept out of training, by
file and by theorem name. Each line of a PAIRS file is {source, before, after, context?, path? or file?}: pairs
mined by mine.py and given context by contexts.py, or rewrites Lean accepted that `leanperf --propose` logged
(LEANPERF_PROPOSE_LOG, given context by contexts.py --tree). A file named *self* holds the model's own rewrites.

Environment: MATHLIB_LIMIT (default 8000, the largest relative shrinks), MAX_CHARS (default 6000),
WEIGHT_<SOURCE> (repeats per example: rh 1, compact 1, claude 4, self 1), CONTEXT (default 1),
PROOF_ONLY (default 1: the target is the proof after `:=`), OUT (default data).
"""
import json
import os
import random
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import context  # noqa: E402

random.seed(0)
PROOF_ONLY = os.environ.get('PROOF_ONLY', '1') == '1'
USE_CONTEXT = os.environ.get('CONTEXT', '1') == '1'
SYSTEM = ("You shorten Lean 4 proofs. Write a proof of the declaration's statement that is as short as you can make it. "
          "Answer with the proof alone, the text that follows `:=`.") if PROOF_ONLY else \
    "You shorten Lean 4 proofs. Rewrite the declaration as briefly as you can, keeping its name, binders and statement exactly. Answer with the declaration only."
WEIGHTS = {'rh': 1, 'compact': 1, 'claude': 4, 'self': 1, 'mathlib': 1}


def tokens(t):
    return re.findall(r"[^\W\d][\w'.!?₀-₉]*", t)


def good(b, a):
    if len(b) + len(a) > int(os.environ.get('MAX_CHARS', '6000')) or len(b) > 3000 or len(a) < 20:
        return False
    saved = len(b.encode()) - len(a.encode())
    if saved < 40 and saved < 0.15 * len(b.encode()):
        return False
    # A rename-only change keeps the token count and changes few tokens.
    tb, ta = tokens(b), tokens(a)
    if len(tb) == len(ta) and sum(x != y for x, y in zip(tb, ta)) <= 2:
        return False
    return True


def split_proof(t):
    """The statement and the proof of a declaration: around the first `:=` outside brackets."""
    depth = 0
    for i, c in enumerate(t[:-1]):
        if c in '([{⟨⦃':
            depth += 1
        elif c in ')]}⟩⦄':
            depth -= 1
        elif depth == 0 and t.startswith(':=', i):
            return t[:i], t[i + 2:]
    return None


# In a logged group only the last declaration is the one the model sees (see scripts/propose-local).
LAST_DECL = re.compile(r'^(?:/--.*?-/\s*)?(?:@\[[^\n]*\]\s*)?(?:(?:private|protected) )*(?:theorem|lemma) ', re.M | re.S)


def last(t):
    starts = [m.start() for m in LAST_DECL.finditer(t)]
    return t[starts[-1]:] if starts else t


held_out = set(sys.argv[1].split(',')) if len(sys.argv) > 1 and sys.argv[1] else set()
root = os.environ.get('HELD_OUT_ROOT', os.path.expanduser('~/Code/riemann-hypothesis'))
decl_name = re.compile(r'^(?:@\[[^\n]*\]\s*)?(?:private |protected )*(?:theorem|lemma) ([^\s(:{\[]+)', re.M)
held_names = set()
for h in held_out:
    try:
        held_names |= {n.split('.')[-1] for n in decl_name.findall(open(os.path.join(root, h)).read())}
    except OSError:
        pass

examples, counts = [], {}


def add(src, p):
    b, a = last(p['before']), last(p['after'])
    if not good(b, a):
        return
    path = p.get('path') or p.get('file') or ''
    if src in ('rh', 'claude', 'self') and any(path.endswith(h) or h.endswith(path) for h in held_out if path):
        return
    m = decl_name.match(b.lstrip())
    if m and m.group(1).split('.')[-1] in held_names:
        return
    target = a
    if PROOF_ONLY:
        sb, sa = split_proof(b), split_proof(a)
        if not sb or not sa:
            return
        target = sa[1].strip()
    user = context.message(p.get('context', '') if USE_CONTEXT else '', b)
    ex = {"messages": [{"role": "system", "content": SYSTEM}, {"role": "user", "content": user},
                       {"role": "assistant", "content": target}]}
    for _ in range(int(os.environ.get('WEIGHT_' + src.upper(), WEIGHTS.get(src, 1)))):
        examples.append(ex)
    counts[src] = counts.get(src, 0) + 1


for f in sys.argv[2:]:
    pairs = [json.loads(line) for line in open(f)]
    base = os.path.basename(f)
    for p in pairs:
        p.setdefault('source', 'self' if 'self' in base else 'claude')
    if any(p['source'] == 'mathlib' for p in pairs):
        # Mathlib has far more pairs than one epoch on a laptop can use: keep the largest relative shrinks.
        ml = [p for p in pairs if p['source'] == 'mathlib' and good(p['before'], p['after'])]
        ml.sort(key=lambda p: len(p['after'].encode()) / len(p['before'].encode()))
        pairs = [p for p in pairs if p['source'] != 'mathlib'] + ml[:int(os.environ.get('MATHLIB_LIMIT', '8000'))]
    for p in pairs:
        add(p['source'], p)

random.shuffle(examples)
n = max(50, len(examples) // 50)
out = os.environ.get('OUT', 'data')
os.makedirs(out, exist_ok=True)
with open(os.path.join(out, 'valid.jsonl'), 'w') as f:
    for e in examples[:n]:
        f.write(json.dumps(e) + '\n')
with open(os.path.join(out, 'train.jsonl'), 'w') as f:
    for e in examples[n:]:
        f.write(json.dumps(e) + '\n')
print('kept per source', counts, 'examples (with weights)', len(examples), 'valid', n)
