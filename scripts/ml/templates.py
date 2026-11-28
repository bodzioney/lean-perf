"""A dictionary of step contractions, learned from examples the way a dictionary coder learns its
phrases: each checked contraction of two steps into one is generalized into a template, and a
template's support is the number of examples it reproduces.

    python3 -I templates.py OUT.jsonl EXAMPLES.jsonl...

EXAMPLES are {steps, merged} lines (pairs21.py, LEANPERF_PAIR_LOG), of two or three steps, the
windows of the peephole pass `contractPair`. A template is found by
anti-unification. The longest balanced token spans that the merged step copies from the steps become
holes `$k`, which match any balanced span and must match the same text wherever they recur. The
other identifiers and terms of the steps become wildcards `$_`. Tactic names and keywords stay
literal. For example

    have h_cases := floorOf_level_cases i  /  grind  ->  grind [floorOf_level_cases i]

gives `have $_ := $0  /  grind  ->  grind [$0]`. scripts/pair-dict proposes the instances of the
templates for the steps LeanPerf asks about, and Lean checks each one, so a template that is too
general only costs a check.
"""
import json
import re
import sys
from collections import defaultdict

TOKEN = re.compile(r"""
   (?P<ws>\s+)
  |(?P<id>[^\W\d][\w'!?₀-₉ₐ-ₜᵢ-ᵪ]*(?:\.(?:[^\W\d][\w'!?₀-₉ₐ-ₜᵢ-ᵪ]*|\d+))*)
  |(?P<num>\d+(?:\.\d+)?)
  |(?P<op>:=|<;>|=>|<\|>|<\||\|>|\?_|::|->|<-|\.\.|[^\s])
""", re.X)

OPEN, CLOSE = "([{⟨⦃⟪", ")]}⟩⦄⟫"
KEYWORDS = {":=", "at", "using", "with", "only", "by", "fun", "↦", "=>", "<;>", "·", "from", "in",
            "generalizing", "then", "else", "if", "show", "this", "?_"}
TACTICS = set("""rw rwa rewrite simp simpa simp_all dsimp simp_rw norm_num exact refine apply intro
intros rintro obtain rcases cases induction have let set show change unfold ext funext constructor use
exists refine' linarith nlinarith positivity omega lia ring ring_nf field_simp field aesop grind rfl
trivial decide tauto bound gcongr fun_prop congr convert calc subst specialize by_contra push_neg
contrapose exfalso symm left right split_ifs filter_upwards choose lift norm_cast push_cast exact_mod_cast
simpa? exact? apply? infer_instance continuity measurability abel module noncomm_ring nofun nomatch
replace clear classical haveI letI suffices interval_cases fin_cases""".split())


def tokens(text):
    """Tokens of `text` as (string, start, end), without whitespace."""
    out = []
    for m in TOKEN.finditer(text):
        if m.lastgroup != "ws":
            out.append((m.group(0), m.start(), m.end()))
    return out


def literal(tok):
    return tok in KEYWORDS or tok in TACTICS


def balanced(toks):
    depth = 0
    for t in toks:
        if t in OPEN:
            depth += 1
        elif t in CLOSE:
            depth -= 1
            if depth < 0:
                return False
    return depth == 0


def meaningful(toks):
    return any(not literal(t) and (t[0].isalnum() or t[0] == "_") for t in toks)


def occurs(span, toks):
    n = len(span)
    return any(tuple(toks[i:i + n]) == span for i in range(len(toks) - n + 1))


def learn(steps, merged):
    """The template of one example: (patterns of the steps, template of the merged step), or None.
    A pattern is a tuple of items: ("l", token), ("h", k) for hole k, ("w",) for a wildcard. The
    merged step's items carry the whitespace before them, to write instances the way it was written."""
    S = [[t for t, _, _ in tokens(s)] for s in steps]
    Mt = tokens(merged)
    M = [t for t, _, _ in Mt]
    if not M or any(not s for s in S):
        return None
    holes = []
    out = []
    i = 0
    while i < len(M):
        found = None
        # The merged step's tactic name stays literal.
        if i > 0 and not literal(M[i]):
            for L in range(len(M) - i, 0, -1):
                span = tuple(M[i:i + L])
                if balanced(span) and meaningful(span) and any(occurs(span, s) for s in S):
                    found = span
                    break
        ws = merged[Mt[i - 1][2]:Mt[i][1]] if i > 0 else ""
        if found:
            if found not in holes:
                holes.append(found)
            out.append(("h", holes.index(found), ws))
            i += len(found)
        else:
            out.append(("l", M[i], ws))
            i += 1
    pats = []
    for s in S:
        marks = [None] * len(s)
        # Longest holes first, so that a hole inside another does not split it.
        for k in sorted(range(len(holes)), key=lambda k: -len(holes[k])):
            h, n = holes[k], len(holes[k])
            j = 0
            while j + n <= len(s):
                if tuple(s[j:j + n]) == h and all(m is None for m in marks[j:j + n]):
                    marks[j:j + n] = [("h", k)] * n
                    j += n
                else:
                    j += 1
        for j, t in enumerate(s):
            if marks[j] is None and (j == 0 or literal(t)):
                marks[j] = ("l", t)
        pat = []
        j = 0
        while j < len(s):
            if marks[j] is None:
                e = j
                while e < len(s) and marks[e] is None:
                    e += 1
                run = s[j:e]
                if balanced(run):
                    pat.append(("w",))
                else:
                    # A hole inside brackets: the brackets are literal, the rest wildcards.
                    for t in run:
                        if t in OPEN or t in CLOSE:
                            pat.append(("l", t))
                        elif not pat or pat[-1] != ("w",):
                            pat.append(("w",))
                j = e
            else:
                pat.append(marks[j])
                # A hole marks every token of its span.
                if marks[j][0] == "h":
                    j += len(holes[marks[j][1]])
                else:
                    j += 1
        pats.append(tuple(pat))
    # A hole that the steps do not show cannot be filled.
    shown = {it[1] for p in pats for it in p if it[0] == "h"}
    if any(it[0] == "h" and it[1] not in shown for it in out):
        return None
    return tuple(pats), tuple(out)


def spans(toks):
    """For each start, the ends of the balanced non-empty spans that start there."""
    out = []
    for i in range(len(toks)):
        ends, depth = [], 0
        for j in range(i, len(toks)):
            t = toks[j]
            if t in OPEN:
                depth += 1
            elif t in CLOSE:
                depth -= 1
                if depth < 0:
                    break
            if depth == 0:
                ends.append(j + 1)
        out.append(ends)
    return out


def match(pat, toks, sp, bind, i=0, k=0):
    """Bindings of the holes (as token ranges) under which `pat[k:]` matches `toks[i:]`."""
    if k == len(pat):
        if i == len(toks):
            yield bind
        return
    it = pat[k]
    if it[0] == "l":
        if i < len(toks) and toks[i] == it[1]:
            yield from match(pat, toks, sp, bind, i + 1, k + 1)
        return
    if i >= len(toks):
        return
    if it[0] == "h" and it[1] in bind:
        want = bind[it[1]]
        n = len(want)
        if tuple(toks[i:i + n]) == want:
            yield from match(pat, toks, sp, bind, i + n, k + 1)
        return
    for e in sp[i]:
        if it[0] == "h":
            yield from match(pat, toks, sp, {**bind, it[1]: tuple(toks[i:e]), ("pos", it[1]): (i, e)}, e, k + 1)
        else:
            yield from match(pat, toks, sp, bind, e, k + 1)


def instances(template, steps, limit=4):
    """What the template writes for `steps`: up to `limit` distinct steps."""
    pats, out = template
    if len(pats) != len(steps):
        return []
    toks = [tokens(s) for s in steps]
    names = [[t for t, _, _ in ts] for ts in toks]
    res = []

    def go(j, bind):
        if j == len(steps):
            yield bind
            return
        for b in match(pats[j], names[j], spans(names[j]), {**bind, "step": j}):
            # Keep where each hole was bound: its text is the source between its first and last token.
            b2 = dict(b)
            for key in list(b):
                if isinstance(key, tuple) and key[0] == "pos" and ("src", key[1]) not in b2:
                    s0, e0 = b[key]
                    b2[("src", key[1])] = steps[j][toks[j][s0][1]:toks[j][e0 - 1][2]]
                    del b2[key]
            yield from go(j + 1, b2)

    for b in go(0, {}):
        text = ""
        for it in out:
            text += it[2] + (it[1] if it[0] == "l" else b[("src", it[1])])
        if text not in res:
            res.append(text)
        if len(res) >= limit:
            break
    return res


def key(template):
    pats, out = template
    return json.dumps([pats, [it[:2] for it in out]], ensure_ascii=False)


def norm(s):
    return re.sub(r"\s+", "", s)


def main():
    out_path, files = sys.argv[1], sys.argv[2:]
    examples = []
    for f in files:
        for line in open(f):
            e = json.loads(line)
            if len(e.get("steps", [])) in (2, 3) and e.get("merged"):
                examples.append((e["steps"], e["merged"]))
    templates = {}
    origin = defaultdict(set)
    for n, (steps, merged) in enumerate(examples):
        t = learn(steps, merged)
        if t is None:
            continue
        k = key(t)
        templates.setdefault(k, t)
        origin[k].add(n)
    # Support: the examples a template reproduces, found among those with the same tactic names.
    heads = defaultdict(list)
    for n, (steps, _) in enumerate(examples):
        heads[tuple(s.split()[0] if s.split() else "" for s in steps)].append(n)
    support = {}
    for k, t in templates.items():
        h = tuple(p[0][1] if p and p[0][0] == "l" else "" for p in t[0])
        hits = set()
        for n in heads.get(h, []):
            steps, merged = examples[n]
            if any(norm(x) == norm(merged) for x in instances(t, steps)):
                hits.add(n)
        support[k] = hits | origin[k]
    # Leave one out: an example that a template learned from other examples reproduces.
    covered = set()
    for k, hits in support.items():
        if len(hits) >= 2 or (hits - origin[k]):
            covered |= hits
    rows = sorted(templates, key=lambda k: -len(support[k]))
    with open(out_path, "w") as f:
        for k in rows:
            pats, out = templates[k]
            f.write(json.dumps({"patterns": pats, "merged": out, "support": len(support[k])},
                               ensure_ascii=False) + "\n")
    multi = sum(1 for k in rows if len(support[k]) >= 2)
    print(f"{len(examples)} examples, {len(templates)} templates, {multi} with support of 2 or more; "
          f"{len(covered)} examples ({len(covered) / max(1, len(examples)):.0%}) reproduced by a "
          f"template that another example also gives", file=sys.stderr)


if __name__ == "__main__":
    main()
