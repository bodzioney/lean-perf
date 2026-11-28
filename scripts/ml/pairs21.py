"""Mine "steps became one" examples from pairs of a declaration's text before and after a change
that kept its statement (mine.py, or rewrites logged by `leanperf --propose`).

    python3 -I pairs21.py OUT.jsonl PAIRS.jsonl...

An example is a hunk of the line diff where two to five consecutive one-line tactic steps at the
same indentation became one shorter line at that indentation, other than any of them. Each line of
OUT is {source, statement, previous, steps, merged}: the declaration up to its proof, up to six steps
before the run, the run and the step that replaced it, all without indentation.
"""
import difflib
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


def indent(line):
    return len(line) - len(line.lstrip(" "))


def plain(line):
    s = line.strip()
    return s and not s.startswith("--") and "/-" not in s and "-/" not in s and not s.startswith("·") \
        and not re.search(r"(:=|\bby|,|\(|⟨|\[|\bfun\b.*↦|=>)\s*$", s)


def proof_start(lines):
    """The index of the first line of the proof: the line after the one that ends with `:= by`."""
    for k, l in enumerate(lines):
        if re.search(r":=\s*by\s*$", l):
            return k + 1
    return None


def examples(source, before, after, most=5):
    b, a = before.split("\n"), after.split("\n")
    start = proof_start(b)
    if start is None:
        return
    statement = "\n".join(b[:start]).strip()
    for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, b, a, autojunk=False).get_opcodes():
        if tag != "replace" or not 2 <= i2 - i1 <= most or j2 - j1 != 1 or i1 < start:
            continue
        xs, m = b[i1:i2], a[j1]
        col = indent(xs[0])
        if col < 2 or any(indent(x) != col for x in xs) or indent(m) != col:
            continue
        if not (all(plain(x) for x in xs) and plain(m)):
            continue
        # Each line is a whole step: the line after the run is not indented deeper.
        if i2 < len(b) and b[i2].strip() and indent(b[i2]) > col:
            continue
        if j2 < len(a) and a[j2].strip() and indent(a[j2]) > col:
            continue
        steps, ms = [x.strip() for x in xs], m.strip()
        if ms in steps or len(ms.encode()) >= sum(len(x.encode()) for x in steps):
            continue
        previous = [l.strip() for l in b[start:i1] if indent(l) >= col and l.strip()][-6:]
        yield {"source": source, "statement": statement, "previous": previous, "steps": steps,
               "merged": ms}


def main():
    out, srcs = sys.argv[1], sys.argv[2:]
    n = 0
    seen = set()
    with open(out, "w") as f:
        for path in srcs:
            for line in open(path):
                p = json.loads(line)
                src = p.get("source") or ("codex" if "codex" in path else "claude")
                for e in examples(src, p["before"], p["after"]):
                    k = (tuple(e["steps"]), e["merged"])
                    if k in seen:
                        continue
                    seen.add(k)
                    f.write(json.dumps(e) + "\n")
                    n += 1
    print(f"{n} examples")


if __name__ == "__main__":
    main()
