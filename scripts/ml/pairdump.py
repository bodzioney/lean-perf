"""List adjacent one-line tactic steps of Lean files, for a proposer that answers them in batches.

    python3 -I pairdump.py OUT.jsonl FILE.lean...

Each line of OUT is {path, statement, previous, steps}: the declaration up to its proof, up to six
steps before the pair, and the two steps, as `contractPair` sends them to LEANPERF_PAIR_MODEL. The
text is read with the indentation rules of pairs21.py, not parsed: Lean checks every answer later.
"""
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import pairs21  # noqa: E402

DECL = re.compile(r"^(?:@\[[^\n]*\]\s*)?(?:(?:private|protected|nonrec) )*(?:theorem|lemma) ")


def pairs(path, text):
    lines = text.split("\n")
    k = 0
    while k < len(lines):
        if not DECL.match(lines[k]):
            k += 1
            continue
        # The declaration runs to the next line at column 0.
        end = k + 1
        while end < len(lines) and (not lines[end].strip() or lines[end][0] == " "):
            end += 1
        decl = lines[k:end]
        start = pairs21.proof_start(decl)
        if start is not None:
            statement = "\n".join(decl[:start]).strip()
            for i in range(start, len(decl) - 1):
                x, y = decl[i], decl[i + 1]
                col = pairs21.indent(x)
                if col < 2 or pairs21.indent(y) != col or not (pairs21.plain(x) and pairs21.plain(y)):
                    continue
                # A tactic step starts with its name; other lines continue a term.
                if not (re.match(r"[a-z]", x.strip()) and re.match(r"[a-z]", y.strip())):
                    continue
                if i + 2 < len(decl) and decl[i + 2].strip() and pairs21.indent(decl[i + 2]) > col:
                    continue
                if i > start and pairs21.indent(decl[i - 1]) > col and decl[i - 1].strip():
                    # `x` may continue the line above.
                    continue
                previous = [l.strip() for l in decl[start:i] if pairs21.indent(l) >= col and l.strip()][-6:]
                yield {"path": path, "statement": statement, "previous": previous,
                       "steps": [x.strip(), y.strip()]}
        k = end


def main():
    out, files = sys.argv[1], sys.argv[2:]
    n = 0
    with open(out, "w") as f:
        for p in files:
            for e in pairs(p, open(p, encoding="utf-8").read()):
                f.write(json.dumps(e) + "\n")
                n += 1
    print(f"{n} pairs")


if __name__ == "__main__":
    main()
