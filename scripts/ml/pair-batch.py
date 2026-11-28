"""Ask Codex for step contractions of many pairs at once, writing a table for scripts/pair-table.

    python3 -I pair-batch.py PAIRS.jsonl TABLE.jsonl [BATCH] [MAX_CALLS]

PAIRS comes from pairdump.py. Each call sends BATCH numbered pairs (default 40) and asks for one step
per pair, or SKIP; the answers go to TABLE as {steps, candidates}. Lean checks them later, with
`LEANPERF_PAIR_MODEL=scripts/pair-table leanperf --compress --rules contractPair`. Pairs already in
TABLE are skipped, so the script can resume; it stops after MAX_CALLS calls (default 50) or when a
call fails.
"""
import json
import os
import re
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import pairprompt  # noqa: E402

PROMPT = """You shorten Lean 4 (Mathlib) tactic proofs. Below are numbered items. Each gives a theorem
statement, the proof steps before, and two consecutive tactic steps. For each item, propose ONE tactic
step that does the work of both steps (it may close the goal or leave the same goal for the remaining
proof), strictly shorter in characters than the two together. Use any Mathlib tactic or lemma.

The step must merge the work, as in these examples:
  rw [h] at h'  /  exact h'                       ->  rwa [h] at h'
  have k : T := by simp_all  /  simpa using f k   ->  simpa using f (by simp_all)
  apply f  /  exact h                             ->  exact f h
  rw [a]  /  exact h                              ->  exact a ▸ h
  obtain ⟨x, hx⟩ := h  /  exact ⟨x, hx.le⟩        ->  exact ⟨_, h.2.le⟩
Do not join the two steps with `<;>` or `;`, and do not only reformat them, rename locals or drop type
ascriptions: other tools already do that. Most pairs cannot be merged; answer SKIP for those. Answer
only with lines `<number>: <step>` or `<number>: SKIP`, one per item, in order, nothing else.
"""


def main():
    src, table = sys.argv[1], sys.argv[2]
    batch = int(sys.argv[3]) if len(sys.argv) > 3 else 40
    max_calls = int(sys.argv[4]) if len(sys.argv) > 4 else 50
    pairs = [json.loads(l) for l in open(src)]
    done = set()
    if os.path.exists(table):
        for l in open(table):
            done.add(tuple(json.loads(l)["steps"]))
    todo = [p for p in pairs if tuple(p["steps"]) not in done]
    calls = 0
    for k in range(0, len(todo), batch):
        if calls >= max_calls:
            break
        chunk = todo[k:k + batch]
        items = []
        for i, p in enumerate(chunk):
            items.append(f"## {i + 1}\n" + pairprompt.message(p["statement"], p["previous"], p["steps"]))
        prompt = PROMPT + "\n\n" + "\n\n".join(items)
        with tempfile.TemporaryDirectory() as d:
            out = os.path.join(d, "answer.txt")
            subprocess.run(["codex", "exec", "-s", "read-only", "--skip-git-repo-check", "--ephemeral",
                            "-C", d, "-o", out, "-"], input=prompt, capture_output=True, text=True, timeout=1800)
            text = open(out).read() if os.path.exists(out) else ""
        calls += 1
        answers = {}
        for line in text.splitlines():
            m = re.match(r"\s*(\d+)\s*:\s*(.*\S)\s*$", line)
            if m:
                answers[int(m.group(1))] = m.group(2).strip().strip("`")
        if not answers:
            print(f"call {calls}: no answers, stopping", file=sys.stderr)
            break
        with open(table, "a") as f:
            for i, p in enumerate(chunk):
                a = answers.get(i + 1, "SKIP")
                cands = [] if a.upper() == "SKIP" or pairprompt.glued(p["steps"], a) else [a]
                f.write(json.dumps({"steps": p["steps"], "path": p["path"], "candidates": cands}) + "\n")
        print(f"call {calls}: {sum(1 for a in answers.values() if a.upper() != 'SKIP')} proposals of {len(chunk)}",
              file=sys.stderr, flush=True)


if __name__ == "__main__":
    main()
