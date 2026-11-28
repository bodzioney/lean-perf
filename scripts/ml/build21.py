"""Build the fine-tuning set of the step-contraction model from pairs21.py examples.

    OUT=data21 python3 -I build21.py EXAMPLES.jsonl... [--twice EXAMPLES.jsonl...] [--hold-out PATH_SUBSTRING]

Writes chat examples {system, user: two steps in context, assistant: the step that replaced them}
to OUT/train.jsonl and OUT/valid.jsonl (2%, at least 30). Examples that only delete a step or join
the steps are left out. The files after --twice, such as contractions that Lean accepted in the
project at hand, appear twice in the training set.
"""
import json
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import pairprompt  # noqa: E402

random.seed(0)
args = sys.argv[1:]
hold = []
if "--hold-out" in args:
    k = args.index("--hold-out")
    hold = args[k + 1].split(",")
    args = args[:k] + args[k + 2:]
twice = []
if "--twice" in args:
    k = args.index("--twice")
    twice = args[k + 1:]
    args = args[:k]
examples = []
for f in args + twice:
    for line in open(f):
        e = json.loads(line)
        if any(h in e.get("path", "") for h in hold):
            continue
        # Deleting a step is unneededStep's work, and joining the steps saves nothing.
        if e["merged"] in e["steps"] or pairprompt.glued(e["steps"], e["merged"]):
            continue
        user = pairprompt.message(e["statement"], e["previous"], e["steps"], e.get("goal", ""))
        examples.append({"twice": f in twice, "messages": [{"role": "system", "content": pairprompt.SYSTEM},
                                      {"role": "user", "content": user},
                                      {"role": "assistant", "content": e["merged"]}]})
random.shuffle(examples)
n = max(30, len(examples) // 50)
out = os.environ.get("OUT", "data21")
os.makedirs(out, exist_ok=True)
with open(os.path.join(out, "valid.jsonl"), "w") as f:
    for e in examples[:n]:
        f.write(json.dumps({"messages": e["messages"]}) + "\n")
train = [e for e in examples[n:] for _ in range(2 if e["twice"] else 1)]
random.shuffle(train)
with open(os.path.join(out, "train.jsonl"), "w") as f:
    for e in train:
        f.write(json.dumps({"messages": e["messages"]}) + "\n")
print(f"{len(examples)} examples, {n} for validation, {len(train)} training lines")
