"""Add to mined pairs the context a model sees beside the declaration (see context.py): the related statements
above it in its file, as the file was before the change.

    python3 -I contexts.py REPO IN.jsonl OUT.jsonl        pairs from mine.py, files read from git
    python3 -I contexts.py --tree ROOT IN.json OUT.jsonl  readable/compact pairs (compare/pairs.json), files
                                                          read under ROOT
    python3 -I contexts.py --tree ROOT IN.jsonl OUT.jsonl LEANPERF_PROPOSE_LOG pairs, files read under ROOT
"""
import json
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import context  # noqa: E402


def main():
    args = sys.argv[1:]
    tree = args[0] == "--tree"
    if tree:
        args = args[1:]
    root, src, out = args
    if tree:
        files = {}

        def read(path):
            if path not in files:
                try:
                    files[path] = open(os.path.join(root, path), encoding="utf-8").read()
                except OSError:
                    files[path] = None
            return files[path]
    else:
        cat = subprocess.Popen(["git", "-C", root, "cat-file", "--batch"], stdin=subprocess.PIPE,
                               stdout=subprocess.PIPE)
        last = {}

        def read(rev_path):
            if rev_path in last:
                return last[rev_path]
            cat.stdin.write(f"{rev_path}\n".encode())
            cat.stdin.flush()
            header = cat.stdout.readline().split()
            text = None
            if len(header) == 3:
                # Every object's content follows its header, and must be read even when it is not a file.
                data = cat.stdout.read(int(header[2]))
                cat.stdout.read(1)
                if header[1] == b"blob":
                    text = data.decode("utf-8", "replace")
            last.clear()
            last[rev_path] = text
            return text

        changed = {}

        def files_of(commit):
            """The Lean files a commit changed, for pairs mined without their path."""
            if commit not in changed:
                out = subprocess.run(["git", "-C", root, "diff-tree", "--no-commit-id", "-r", "--name-only",
                                      f"{commit}^", commit], capture_output=True, text=True).stdout
                changed.clear()
                changed[commit] = [x for x in out.splitlines() if x.endswith(".lean")][:40]
            return changed[commit]

    if src.endswith(".json"):
        pairs = []
        def stmt(t):
            t = re.sub(r"/-.*?-/|--[^\n]*", "", t, flags=re.S)
            i = t.find(":=")
            t = t[:i] if i >= 0 else t
            return re.sub(r"\s+", " ", re.sub(r"^(?:@\[[^\]]*\]\s*)?(?:theorem|lemma)\s+\S+", "", t.strip())).strip()
        for p in json.load(open(src)):
            # The compact edition restated some theorems; only the same statement makes a pair.
            if stmt(p["grh"]["text"]) != stmt(p["compact"]["text"]):
                continue
            pairs.append({"source": "compact", "path": p["grh"]["file"], "name": p["name"],
                          "before": p["grh"]["text"], "after": p["compact"]["text"]})
    else:
        pairs = [json.loads(line) for line in open(src)]
    kept = missing = 0
    with open(out, "w") as f:
        for k, p in enumerate(pairs):
            b = p["before"]
            # Too long to train on (see build.py), or not shorter at all.
            if len(b) > 3000 or len(p["after"].encode()) >= len(b.encode()):
                continue
            saved = len(b.encode()) - len(p["after"].encode())
            if saved < 40 and saved < 0.15 * len(b.encode()):
                continue
            path = p.get("path") or p.get("file", "")
            if tree:
                text = read(path)
            else:
                text = None
                for f_ in [path] if path else files_of(p["commit"]):
                    t = read(f"{p['commit']}^:{f_}")
                    if t and b in t:
                        text, p["path"] = t, f_
                        break
            i = text.find(b) if text else -1
            if i < 0:
                missing += 1
                continue
            p["context"] = context.related(text[:i], b)
            f.write(json.dumps(p) + "\n")
            kept += 1
            if kept % 1000 == 0:
                print(k, len(pairs), kept, missing, file=sys.stderr, flush=True)
    print(f"{src}: {kept} pairs with context, {missing} not found in their file")


if __name__ == "__main__":
    main()
