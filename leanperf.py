#!/usr/bin/env python3
"""A syntax-only Lean proof linter, batch rewriter and LSP server."""
import argparse
from contextlib import contextmanager
import difflib
import json
import os
from pathlib import Path
import statistics
import subprocess
import sys
import tempfile
import time

PACKAGE = Path(__file__).resolve().parent
RULES = {
    "splitObtain": "Bind the application before destructuring it",
    "exactUsing": "Use the hypothesis whose type matches the goal",
    "simpRfl": "Use reflexivity for this equality",
}
TOKENS = {"splitObtain": "obtain", "exactUsing": "simpa", "simpRfl": "simp"}


@contextmanager
def parser_process():
    # Resolve tools solely in our package. An untrusted workspace can contain an executable lakefile.
    exe = subprocess.check_output(["lake", "query", "leanperf-parser"], cwd=PACKAGE, text=True).strip()
    sysroot = subprocess.check_output(["lean", "--print-prefix"], cwd=PACKAGE, text=True).strip()
    with subprocess.Popen([exe, sysroot, PACKAGE / ".lake/build/lib/lean"], cwd=PACKAGE,
                          stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True,
                          encoding="utf-8") as proc:
        def analyze(source):
            proc.stdin.write(json.dumps(source, ensure_ascii=False) + "\n")
            proc.stdin.flush()
            reply = proc.stdout.readline()
            if not reply:
                raise RuntimeError("LeanPerf parser stopped unexpectedly")
            return json.loads(reply)
        try:
            yield analyze
        finally:
            proc.stdin.close()


def pos_key(pos):
    return pos["line"], pos["character"]


def independent(findings):
    """Keep an outer edit intact if its source contains another reported tactic."""
    def order(f):
        r = f["edit"]["range"]
        line, col = pos_key(r["end"])
        return pos_key(r["start"]), -line, -col
    end = (-1, -1)
    result = []
    for finding in sorted(findings, key=order):
        r = finding["edit"]["range"]
        if pos_key(r["start"]) >= end:
            result.append(finding)
            end = pos_key(r["end"])
    return result


def checked_rules(names):
    if not isinstance(names, list) or not all(isinstance(r, str) and r in RULES for r in names):
        raise ValueError("expected an array containing rule names from " + ", ".join(RULES))
    return set(names)


def lint(source, rules, analyze):
    if not any(TOKENS[r] in source for r in rules):
        return [], 0
    result = analyze(source)
    return [f for f in result["findings"] if f["rule"] in rules], result["skippedCommands"]


def apply_edits(text, findings):
    # The Lean parser returns standard LSP positions (UTF-16), even on a UTF-8 filesystem.
    lines = text.split("\n")
    starts = [0]
    for line in lines:
        starts.append(starts[-1] + len(line) + 1)

    def offset(pos):
        row, col = pos_key(pos)
        encoded = lines[row].removesuffix("\r").encode("utf-16-le")
        if not 0 <= col * 2 <= len(encoded):
            raise ValueError("column outside the document")
        return starts[row] + len(encoded[:2*col].decode("utf-16-le"))

    parts, cursor = [], 0
    for f in independent(findings):
        edit = f["edit"]
        r = edit["range"]
        start, end = offset(r["start"]), offset(r["end"])
        new = edit["newText"]
        if lines[r["start"]["line"]].endswith("\r"):
            new = new.replace("\n", "\r\n")
        parts.extend((text[cursor:start], new))
        cursor = end
    return "".join(parts) + text[cursor:]


def check(path, text):
    start = time.monotonic()
    run = subprocess.run(["lake", "--no-build", "--no-cache", "lean", str(path), "--", "--stdin"],
                         input=text.encode(), stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if run.returncode:
        raise ValueError("Lake check failed\n" + run.stdout.decode(errors="replace"))
    return time.monotonic() - start


def save(path, original, new):
    with tempfile.NamedTemporaryFile("wb", dir=path.parent, delete=False) as stream:
        temp = Path(stream.name)
        try:
            stream.write(new.encode())
            stream.flush()
            temp.chmod(path.stat().st_mode)
            if path.is_symlink() or path.read_bytes() != original:
                raise ValueError("file changed during analysis")
            os.replace(temp, path)
        finally:
            temp.unlink(missing_ok=True)


def files(paths):
    for path in paths:
        if path.is_symlink():
            raise ValueError(f"symlink input: {path}")
        if path.is_dir():
            for root, dirs, names in os.walk(path):
                dirs[:] = sorted(d for d in dirs if not d.startswith("."))
                for name in sorted(names):
                    child = Path(root) / name
                    if name.endswith(".lean") and not child.is_symlink():
                        yield child.resolve()
        elif path.is_file() and path.suffix == ".lean":
            yield path.resolve()
        else:
            raise ValueError(f"expected a Lean file or directory: {path}")


def run_cli(args, rules, analyze):
    failed = count = skipped = 0
    seen = set()
    for path in files(args.paths):
        if path in seen:
            continue
        seen.add(path)
        label = os.path.relpath(path)
        try:
            original = path.read_bytes()
            text = original.decode()
            findings, missed = lint(text, rules, analyze)
            skipped += missed
            if not findings:
                continue
            edits = independent(findings)
            new = apply_edits(text, edits)
            if args.bench:
                times = [[], []]
                for i in range(args.bench):
                    for variant in ((0, 1) if i % 2 == 0 else (1, 0)):
                        times[variant].append(check(path, (text, new)[variant]))
                before, after = map(statistics.median, times)
                print(f"{label}: original {before:.2f}s, rewritten {after:.2f}s "
                      f"(median of {args.bench} Lake checks each)", file=sys.stderr)
            elif args.check:
                check(path, new)
            if args.apply:
                save(path, original, new)
            else:
                sys.stdout.writelines(difflib.unified_diff(text.splitlines(True), new.splitlines(True),
                                                           f"a/{label}", f"b/{label}"))
            count += len(edits)
        except (OSError, ValueError) as error:
            print(f"{label}: {error}", file=sys.stderr)
            failed += 1
    print(f"{count} edits, {skipped} unparsed commands, {failed} failed files", file=sys.stderr)
    return int(failed > 0)


def read_lsp(stream):
    headers = {}
    while True:
        line = stream.readline()
        if not line:
            return None
        if line == b"\r\n":
            break
        name, value = line.split(b":", 1)
        headers[name.lower()] = value.strip()
    return json.loads(stream.read(int(headers[b"content-length"])))


def write_lsp(stream, message):
    data = json.dumps({"jsonrpc": "2.0", **message}, ensure_ascii=False).encode()
    stream.write(f"Content-Length: {len(data)}\r\n\r\n".encode() + data)
    stream.flush()


class LanguageServer:
    def __init__(self, analyze, rules, send):
        self.analyze = analyze
        self.rules = rules
        self.enabled = True
        self.send = send
        self.documents = {}
        self.versioned_edits = False
        self.shutdown = False

    def configure(self, options):
        if "rules" in options:
            self.rules = checked_rules(options["rules"])
        if "enabled" in options:
            if not isinstance(options["enabled"], bool):
                raise ValueError("enabled must be a boolean")
            self.enabled = options["enabled"]

    def publish(self, uri):
        doc = self.documents[uri]
        findings, _ = lint(doc["text"], self.rules if self.enabled else set(), self.analyze)
        doc["findings"] = findings
        diagnostics = [{"range": f["edit"]["range"], "severity": 4, "source": "LeanPerf",
                        "code": f["rule"], "message": RULES[f["rule"]]} for f in findings]
        self.send({"method": "textDocument/publishDiagnostics", "params": {
            "uri": uri, "version": doc["version"], "diagnostics": diagnostics}})

    def actions(self, params):
        uri = params["textDocument"]["uri"]
        doc = self.documents.get(uri)
        if not doc or not doc["findings"]:
            return []
        only = params["context"].get("only", [])
        def wanted(kind):
            return not only or any(kind == k or kind.startswith(k + ".") for k in only)
        def action(title, kind, findings):
            edits = [f["edit"] for f in findings]
            if self.versioned_edits:
                workspace = {"documentChanges": [{"textDocument": {
                    "uri": uri, "version": doc["version"]}, "edits": edits}]}
            else:
                workspace = {"changes": {uri: edits}}
            return {"title": title, "kind": kind, "edit": workspace}
        results = []
        if wanted("quickfix"):
            r = params["range"]
            for f in doc["findings"]:
                span = f["edit"]["range"]
                if pos_key(span["start"]) <= pos_key(r["end"]) and pos_key(r["start"]) < pos_key(span["end"]):
                    results.append(action(RULES[f["rule"]], "quickfix", [f]))
        if wanted("source.fixAll.leanPerf"):
            results.append(action("Apply all LeanPerf fixes", "source.fixAll.leanPerf",
                                  independent(doc["findings"])))
        return results

    def handle(self, method, p):
        if method == "initialize":
            self.versioned_edits = p.get("capabilities", {}).get("workspace", {}).get(
                "workspaceEdit", {}).get("documentChanges", False)
            self.configure(p.get("initializationOptions") or {})
            return {"capabilities": {"positionEncoding": "utf-16", "textDocumentSync": 1,
                    "codeActionProvider": {"codeActionKinds": ["quickfix", "source.fixAll.leanPerf"]}},
                    "serverInfo": {"name": "LeanPerf"}}
        if method == "shutdown":
            self.shutdown = True
        elif method == "textDocument/didOpen":
            d = p["textDocument"]
            self.documents[d["uri"]] = {"version": d["version"], "text": d["text"]}
            self.publish(d["uri"])
        elif method == "textDocument/didChange":
            d = p["textDocument"]
            doc = self.documents[d["uri"]]
            if d["version"] > doc["version"]:
                doc.update(version=d["version"], text=p["contentChanges"][-1]["text"])
                self.publish(d["uri"])
        elif method == "textDocument/didClose":
            uri = p["textDocument"]["uri"]
            self.documents.pop(uri, None)
            self.send({"method": "textDocument/publishDiagnostics", "params": {"uri": uri, "diagnostics": []}})
        elif method == "workspace/didChangeConfiguration":
            self.configure((p.get("settings") or {}).get("leanPerf", {}))
            for uri in self.documents:
                self.publish(uri)
        elif method == "textDocument/codeAction":
            return self.actions(p)
        elif method not in {"initialized", "$/cancelRequest", "$/setTrace"}:
            raise NotImplementedError(method)


def run_server(analyze, rules):
    send = lambda msg: write_lsp(sys.stdout.buffer, msg)
    server = LanguageServer(analyze, rules, send)
    while (msg := read_lsp(sys.stdin.buffer)) is not None:
        if msg.get("method") == "exit":
            return int(not server.shutdown)
        try:
            result = server.handle(msg["method"], msg.get("params") or {})
            if "id" in msg:
                send({"id": msg["id"], "result": result})
        except (NotImplementedError, KeyError, ValueError, TypeError, IndexError) as error:
            code = -32601 if isinstance(error, NotImplementedError) else -32602
            if "id" in msg:
                send({"id": msg["id"], "error": {"code": code, "message": str(error)}})
    return 0


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("paths", type=Path, nargs="*", help="Lean files or directories")
    p.add_argument("--lsp", action="store_true", help="serve LSP over stdio")
    p.add_argument("--rules", default=",".join(RULES), help="comma-separated: " + ", ".join(RULES))
    p.add_argument("--apply", action="store_true", help="apply static fixes in place")
    p.add_argument("--check", action="store_true", help="also elaborate rewritten files with the target Lake project")
    p.add_argument("--bench", type=int, default=0, metavar="N", help="time N original and N rewritten Lake checks")
    args = p.parse_args()
    if args.bench < 0 or (args.lsp and (args.paths or args.apply or args.check or args.bench)) or not (args.lsp or args.paths):
        p.error("select --lsp alone or supply Lean paths with batch options")
    rules = checked_rules(args.rules.split(","))
    with parser_process() as analyze:
        return run_server(analyze, rules) if args.lsp else run_cli(args, rules, analyze)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        sys.exit(str(error))
