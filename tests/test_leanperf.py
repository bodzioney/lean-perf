import io
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import leanperf


def cli(*args, cwd=ROOT):
    return subprocess.run([sys.executable, ROOT / "leanperf.py", *args], cwd=cwd,
                          capture_output=True, timeout=120)


class LeanPerfTests(unittest.TestCase):
    def test_checked_preview(self):
        f = ROOT / "tests/Examples.lean"
        original = f.read_bytes()
        r = cli("--check", str(f))
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertIn(b"3 edits", r.stderr)
        self.assertIn(b"+  have hObtained' := f", r.stdout)
        self.assertEqual(original, f.read_bytes())

    def test_static_apply_never_loads_the_project(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            marker = root / "executed"
            (root / "lean-toolchain").write_text("intentionally-unavailable")
            (root / "lakefile.lean").write_text("invalid project configuration")
            f = root / "Example.lean"
            original = (f'import Missing.Dependency\n#eval IO.FS.writeFile "{marker}" "ran"\n'
                        '/- example (x : Nat) : x = x := by simp -/\n'
                        'def quoted := "example (x : Nat) : x = x := by simp"\n'
                        'example (𝒳 : Nat) : 𝒳 = 𝒳 := by simp\n'
                        'example (x : Nat) : 0 + x = x := by simp\n'
                        'example (x : Nat) : x = x := by\n  first | simp | rfl\n'
                        'example (h : True) : True := by simpa using h\n').replace('\n', '\r\n').encode()
            f.write_bytes(original)
            r = cli("--apply", "--rules", "simpRfl", str(root), cwd=root)
            self.assertEqual(r.returncode, 0, r.stderr)
            self.assertEqual(f.read_bytes(), original.replace('𝒳 := by simp'.encode(), '𝒳 := by rfl'.encode()))
            self.assertFalse(marker.exists())
            again = cli("--rules", "simpRfl", str(f), cwd=root)
            self.assertEqual(again.stdout, b"")
            self.assertEqual(again.returncode, 0, again.stderr)

    def test_failed_check_preserves_source(self):
        with tempfile.TemporaryDirectory() as d:
            f = Path(d) / "Broken.lean"
            f.write_text("example (x : Nat) : x = x := by simp\nexample : False := by exact True.intro\n")
            original = f.read_bytes()
            r = cli("--apply", "--check", str(f))
            self.assertNotEqual(r.returncode, 0)
            self.assertIn(b"Lake check failed", r.stderr)
            self.assertEqual(f.read_bytes(), original)

    def test_language_server(self):
        body = "example (𝒳 : Nat) : 𝒳 = 𝒳 := by simp\n"
        uri = "file:///unsaved%20proof.lean"
        doc = {"uri": uri}
        buf = io.BytesIO()
        def send(method, params, request=None):
            msg = {"method": method, "params": params}
            if request is not None:
                msg["id"] = request
            leanperf.write_lsp(buf, msg)
        send("initialize", {"capabilities": {"workspace": {"workspaceEdit": {"documentChanges": True}}},
                            "initializationOptions": {"rules": ["simpRfl"]}}, 1)
        send("initialized", {})
        send("textDocument/didOpen", {"textDocument": {**doc, "version": 1, "languageId": "lean", "text": body}})
        col = len(body.split("simp")[0].encode("utf-16-le")) // 2
        caret = {"line": 0, "character": col}
        params = {"textDocument": doc, "range": {"start": caret, "end": caret}, "context": {"diagnostics": []}}
        send("textDocument/codeAction", params, 2)
        send("textDocument/codeAction", {**params, "context": {"only": ["source.fixAll"], "diagnostics": []}}, 3)
        send("workspace/didChangeConfiguration", {"settings": {"leanPerf": {"enabled": False}}})
        send("textDocument/codeAction", params, 4)
        send("workspace/didChangeConfiguration", {"settings": {"leanPerf": {"enabled": True}}})
        send("textDocument/didChange", {"textDocument": {**doc, "version": 2},
                                        "contentChanges": [{"text": body.replace("simp", "rfl")}]})
        send("textDocument/codeAction", params, 5)
        send("textDocument/didClose", {"textDocument": doc})
        send("shutdown", None, 6)
        send("exit", None)
        run = subprocess.run([sys.executable, ROOT / "leanperf.py", "--lsp"], input=buf.getvalue(),
                             capture_output=True, timeout=90)
        self.assertEqual(run.returncode, 0, run.stderr)
        replies, notifications = {}, []
        result = io.BytesIO(run.stdout)
        while (msg := leanperf.read_lsp(result)) is not None:
            if "id" in msg:
                replies[msg["id"]] = msg["result"]
            else:
                notifications.append(msg["params"])
        self.assertEqual(replies[1]["capabilities"]["positionEncoding"], "utf-16")
        diag = notifications[0]["diagnostics"][0]
        self.assertEqual(diag["code"], "simpRfl")
        self.assertEqual(diag["range"]["start"], caret)
        quick, fix_all = replies[2]
        self.assertEqual(quick["kind"], "quickfix")
        change, = quick["edit"]["documentChanges"]
        self.assertEqual(change["textDocument"], {**doc, "version": 1})
        self.assertEqual(change["edits"], [{"range": diag["range"], "newText": "rfl"}])
        self.assertEqual(replies[3], [fix_all])
        self.assertEqual(replies[4], [])
        self.assertEqual(replies[5], [])
        self.assertEqual(notifications[-1]["diagnostics"], [])


if __name__ == "__main__":
    unittest.main()
