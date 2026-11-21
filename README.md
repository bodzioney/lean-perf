# LeanPerf

LeanPerf finds and rewrites Lean proof patterns by parsing source text. Its command line and language server use the same Lean rules. You can lint an unsaved buffer or an entire source tree before any project dependency has been built.

The default scan reads Lean files. The parser loads its own grammar and the pinned Lean toolchain. Project imports, tactics, macros, `#eval` commands and the project's Lake configuration are never executed by the scan.

## Getting started

Install Python 3.9 or later and Elan with the toolchain in `lean-toolchain` (Lean 4.33.1). Build the parser in this repository with `lake build`. The launcher also builds it on first use. From the project you want to lint, run the following commands, adjusting the checkout path as needed.

```sh
# Preview a unified diff for a directory
~/Code/lean-perf/leanperf.py src/

# Apply one rule to a file, entirely offline once the toolchain is installed
~/Code/lean-perf/leanperf.py --rules simpRfl --apply src/Example.lean

# Ask the target project's Lean compiler to check a candidate before writing it
~/Code/lean-perf/leanperf.py --rules splitObtain --apply --check src/Example.lean

# Compare original and rewritten compilation times without editing the file
~/Code/lean-perf/leanperf.py --bench 4 src/Example.lean
```

`--rules` takes a comma-separated list of rule names. Preview and apply are syntax-only by default. `--check` and `--bench` explicitly run the target's Lake configuration and Lean elaborator. Run these two modes from the target's Lake project root with its imports already built. They use `lake --no-build --no-cache lean` on the original module path and supply the candidate on stdin. A failed check leaves that file alone and produces a nonzero exit status. Directory edits are atomic per file.

Timing includes Lake startup and import loading. The benchmark alternates the order of the two versions and reports median wall time. The effect on a full build depends on which modules are rebuilt.

## Rules

| Rule | Candidate |
|---|---|
| `simpRfl` | For a declaration with an explicit goal such as `x = x` and the entire proof `by simp`, suggest `by rfl`. Both operands must be the same identifier. |
| `exactUsing` | For a whole proof `by simpa using h`, suggest `by exact h` when the final explicit binder names `h` and its type has the same source text as the goal. |
| `splitObtain` | For a standalone `obtain ⟨…⟩ := f …`, introduce a fresh `have` for the application, then destructure the local result. This can reduce elaboration time in dependent proofs. |

For example, LeanPerf can recognize `example (x : Nat) : x = x := by simp` directly. A goal such as `0 + x = x`, or a `simp` after another tactic, needs information outside that pattern. LeanPerf skips those cases. A syntax match is a candidate for a proof edit. Use `--check` for compiler confirmation.

The parser understands the pinned Lean grammar and a small set of common Mathlib notation. Commands that need other imported or locally declared syntax can be skipped. The CLI reports how many commands the parser could not read. Add parser declarations in `LeanPerf/Grammar.lean` and rewrite rules in `LeanPerf.lean`.

## Editor integration

Start `python3 /absolute/path/to/leanperf.py --lsp` as an additional language server for Lean files. The server accepts full-document changes over stdio and publishes diagnostics for the current buffer version. The editor can request an individual quick fix or `source.fixAll.leanPerf` for the document. Edits use UTF-16 positions and include the document version when the client supports versioned workspace edits.

For Neovim 0.11 or later, place this in your configuration alongside your existing Lean server.

```lua
vim.lsp.config('leanperf', {
  cmd = { 'python3', vim.fn.expand('~/Code/lean-perf/leanperf.py'), '--lsp' },
  filetypes = { 'lean' },
  root_markers = { 'lean-toolchain', '.git' },
})
vim.lsp.enable('leanperf')
```

Use `vim.lsp.buf.code_action()` on a diagnostic. To change the defaults, pass `initializationOptions` such as `{"enabled": true, "rules": ["simpRfl", "splitObtain"]}`. A client can also send `workspace/didChangeConfiguration` with the new values under `settings.leanPerf`. Setting `enabled` to `false` clears the diagnostics for open buffers.

## Tests

Run `python3 -m unittest discover -s tests -v`. The integration tests exercise the parser, optional compilation, static rewriting without project dependencies, and LSP diagnostics and edits.
