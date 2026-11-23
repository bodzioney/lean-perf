# LeanPerf

LeanPerf finds and rewrites Lean proof patterns by parsing source text. Its command line and language server use the same Lean rules. You can lint an unsaved buffer or an entire source tree before any project dependency has been built.

The default scan reads Lean files. The parser loads its own grammar and the pinned Lean toolchain. Project imports, tactics, macros, `#eval` commands and the project's Lake configuration are never executed by the scan.

## Getting started

Install Elan with the toolchain in `lean-toolchain` (Lean 4.37.0-rc1) and run `lake build` in this repository. This builds `leanperf`, one native executable for the command line, the language server and the elaborated passes. Nothing else is required. From the project you want to lint, run the following commands, adjusting the checkout path as needed.

```sh
# Preview a unified diff for a directory
~/Code/lean-perf/.lake/build/bin/leanperf src/

# Apply one rule to a file, entirely offline once the toolchain is installed
~/Code/lean-perf/.lake/build/bin/leanperf --rules simpRfl --apply src/Example.lean

# Ask the target project's Lean compiler to check a candidate before writing it
~/Code/lean-perf/.lake/build/bin/leanperf --rules splitObtain --apply --check src/Example.lean

# Compare original and rewritten compilation times without editing the file
~/Code/lean-perf/.lake/build/bin/leanperf --bench 4 src/Example.lean
```

`--rules` takes a comma-separated list of rule names. Preview and apply are syntax-only by default. `--check` and `--bench` explicitly run the target's Lake configuration and Lean elaborator. Run these two modes from the target's Lake project root with its imports already built. They use `lake --no-build --no-cache lean` on the original module path and supply the candidate on stdin. A failed check leaves that file alone and produces a nonzero exit status. Directory edits are atomic per file.

`--shorter` selects edits that reduce the UTF-8 byte count of the replaced source. Use it for proof compression, including with `--dedup --check --apply`. Measure compilation time separately with `--bench`.

Timing includes Lake startup and import loading. The benchmark alternates the order of the two versions and reports median wall time. The effect on a full build depends on which modules are rebuilt.

## Rules

| Rule | Candidate |
|---|---|
| `simpRfl` | For a declaration with an explicit goal such as `x = x` and the entire proof `by simp`, suggest `by rfl`. Both operands must be the same identifier. |
| `rflTerm` | For a declaration with an explicit equality goal and the whole proof `by rfl`, suggest the term `rfl`. Comments inside the proof are preserved by skipping the edit. |
| `exactUsing` | For a whole proof `by simpa using h`, suggest `by exact h` when the final explicit binder names `h` and its type has the same source text as the goal. |
| `splitObtain` | For a standalone `obtain ⟨…⟩ := f …`, introduce a fresh `have` for the application, then destructure the local result. This can reduce elaboration time in dependent proofs. |

For example, LeanPerf can recognize `example (x : Nat) : x = x := by simp` directly. A goal such as `0 + x = x`, or a `simp` after another tactic, needs information outside that pattern. LeanPerf skips those cases. A syntax match is a candidate for a proof edit. Use `--check` for compiler confirmation.

The parser understands the pinned Lean grammar and a small set of common Mathlib notation. Commands that need other imported or locally declared syntax can be skipped. The CLI reports how many commands the parser could not read. Add parser declarations in `LeanPerf/Grammar.lean` and rewrite rules in `LeanPerf.lean`.

## Duplicate theorems

`--dedup` reports theorems that restate an existing theorem. It has two passes. The elaborated pass needs the project's dependencies built. It also finds theorems that are a special case of a more general one and suggests a one-term proof that cites it. The syntactic pass needs nothing built and runs no Lean. By default, `--dedup` elaborates when it can and falls back to syntax, saying why. `--dedup-pass syntax` or `--dedup-pass elaborate` chooses one. Run either from the target's Lake project root.

```sh
# Report on a directory, and preview the suggested proofs when dependencies are built
~/Code/lean-perf/.lake/build/bin/leanperf --dedup src/

# Elaborate each rewritten file in full before replacing its proofs
~/Code/lean-perf/.lake/build/bin/leanperf --dedup --check --apply src/Example.lean

# Compare spelling only: nothing is built, and no Lean or Lake runs
~/Code/lean-perf/.lake/build/bin/leanperf --dedup-pass syntax src/
```

The `auto` pass checks that the target uses LeanPerf's toolchain, asks Lake for the search path without building, and checks that each dependency the analyzed files import, directly or through project modules, has an `.olean`.

### The elaborated pass

Build and run the native Lean executable directly from the target Lake project. For example, in the Riemann checkout the following commands build skeletons and preview shorter proofs.

```sh
lint=~/Code/lean-perf/.lake/build/bin/leanperf

# Build dependency skeletons for a directory and populate the project-local cache
"$lint" --project --build-only --jobs=2 src/Lemmata

# Report shorter proof terms and their source locations
"$lint" --project --shorter --jobs=1 src/Lemmata/FirstBlockLemmaD
```

With `--project`, the executable runs the builder directly and expands directories internally. Its default report includes verified replacements and duplicates in other modules. Without it, the command line adds unified diffs, checked application, the syntax fallback and LSP integration, using the same builder and cache.

LeanPerf plans the project import graph and gives ready modules to a bounded pool of Lean processes. Each worker elaborates a module against its imports and can reuse the imported environment and theorem index across modules with the same header. The default is two workers. Each worker loading a large dependency such as Mathlib needs memory for its own elaborator and index. Use `--jobs=1` to bound that cost or set `LEANPERF_JOBS` for the CLI and editor.

Skeletons live under `.lake/leanperf`, separate from Lake's build products. Set `LEANPERF_CACHE_DIR` to choose another location. Each entry contains the module's serialized Lean artifacts, canonical theorem types and, after analysis, its local report. The builder publishes completed entries with an atomic rename. Cache keys include source content, direct dependency keys, the toolchain and executable identity, search path, project configuration and options. External compiled dependencies are tracked by artifact path, size and modification time through their import graph. Old entries can be reclaimed by removing the LeanPerf cache directory between runs. Projects whose metaprograms read additional inputs should start a fresh cache when those inputs change.

For statement comparison, LeanPerf opens the outer binders, orders them subject to their dependencies and closes the type again. Bound occurrences use Lean's de Bruijn indices throughout. In `fun x => fun y => x` the occurrence is index 1, while in `fun x => fun x => x` it is index 0. The persisted expressions erase display names and binder annotations on quantifiers, lambdas and lets, and normalize universe parameters by first occurrence. Global constants retain their qualified names. A hash locates candidates, and structural equality checks the complete canonical types. A discrimination tree also finds special cases. Each suggested term must elaborate against the original statement in the declaration's own environment.

Requested modules and their unbuilt project dependencies are elaborated as skeletons. LeanPerf can import a project dependency with an up-to-date `.olean`. Skeletons replace theorem proofs and proposition-valued tactic blocks with `sorry`, skip kernel checking, and retain executable definitions for imported metaprograms. A failed skeleton reports its errors and can be retried after correction. With `--check`, LeanPerf elaborates the entire edited module with its proofs and kernel checks enabled against its dependency skeletons. Verifying the complete proof development requires a full Lean build. The native launcher reads `srcDir` and global `[leanOptions]` from `lakefile.toml`. Per-library options are currently unsupported.

Unlike the default scan, the elaborated pass runs the target's Lake configuration and imports its dependencies, including their tactics and macros. The target must use LeanPerf's toolchain (`lean-toolchain`), since `.olean` files are specific to one Lean version.

### The syntactic pass

The syntactic pass reads source files only. It tokenizes each theorem's statement, so it does not depend on knowing the project's notation. It flattens leading `∀` binders and hypotheses written as arrows into binders, adds the section `variable`s that the statement mentions, and drops coercion arrows and redundant parentheses. It uses relative de Bruijn indices for recognized telescope and nested binders, with index zero referring to the nearest binder. It renames universes by position and orders telescope binders as the elaborated pass does. Theorems with the same result are reported as likely restatements, without a fix. The pass cannot see the dependencies' theorems, resolve names through `open` or namespaces, or infer the types of untyped binders.

In a benchmark of the original serial pass on a library of 499 unbuilt files and 6,676 theorems, the syntactic pass took 4 seconds and the elaborated pass took 10 minutes. The elaborated pass confirmed 430 of the 433 syntactic matches, 411 as restatements and 19 as special cases of a more general lemma. The syntactic pass found 380 of the 507 restatements of project theorems that the elaborated pass found.

For both passes, a restatement that the theorem cannot cite, because its module is not imported or the restatement is private, is reported without a fix. When the other theorem can cite this one, only the other is reported.

## Cheaper tactics

`--tactics` replays alternative tactics on the goals where the original tactic ran. For a bare `linarith` or `nlinarith`, it reads the local hypotheses used by the original proof term and tries restricting arithmetic search to those hypotheses with `only [...]`. It also tries `linarith` and `positivity` for `nlinarith`, `simp` for `norm_num`, and the explicit simplification suggested by `simp?`, `simp_all?` or `simpa?`.

A candidate must leave the same goals on every replay, introduce no errors or `sorry`, and use fewer heartbeats in total. Goals are compared as closed terms with their hypothesis names. With `--shorter`, the pass selects the cheapest successful candidate that also reduces the source byte count. The pass also tries deleting scoped overrides of `maxHeartbeats`, `synthInstance.maxHeartbeats`, `maxRecDepth`, `synthInstance.maxSize` and the supported `backward.isDefEq` options, checking whether the command still elaborates.

```sh
# Preview, then apply after elaborating each edited module in full
~/Code/lean-perf/.lake/build/bin/leanperf --tactics src/
~/Code/lean-perf/.lake/build/bin/leanperf --tactics --check --apply src/Example.lean
```

The tactic pass builds skeletons only for project modules imported by another target or dependency. External imports must already have compatible `.olean` files. It caches successful replay results under `.lake/leanperf/tactics`, keyed by the source, dependencies, build settings, LeanPerf executable, `--min-saving` and `--shorter`. `--check` elaborates the edited module even on a cache hit. Set `LEANPERF_CACHE_DIR` to choose another cache directory.

Heartbeats measure elaboration. Use `--bench` to measure wall time including kernel checking. `--min-saving N` (default 1) skips edits that save fewer than `N` heartbeats.

## Compressing proofs

Run `leanperf --compress src/` to preview shorter proofs, or add `--apply` to write the checked changes. The pass compares each `by` proof with short representations of the elaborated proof, local hypotheses, earlier theorems in the module, and imported theorems. It also tries using equalities and iff statements in reverse. For example, it can replace an induction proving Gauss's summation formula in reverse with `Eq.symm (Finset.sum_range_id_mul_two n)` when the Mathlib theorem is imported.

A bounded structural fingerprint indexes theorem conclusions. Lean checks each proposed term in its local context. When edits overlap, the optimizer chooses the combination that saves the most UTF-8 bytes. It preserves comments inside proof blocks and checks the whole rewritten module. Compression also runs the shorter tactic optimizations. Use `--bench` to measure how the edits affect compilation time.

## Editor integration

Start `/absolute/path/to/lean-perf/.lake/build/bin/leanperf --lsp` as an additional language server for Lean files. The server accepts full-document changes over stdio and publishes diagnostics for the current buffer version. The editor can request an individual quick fix or `source.fixAll.leanPerf` for the document. Edits use UTF-16 positions and include the document version when the client supports versioned workspace edits.

For Neovim 0.11 or later, place this in your configuration alongside your existing Lean server.

```lua
vim.lsp.config('leanperf', {
  cmd = { vim.fn.expand('~/Code/lean-perf/.lake/build/bin/leanperf'), '--lsp' },
  filetypes = { 'lean' },
  root_markers = { 'lean-toolchain', '.git' },
})
vim.lsp.enable('leanperf')
```

Use `vim.lsp.buf.code_action()` on a diagnostic. To change the defaults, pass `initializationOptions` such as `{"enabled": true, "rules": ["simpRfl", "splitObtain"]}`. Add `"dedup": true` to report duplicate theorems in the current buffer, including unsaved edits, as information diagnostics, with a quick fix from the elaborated pass. The first buffer chooses the pass for the workspace as `--dedup` does, or `"dedup"` names one: `"syntax"` or `"elaborate"`. The analysis runs in the background from the workspace root. With the elaborated pass, the first buffer waits for its dependencies to be elaborated, and later edits re-elaborate only the buffer. A client can also send `workspace/didChangeConfiguration` with the new values under `settings.leanPerf`. Setting `enabled` to `false` clears the diagnostics for open buffers.

## Tests

Run `lake test`, or `lake test -- <words>` for the tests whose names contain those words. The integration tests exercise the parser, optional compilation, static rewriting without project dependencies, LSP diagnostics and edits, and both duplicate passes on the core-only project in `tests/dedup`. They also exercise cache reuse, transitive invalidation, concurrent publishers, failed builds, and nested binder shadowing.
