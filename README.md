# LeanPerf

LeanPerf finds duplicate theorems, replaces expensive tactics, and shortens proofs and theorem statements. The default syntax lints work on an unsaved buffer or a whole source tree before dependencies are built. The elaborated modes use Lean to construct and check candidate proofs.

The default scan reads Lean files. The parser loads its own grammar and the pinned Lean toolchain. Project imports, tactics, macros, `#eval` commands and the project's Lake configuration are never executed by the scan.

## Getting started

Install Elan with the toolchain in `lean-toolchain` (Lean 4.37.0-rc1) and run `lake build` in this repository. This builds `leanperf`, one native executable for the command line, the language server and the elaborated passes. Nothing else is required. From the project you want to lint, run the following commands, adjusting the checkout path as needed.

```sh
# Shrink a directory's proofs with every checked pass, in order (see "Iterating")
~/Code/lean-perf/.lake/build/bin/leanperf --golf src/

# Preview a unified diff for a directory
~/Code/lean-perf/.lake/build/bin/leanperf src/

# Apply one rule to a file, entirely offline once the toolchain is installed
~/Code/lean-perf/.lake/build/bin/leanperf --rules simpRfl --apply src/Example.lean

# Ask the target project's Lean compiler to check a candidate before writing it
~/Code/lean-perf/.lake/build/bin/leanperf --rules splitObtain --apply --check src/Example.lean

# Compare original and rewritten compilation times without editing the file
~/Code/lean-perf/.lake/build/bin/leanperf --bench 4 src/Example.lean
```

Preview and apply are syntax-only by default. `--check` and `--bench` explicitly run the target's Lake configuration and Lean elaborator. Run these two modes from the target's Lake project root with its imports already built. They use `lake --no-build --no-cache lean` on the original module path and supply the candidate on stdin. A failed check leaves that file alone and produces a nonzero exit status.

`--shorter` selects edits that reduce the UTF-8 byte count of the replaced source. Use it for proof compression, including with `--dedup --check --apply`. Measure compilation time separately with `--bench`.

Timing includes Lake startup and import loading. The benchmark alternates the order of the two versions and reports median wall time. The effect on a full build depends on which modules are rebuilt.

## Choosing lints

Run `leanperf --list-lints` to see each lint's name, mode and purpose. Pick the mode that fits your goal. Within that mode, `--rules` selects a comma-separated list and `--allow` (or `-A`) suppresses named lints. Existing names also appear in diagnostics. The individual names and allow switch follow the approach used by [Clippy](https://doc.rust-lang.org/clippy/configuration.html#allowingdenying-lints).

| Goal | Mode | Available lints |
|---|---|---|
| Clean up straightforward proof syntax | Default | `simpRfl`, `rflTerm`, `exactUsing`, `splitObtain` |
| Find likely restatements before building dependencies | `--dedup-pass syntax` | `syntacticDuplicate` |
| Find restatements and more general theorems | `--dedup-pass elaborate` | `duplicate`, `specialCase` |
| Reduce tactic search | `--tactics` | `fasterTactic`, `unneededOption`, `unneededSeal` |
| Shrink everything, in the order below | `--golf` | every pass that follows, in turn |
| Take tactic steps and declarations out of proofs with a checked rewrite | `--compress` | `reuseProof`, `reprove`, `unusedHave`, `redundantShow`, `unneededClassical`, `shorterBlock`, `unneededStep`, `contractPair`, `inlineHave`, `haveToRefine`, `obtainProjection`, `termExact`, `termCompile`, `simpaUsing`, `rwaAt`, `mergeRw`, `foldHelper` |
| Also save bytes without changing the steps | `--compress --cosmetic` | adds `restatedType`, `redundantAscription`, `unneededErasure`, `shorterSimp`, `shortProjection`, `shortNames`, `sharedHaveBinders`, `shorterSignature`, `unusedInstance` |
| Delete theorems nothing uses, before building dependencies | `--unused` | `unusedTheorem` |
| Put continuation lines on the line they continue | `--layout` | `joinLines`, and `stripComments` when `--rules` names it |
| Rewrite theorems with an external proposer, such as a language model | `--propose CMD` | `rewrite` |

```sh
leanperf --dedup-pass elaborate --rules duplicate --check src/
leanperf --dedup-pass elaborate --rules specialCase --shorter --check src/
leanperf --compress -A shorterSignature src/
```

Selecting only `duplicate` skips the general-theorem search index. A compression run that excludes `reuseProof` skips its imported proof index. The batch modes preview changes by default. Add `--apply` to write the selected edits.

## Syntax rules

| Rule | Candidate |
|---|---|
| `simpRfl` | For a declaration with an explicit goal such as `x = x` and the entire proof `by simp`, suggest `by rfl`. Both operands must be the same identifier. |
| `rflTerm` | For a declaration with an explicit equality goal and the whole proof `by rfl`, suggest the term `rfl`. Comments inside the proof are preserved by skipping the edit. |
| `exactUsing` | For a whole proof `by simpa using h`, suggest `by exact h` when the final explicit binder names `h` and its type has the same source text as the goal. |
| `splitObtain` | For a standalone `obtain ⟨…⟩ := f …`, introduce a fresh `have` for the application, then destructure the local result. This can reduce elaboration time in dependent proofs. |

For example, LeanPerf can recognize `example (x : Nat) : x = x := by simp` directly. A goal such as `0 + x = x`, or a `simp` after another tactic, needs information outside that pattern. LeanPerf skips those cases. A syntax match is a candidate for a proof edit. Use `--check` for compiler confirmation.

The parser understands the pinned Lean grammar and a small set of common Mathlib notation. Commands that need other imported or locally declared syntax can be skipped. The CLI reports how many commands the parser could not read. The parser declarations live in `LeanPerf/Grammar.lean`, the syntax rules in `LeanPerf/Rules.lean` and the lint catalog in `LeanPerf/Lints.lean`.

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

The elaborated matcher distinguishes two useful questions. For **duplicates**, it compares the closed types and keeps the binder correspondence. If two binders both have type `Nat`, their occurrences in later hypotheses can tell them apart. Even an argument unused by the original theorem can be supplied in a replacement. Each imported bucket of canonical types is indexed on first use.

For **specializations**, the matcher tries to construct an application of the candidate theorem with one consistent substitution. For example, a theorem requiring `Token n` and `Grant n` can use the two projections of a local `h : Token n ∧ Grant n`. If several hypotheses match, the search can revisit its first choice when a later premise fails. It permits up to 64 matching premise assignments per candidate. A `Token n` and a `Grant m` for unrelated indices do not discharge those premises together. The matcher uses no Riemann-specific names or rewrite rules.

### The syntactic pass

The syntactic pass reads source files only. It tokenizes each theorem's statement, so it does not depend on knowing the project's notation. It flattens leading `∀` binders and hypotheses written as arrows into binders, adds the section `variable`s that the statement mentions, and drops coercion arrows and redundant parentheses. It uses relative de Bruijn indices for recognized telescope and nested binders, with index zero referring to the nearest binder. It renames universes by position and orders telescope binders as the elaborated pass does. Theorems with the same result are reported as likely restatements, without a fix. The pass cannot see the dependencies' theorems, resolve names through `open` or namespaces, or infer the types of untyped binders.

In a benchmark of the original serial pass on a library of 499 unbuilt files and 6,676 theorems, the syntactic pass took 4 seconds and the elaborated pass took 10 minutes. The elaborated pass confirmed 430 of the 433 syntactic matches, 411 as restatements and 19 as special cases of a more general lemma. The syntactic pass found 380 of the 507 restatements of project theorems that the elaborated pass found.

For both passes, a restatement that the theorem cannot cite, because its module is not imported or the restatement is private, is reported without a fix. When the other theorem can cite this one, only the other is reported.

## Cheaper tactics

`--tactics` replays alternative tactics on the goals where the original tactic ran. For `linarith` and `nlinarith`, it reads the hypotheses used by the original proof term and tries restricting arithmetic search to them with `only [...]`. When the tactic supplies extra premises, it tries those terms on their own and combined with the inferred hypotheses. It also tries `linarith` and `positivity` for `nlinarith`, `assumption` and `omega` for `linarith`, `simp` for `norm_num`, `rw` for `erw`, and a rewrite with the same lemmas for `simp [...]` and `simp_rw [...]`. It tries the explicit simplification suggested by `simp?`, `simp_all?` or `simpa?`, and the `grind only [...]` call that `grind?` reports. For a bare `grind` it also tries `omega`, `simp`, `simp_all`, `positivity` and `linarith`, and for a bare `aesop` it tries `simp` and `simp_all`. The cheapest closers run first, and the first success bounds the heartbeats of every later attempt.

A candidate must leave the same goals on every replay, introduce no errors or `sorry`, and use fewer heartbeats in total. Goals are compared as closed terms with their hypothesis names. A replay runs in the environment from before the declaration, so a tactic such as `simp` cannot prove a `@[simp]` lemma with that lemma itself. It also runs any tactic block that a term postponed, and fails if the proof keeps a hole that is not one of the reported goals. With `--shorter`, the pass selects the cheapest successful candidate that also reduces the source byte count. The pass also tries deleting scoped overrides of `maxHeartbeats`, `synthInstance.maxHeartbeats`, `maxRecDepth`, `synthInstance.maxSize` and the supported `backward.isDefEq` options, checking whether the command still elaborates.

```sh
# Preview, then apply after elaborating each edited module in full
~/Code/lean-perf/.lake/build/bin/leanperf --tactics src/
~/Code/lean-perf/.lake/build/bin/leanperf --tactics --check --apply src/Example.lean
```

The tactic pass builds skeletons only for project modules imported by another target or dependency, and only when their `.olean` is missing or older than the source. A target with a current `.olean` is analyzed from its source, while the modules that import it load the `.olean`, since the edits LeanPerf checks keep every exported type. In a built project, no skeletons are needed. External imports must already have compatible `.olean` files. A skeleton can elaborate differently from its source, for example when a definition uses a section variable only inside a proof that becomes `sorry`. When a skeleton reports errors, the module is elaborated with its proofs instead. Batch replay analyzes up to `--jobs N` files concurrently (default 2) and emits edits in path order. It caches successful reports under `.lake/leanperf/tactics`, keyed by the source, dependencies, build settings, LeanPerf executable, saving threshold and compression options. `--check` elaborates the edited module even on a cache hit. Set `LEANPERF_CACHE_DIR` to choose another cache directory.

`unneededSeal` deletes `seal f in` or `unseal f in` in front of a command, together with a one-line `--` comment directly above it. A seal keeps definitional checks from unfolding `f`, which usually exists for speed. So the command is elaborated with and without it, and the seal goes only when the command elaborates without errors, declares the same types, and uses no more heartbeats. On three seals in the Riemann module `ThreeExchanges`, elaborating without them took 1.3 to 4.4 times the heartbeats, and LeanPerf kept all three.

Heartbeats measure elaboration. Use `--bench` to measure wall time including kernel checking. `--min-saving N` (default 1) skips edits that save fewer than `N` heartbeats.

## Compressing proofs

Run `leanperf --compress src/` to preview shorter proofs, or add `--apply` to write the checked changes. A proof is shorter when it has fewer tactic steps or the module fewer declarations, not merely fewer bytes. A step is a tactic wherever it is, including the tactic blocks inside terms. Tactics that only arrange others, such as sequences, bullets, parentheses, `<;>`, `case` and `next`, do not count. So `rw [a, b]` is one step and `exact f (by simp)` two. When several rewrites take out as many steps, the one that Lean elaborates with the fewest heartbeats wins, and then the one with fewer bytes: `rwa [h]` before `grind`, which searches for what the steps spelled out. Lints that only save bytes, such as shorter local names or dropped type ascriptions, run with `--cosmetic`, and the lints that make tactics cheaper with `--tactics`. The pass compares each `by` proof with short representations of the elaborated proof, local hypotheses, earlier theorems in the module, and imported theorems. It also tries using equalities and iff statements in reverse. For example, it can replace an induction proving Gauss's summation formula in reverse with `Eq.symm (Finset.sum_range_id_mul_two n)` when the Mathlib theorem is imported.

A bounded structural fingerprint indexes theorem conclusions. Lean checks each proposed term in its local context. A term that names a constant the elaborator generated, such as `inst._proof_11`, is rejected, since the numbering of such constants changes when the module changes. When edits overlap, the optimizer chooses the combination that saves the most UTF-8 bytes. Each lint checks its edit against the original declaration, and two edits that are each correct can conflict. A replay can also differ from elaboration: the info tree may record a `by` block nested in a term, such as a `calc` step, in a state the elaborator never reaches. So LeanPerf elaborates a declaration with all its edits when it has several, or when one was checked only by a replay, and splits the group on failure. A failing whole-module check would otherwise discard every edit in the file. It preserves comments inside proof blocks and checks the whole rewritten module. Use `--bench` to measure how the edits affect compilation time.

The whole-declaration lints `unusedHave`, `reprove`, `shorterSignature` and `unusedInstance` treat Mathlib's `lemma` as the `theorem` its macro produces. In the Riemann project, 15,869 of 17,350 theorem declarations are written with `lemma`.

The `unusedHave` lint tries removing complete, uncommented lines that introduce a named local proof. A missing reference in the source nominates a candidate. Lean then re-elaborates the theorem, since tactics such as `assumption` can use a local fact without naming it. If removing several facts together fails, LeanPerf splits the group and checks smaller combinations. It accepts a proof only when its exported theorem type and universes match and the new proof contains no `sorry`.

The optimizer also indexes local equalities, iff statements, and order comparisons by their endpoints, including facts inside conjunctions. It searches chains of up to three local facts, tries symmetry and antisymmetry, and checks the resulting term. For example, with `h₁ : a ≤ b` and `h₂ : b ≤ c`, it can replace a proof of `a ≤ c` with `h₁.trans h₂`. Arithmetic replay also tests these terms against the original tactic's heartbeat count.

For generated theorem statements with explicit universe arguments or coercions, `--compress` tries Lean's mathematical notation and a spelling that omits explicit universe arguments. It re-elaborates the declaration and compares its exported type structurally, including binder names, implicit and instance arguments, and the ordered universe parameters. This preserves named-argument calls from other modules. Statements containing comments keep their original text.

On the 47 modules of `src/Lib/ClassField` in the Riemann project (1.5 MB of source, all dependencies built), `leanperf --compress --jobs 3` took 7.5 minutes. It proposed 490 edits in 42 files, each of which passed the whole-module check, and saved 25 KB: 473 `restatedType`, 8 `fasterTactic`, 4 `unneededClassical`, 3 `unneededErasure` and 2 `unusedHave` edits.

### Redundant proof steps

Five lints delete text that a proof step does not need. `restatedType` drops the type of `have h : T := e` or `obtain ⟨x, hx⟩ : T := e`, which becomes `have h := e`. A value written as a `by` block needs its type as the goal, so it is never a candidate. `redundantShow` deletes a `show T` line when the goal already has the form `T`, `unneededClassical` deletes a `classical` line when the rest of the proof needs no classical instance, and `unneededErasure` deletes `-f` from the arguments of `simp`, `simp_all` or `dsimp`. Lean's unused-argument linter checks the lemmas a `simp` call adds but not the ones it erases. When dropping every erasure changes the result, each one is tried alone. `redundantAscription` does for terms inside a step what `restatedType` does for a `have`: `exact (h x : P x)` becomes `exact h x`, and `fun (x : ℕ) ↦ …` becomes `fun x ↦ …`. An ascription is a candidate only when the info tree records that its position expected the type it states. Otherwise it converts a term, as `(n : ℝ)` does, or fixes the type of a numeral. Where `e` cannot stand alone, as an argument of a function, `(e : T)` becomes `(e)`.

Each candidate is replayed on every goal where the step ran, in the recorded metavariable context, next to the original step. When the two leave structurally equal goals, with the same hypothesis names and types, the rest of the proof runs in the same state and the edit is accepted. An inferred type often reaches a coercion or an operation through a different path of instances than the written one. The goals are then equal only up to unfolding instances, and a later tactic such as `rw` may notice. Such edits are accepted only after the whole theorem is elaborated with all its edits, and the group is split on failure as for `unusedHave`. On two Riemann modules, verifying these edits more than doubled the accepted deletions, from 14 to 32.

`shorterSimp` tries dropping the whole list from `simp`, `simp_all`, `simpa` and `dsimp`, then removes arguments from right to left, also trying without `only` when present. It leaves comments, locations and `using` clauses intact and proposes an edit only when replay leaves the same goals within its heartbeat budget and saves at least four UTF-8 bytes.

```lean
-- before
obtain ⟨Y, hY⟩ : ∃ Y : ℝ, ∀ y ≥ Y,
    |primeRemainder P.d P.q₀ y| ≤ 1 / log y ^ B ∧ |primeRemainder P.d 1 y| ≤ 1 / log y ^ B :=
  eventually_atTop.1 (…)
-- after
obtain ⟨Y, hY⟩ :=
  eventually_atTop.1 (…)
```

### Blocks that one tactic closes

The compact edition of the Riemann development proves the readable edition's lemmas in about half the bytes, and states fewer steps to do it. For the 4,771 lemmas that both editions contain under the same name, `calc` blocks fall from 547 to 2, `rw` calls from 3,168 to 570 and `refine` from 2,268 to 403, while `grind`, `aesop` and `bound` appear three to five times as often. `shorterBlock` looks for such steps. For every tactic sequence that proves a proposition, it tries a short closer on the goal where the sequence starts and on the goals where its last three steps start. The closers are `rfl`, `simp`, `ring`, `omega`, `positivity`, `linarith`, `norm_num`, `fun_prop`, `bound`, `simp_all`, `grind` and `aesop`, and `simp`, `simp_all` and `grind` given every rule that the replaced `rw` and `simp` calls name. When a step's goals are closed one bullet each, as after `constructor`, it also tries `step <;> closer`.

```lean
-- before
  calc valuationVia k A c = ∏ y : orbit Γ x, A y := by simp [valuationVia, hc]
    _ = A x ^ (stabilizer Γ x).index := by simp [h_val, index_stabilizer]
-- after
  simp [valuationVia, hc, h_val, index_stabilizer]
```

`unneededStep` deletes a step that the rest of its block does without: `have` facts that automation finds anyway, a `change` or `simp only` that a later `simp` repeats. Each step of a block of at most 24 steps is tried in turn, from the first, by replaying the block without it from the goal where the block starts, and a deletion is kept for the steps after it. On `LocalFields.lean` it deletes 4 steps, 400 bytes.

A closer that searches is often slower than the steps it finds. It must take out at least one step, and is accepted when it costs at most twice the replaced steps plus 100,000 raw heartbeats for each step it saves. Of the closers that work, the cheapest is kept. Blocks with comments, blocks of one step and proofs of data are skipped, and a closer for a whole block makes its inner blocks moot. The message gives the heartbeats of the steps and of the closer. Replaying the steps themselves is limited to twice the heartbeats that their declaration was allowed, since a replay can take a slower path than the elaboration did. Some unfolding counts no heartbeats at all, and in one Riemann module it ran for hours, so a module that takes a worker more than 30 minutes fails without edits (`LEANPERF_TIMEOUT`, in seconds; 0 for no limit).

### Rewrites that Claude makes most often

Of the 295 rewrites of Riemann modules that Claude proposed and Lean accepted, which save 34% of their bytes, 47% of the savings are comments and 13% whitespace. In the code, nearly half of the `have`s go, `by` falls by a fifth, and `.mp` and `.mpr` become `.1` and `.2`. `inlineHave` puts the proof of `have h : T := e` where the rest of its block names `h` once: `e` in place of `h` when that elaborates, else `(e : T)`. It leaves a `have` with binders or one whose value is a tactic block or spans lines with layout. `termExact` writes `e` for `by exact e` and `fun x y ↦ e` for `by intro x y` followed by `exact e`. `termCompile` turns structural tactic blocks into terms, including lambdas for `intro`, anonymous constructors for `constructor` with bullets, and filled-in terms for `refine`. It keeps short tactic proofs such as `by simp` for subgoals and proposes the result when it saves at least eight bytes. `shortProjection` writes `.1` and `.2` for `.mp` and `.mpr`. `obtainProjection` replaces a flat `obtain` or `rcases` destructuring of a local with projections at its uses. For example, after `obtain ⟨a, b, c⟩ := h`, it writes `h.1`, `h.2.1` and `h.2.2` for the three parts. `simpaUsing` replaces `simp at h` and a final `exact h` with `simpa using h`, keeping any simp arguments. `rwaAt` replaces `rw [L] at h` and a final `exact h` with `rwa [L] at h`. `mergeRw` combines consecutive `rw` steps on their own lines at the same location when the merged line fits in 100 columns. `sharedHaveBinders` drops the explicit binders of a `have` that the theorem binds with the same name and type, together with the arguments its uses pass for them. `haveToRefine` turns `have h : T := by tacs` used only in a final `exact e` into `refine e` with `?_` in place of `h`, or `(?_ : T)` when the hole needs its type, followed by `tacs`. These rewrites are checked by elaborating the theorem with each edit, with the `shortProjection` edits of a theorem checked together. None of them deletes a comment.

On `LocalFields.lean` in the Riemann project, which is already golfed by thousands of mechanical pull requests, these find little: one `have` and 21 projections. `--layout --rules stripComments`, then `--compress`, then `--layout` take it from 42,671 to 34,306 bytes (−20%) and 691 to 584 lines, without a model. With Claude as a proposer the same module reaches −38%.

### Shorter local names

`shortNames` renames the locals a proof binds by name, from `intro`, `obtain`, `have`, `fun` and the like, to the shortest names that no identifier of the theorem uses, keeping the first letter where it can: `h_unif` becomes `h` or `h'`. The binders are those the info tree records, so a name that only resembles a local is left alone, and so are the statement's binders, which are part of its type, and the parameter names of named arguments such as `(h := e)`. Every use of a renamed local changes with it, so the renaming waits until no other lint changes the theorem, and Lean checks all of a theorem's renamings together, then halves of them when they fail. In Claude's accepted rewrites, local names fall from 4.3 to 2.9 characters on average; on `LocalFields.lean` this lint saves 2.5% of the bytes.

### Folding helper lemmas

Most of what separates the readable and compact editions of the Riemann development is declarations: 57% of the readable edition's theorem lines are in lemmas used only in their own file. `foldHelper` folds a theorem that only one other declaration of its module uses, directly or through other such helpers, and that no other module mentions, into that declaration. Each helper becomes a `have` at the start of the theorem's proof, with its binders, statement and proof copied and re-indented, and its uses name the `have`, including uses by dot notation such as `h.helper x`, which become `nm x h` with `h` at the helper's receiver argument. Implicit and instance binders that the theorem already binds the same way are dropped, so the `have` uses the theorem's variables, and `Type*` becomes `Type _`, since a `have` cannot be universe polymorphic. Lean then elaborates every command from the first helper to the theorem: the theorems that stay must keep their statements and docstrings, nothing new may be declared, and the span may take at most twice its heartbeats. When a group fails, each helper is tried alone. A docstring that mentions a folded helper keeps the mention.

### Iterating

`leanperf --golf MODULE_OR_DIR…` (or `scripts/golf`) runs every pass that shrinks proofs, in the order that lets each feed the next. `--unused` deletes the theorems that nothing in the project mentions, so that no later pass works on them, and more helpers are left with one user to fold into. `--dedup` then proves each theorem that restates another by citing it. Rounds of `--unused` and `--compress` follow until a round changes nothing, and `--tactics` makes the remaining steps cheaper last. Every edit is elaborated before it is written. Run it from the project's root, on a clean working tree, and review the diff. `--cosmetic` adds the byte-only lints and `--layout` to each round, and `--strip-comments` first deletes the comments inside declarations. `--keep-unused` keeps the theorems that nothing uses, as for a library whose users are elsewhere, and `--no-optimize` skips `--tactics`.

The numbers below were measured before compression counted steps, when it counted bytes and ran the byte-only lints, with comments stripped. On `LocalFields.lean` it took 42,671 bytes to 29,648 (−30.5%), against 26,250 for the pipeline with Claude as proposer; most of the remaining difference is two helpers that Claude folds and Lean rejects as `have`s, and a theorem that Claude merges into the wrapper that restates it. On three other `ClassField` modules it did as well as one pass of Claude's on one of them, and less well on the other two:

| Module | Before | After | `scripts/golf` | Claude, one pass |
|---|---:|---:|---:|---:|
| `Global/CMSplittingCharacters` | 55,185 | 42,079 | −23.7% | −28% |
| `GreenbergWiles/SplitPrimeReciprocity` | 61,072 | 50,715 | −17.0% | −15% |
| `HeckeCharacter/Basic` | 44,741 | 37,724 | −15.7% | −22% |

### Unused instance arguments

`unusedInstance` deletes an anonymous instance binder such as `[Fact p.Prime]` from a theorem's signature when neither its statement nor its proof uses it. Instance arguments are synthesized at every use, so no caller changes. LeanPerf first reads the elaborated type and proof term, and elaborates the theorem again only if one of its instance binders is unused in both. It accepts a deletion when the new exported type is the old one without instance binders that nothing after them mentions. A binder that the statement uses, such as `[DecidablePred p]` in a statement about `Finset.filter p s`, is kept even when another instance could take its place. A theorem with attributes, a named binder, or a theorem that some project module applies with `@` keeps its arguments.

## Unused theorems

`leanperf --unused src/` deletes theorems that nothing else in the project mentions. It reads source text only, so it needs nothing built and runs no Lean. Run it from the project's root, since it reads every module under the `srcDir` in `lakefile.toml`.

A theorem counts as used when a used command, or a comment in it, mentions it by a name Lean would resolve there: the full name, or the name relative to an enclosing namespace, an opened namespace, or the namespace of the declaration being made, as in the body of `theorem A.foo`. So `B.foo` is unused even when `A.foo` is used. A mention that names no declaration of the project, such as `h.foo` for a local `h`, could be field notation, so it uses every theorem whose last name component is `foo`. The analysis starts from every command that is not a theorem, every theorem with an attribute (which tactics or generated names can use without spelling it), every theorem in a module that no other project module imports, and text outside commands, such as module documentation. A theorem that none of these reach, directly or through other theorems, is unused. Its deletion includes its doc comment and any `set_option … in`, `omit … in` or attribute lines in front of it.

```sh
leanperf --unused src/                     # preview
leanperf --unused --check --apply src/     # elaborate each rewritten file, then write all of them
```

A theorem is deleted only together with every unused theorem that mentions it, so analyzing some of the files never breaks another one. For the same reason the files are written together: if any check fails, nothing is written. `--check` elaborates each rewritten file against the built dependencies. On the Riemann project the pass reads 801 modules in under 7 seconds and finds 6 unused theorems, each mentioned only by its own declaration. The rewritten files elaborate.

## Joining lines

`leanperf --layout src/` joins a line to the one before it when the joined line fits in 100 columns and the command still parses to the same syntax tree. The tree is what Lean elaborates, so the command means the same, and no proof is elaborated: the pass runs the commands that set up notation and scopes and only parses declarations. It joins signatures that wrap early, terms that continue on the next line, and a single tactic on the line after its `by`. It never joins lines with comments or blank lines, nor two tactic steps, since that needs a `;`, which changes the tree. A line that opens an indented continuation stays at its head.

```lean
-- before
lemma dvd_iff_valuationVia_le {x y : valRingBelow k A} :
    x ∣ y ↔ valuationVia k A y ≤ valuationVia k A x :=
  (integer.integers _).dvd_iff_le
-- after
lemma dvd_iff_valuationVia_le {x y : valRingBelow k A} :
    x ∣ y ↔ valuationVia k A y ≤ valuationVia k A x := (integer.integers _).dvd_iff_le
```

With `--rules stripComments,joinLines`, the pass also deletes the comments inside each declaration, including one after its last token, but not its docstring, string literals or the comments between declarations. A comment alone on its line goes with the line, and the step after a bullet whose comment pushed it down moves up to the bullet. The command must still parse to the same tree. Comments are a choice about the source, so this lint runs only when named. On `LocalFields.lean` it removes 13% of the bytes and 10% of the lines; a second `--layout` then joins lines that the comments kept apart.

Lines account for much of the difference between the two editions of the Riemann development: the lemmas they share take 74,280 lines in the readable edition and 33,186 in the compact one, but 4.8 and 2.6 million characters. Run `--layout` after `--compress --apply`, since a compression edit can leave a block short enough to join.

## Proposed rewrites

The lints above each try one kind of edit. On a development that people have already shortened, together they save a few percent: proofs there are almost all different from each other, and a decision procedure given the premises of a proof rarely finds another one. The compact edition of the Riemann development is four times smaller than the readable one because its proofs were written again, with other arguments and fewer steps. That is search that no fixed rule does, but checking its result is what LeanPerf does anyway.

`leanperf --propose CMD src/` separates the two. For each theorem of at least 160 bytes it runs the shell command `CMD`, writes a JSON request to its standard input, and reads `{"candidates": ["…", …]}` from its standard output. The request holds the declaration without its docstring, the source above it, and the theorems its proof uses. Each candidate is elaborated in place of the declaration, from the state before it. It is accepted when the statement and universe parameters are unchanged, it declares no new names, no proof has `sorry`, no proof uses an axiom that the original does not, apart from Lean's three standard ones, and it elaborates at most twice as slowly as the original plus 2,000 heartbeats. The shortest accepted candidate replaces the declaration. When none is accepted, `CMD` is asked again, up to three times, with every candidate and Lean's errors for it. The rewritten module is then checked as a whole.

Only what the rest of the project sees needs to stay. In the Riemann project, 57% of the lines of theorems are in theorems that only their own module uses, and 57% of the readable lemmas that the compact edition no longer has were used by exactly one other declaration. So a theorem is sent together with the theorems right above it that only it uses and that no other module mentions, up to six commands and 8 KB. The request lists them under `free`: a candidate may delete them, fold their proofs into the theorem, or keep them, as long as the theorem keeps its statement.

`scripts/propose-claude` is such a proposer. It asks Claude through the `claude` command line, with no tools, for up to three shorter versions. `LEANPERF_PROPOSE_MODEL` selects the model (`sonnet` by default). Each request costs a model call, so try it on a few modules first. The first rounds of a module's requests run `LEANPERF_PROPOSE_JOBS` at a time (4 by default), since a model call takes far longer than checking its answer. On 13 theorems of `src/Lib/ClassField/Places/LocalFields.lean` in the Riemann project, Claude Sonnet proposed a rewrite that Lean accepted for each, 12 of them in the first round, and the 16 KB of declarations shrank by 36%, docstrings kept. Sent in groups, 10 requests were all accepted in the first round, and the 17 KB they held shrank by 38%. Two of them held a theorem and a helper lemma that only it used, and both helpers were folded in and deleted. Each rewritten module elaborates.

```sh
leanperf --propose scripts/propose-claude src/Lib/ClassField/Places/LocalFields.lean            # preview
leanperf --propose scripts/propose-claude --apply src/Lib/ClassField/Places/LocalFields.lean    # write
```

With `LEANPERF_PROPOSE_LOG=FILE`, each accepted rewrite is appended to `FILE` as a JSON line with the original text and the rewrite: verified examples for training a proposer.

### A proposer of one's own

`scripts/propose-local` asks a local model behind an OpenAI-compatible chat endpoint, such as `mlx_lm.server`, for several proofs of each declaration's statement at once, so that the server can batch them. It keeps only answers that are shorter than the old proof and that the model finished. With `LEANPERF_PROPOSE_CONTEXT=1` the prompt also gives the statements of the declarations above it in the file that share the most names with it, so that the model can use lemmas that exist. `scripts/ml` builds the data to fine-tune one:

```sh
python3 scripts/ml/mine.py PATH/TO/mathlib4 mathlib.jsonl mathlib       # theorems whose statement stayed and whose text shrank
python3 scripts/ml/mine.py PATH/TO/project project.jsonl rh
python3 scripts/ml/contexts.py PATH/TO/mathlib4 mathlib.jsonl mathlib-ctx.jsonl   # the related statements, from the file before the change
python3 scripts/ml/contexts.py --tree PATH/TO/project accepted.jsonl accepted-ctx.jsonl
python3 scripts/ml/build.py HELD/OUT/Module.lean mathlib-ctx.jsonl project-ctx.jsonl accepted-ctx.jsonl
```

`mine.py` walks a repository's history and keeps every theorem whose statement is unchanged and whose text got shorter. In Mathlib's 36,537 commits there are 45,683 such pairs, though most change little. `contexts.py` adds the related statements a model sees beside each declaration, read from the file as it was before the change, with the same code (`context.py`) that `propose-local` uses. `build.py` keeps pairs that save at least 15% or 40 bytes and are not only renames, ranks Mathlib's by how much they shrink, adds accepted rewrites from `LEANPERF_PROPOSE_LOG`, and writes chat examples for `mlx_lm lora` whose answer is the new proof. Each accepted rewrite of a local model can be added to the next round's data, since Lean has checked it.

A proposer's output is never trusted. Nothing it writes reaches the file unless Lean accepts the declaration with the original statement.

### Contracting steps

`contractPair`, a `--compress` lint, replaces two adjacent one-line steps of a tactic sequence with one. The candidates come from fixed rules: the rules of two `rw` or `simp` steps at one location in one call, two `intro`s as one, `intro` then `exact` as `exact fun`, and `apply f` then `exact e` as `exact f e`. More come from a proposer: by default `scripts/pair-dict` of LeanPerf's checkout, described below, or the command that `LEANPERF_PAIR_MODEL` names, or none when it is empty. A proposer reads `{statement, previous, goal, first, second}` as JSON, where `goal` is the goal before the two steps as the infoview prints it, and writes `{"candidates": [...]}`. A candidate must have fewer steps than the pair and fit on its line within 100 columns. It is kept when the sequence with it in place of the pair still closes every goal it closed, within twice the steps' heartbeats plus 100,000 for each step saved; of those, the cheapest. While the steps before the pair are unchanged, each candidate is first run from the goal recorded before the pair, with only the steps after it, and most fail there. Any proof will do, so the goals between steps may change. After a contraction the pair before it is tried again, so a run of steps can shrink to one step. `LEANPERF_PAIR_LOG` names a JSON-lines file where each accepted contraction is appended, with its goal, as training data for the model that proposes them.

```lean
-- before
  have k : ∏ w : InfinitePlace L, Φ w a.val < 0 := by simp_all
  simpa [g] using lt_asymm k
-- after
  simpa [g] using lt_asymm (by simp_all)
```

`scripts/pair-local` asks a step-contraction model behind an OpenAI-compatible endpoint (port 8090 by default) for six answers. It drops answers that only join the two steps with `<;>` or `;`. `scripts/pair-table` answers from proposals made beforehand, such as those of `scripts/ml/pair-batch.py`, which asks Codex about 40 pairs per call (`scripts/ml/pairdump.py` lists them). `scripts/ml/pairs21.py` mines contractions of two to five steps into one from a repository's history, and `scripts/ml/build21.py` writes the chat examples, adding accepted ones from `LEANPERF_PAIR_LOG`. Kimina-Prover-Distill-1.7B, fine-tuned with LoRA on 1,923 contractions, mostly from Mathlib, found 4 contractions on the four modules that `scripts/golf` had already shrunk (the example above is one): 106 bytes, all of kinds that no fixed rule makes.

`scripts/pair-dict` proposes without a model, from a dictionary of templates (`data/contractions.jsonl`, or `LEANPERF_PAIR_DICT`) that `scripts/ml/templates.py` learns from checked contractions, the way a dictionary coder learns its phrases. Each example is generalized by anti-unification. The longest balanced spans that the merged step copies from the two steps become holes, which must match the same text wherever they recur. The rest of the steps' terms become wildcards, and tactic names and keywords stay literal. A template's support is the number of examples it reproduces. The dictionary tries templates best supported first, and skips a template seen once that writes a name the steps do not show. When a server answers at `LEANPERF_PAIR_URL`, the candidates of `scripts/pair-local` follow the dictionary's; `LEANPERF_PAIR_NEXT` names another command instead, or none when it is empty. The dictionary that comes with LeanPerf was learned from 1,583 contractions of two steps: 1,254 mined from repository history, mostly Mathlib's, and 329 that Lean accepted in Riemann modules from Codex's proposals, the model's, and the dictionary's own. It has 1,222 templates, 162 of them supported by two or more examples, such as:

```
rw $0 / exact $_                  ->  rwa $0                 (16 examples)
by_contra! $_ / obtain $0 := $_   ->  by_contra! $0          (14)
dsimp only [$0] / rw [$1]         ->  simp only [$0, $1]     (13)
rw $_ / exact $0                  ->  simpa using $0         (10)
ext $0 / intro $1                 ->  ext $0 $1              (9)
have := $0 / positivity           ->  positivity [$0]        (8)
```

It proposes for 40% of the Riemann project's adjacent steps, about 2 ms per pair. Every contraction that Lean accepts can go back into the dictionary and the model's data, so both grow as they are used.

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

The `permuted dependent statements` test generates 24 versions of a theorem with premises `E a b`, `E b c` and `E c d`. It permutes the four data binders and varies the premise order. LeanPerf recognizes all 23 restatements, checks their rewritten proofs, and keeps a theorem with the same binder counts and a different dependency graph. This measures a known family of duplicates. Discovery rates in an arbitrary library depend on which theorems and imports are present.

On 11 unmodified modules from the Riemann project, the elaborated search found zero replacements, with a median cold scan of 12.50 seconds across three runs. Tactic replay had more impact on compilation time in a separate two-module trial on the same revision. Across five alternating Lake checks per version, `GapNum` went from 6.17 to 3.05 seconds and `LargeConstantLeParamCube` from 3.70 to 2.91 seconds on the benchmark machine. These are per-module timings. [Riemann benchmark revision](https://github.com/leanprover-community/riemann-hypothesis/tree/320abbbfc6634dc7b5e9961f940cd7821d37c9e1)
