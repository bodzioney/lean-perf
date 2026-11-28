namespace LeanPerf.Lints

structure Lint where
  name : String
  group : String
  description : String
  token : String := ""

def catalog : List Lint := [
  ⟨"splitObtain", "syntax", "Bind the application before destructuring it", "obtain"⟩,
  ⟨"exactUsing", "syntax", "Use the hypothesis whose type matches the goal", "simpa"⟩,
  ⟨"simpRfl", "syntax", "Use reflexivity for this equality", "simp"⟩,
  ⟨"rflTerm", "syntax", "Use the reflexivity proof term directly", "rfl"⟩,
  ⟨"syntacticDuplicate", "dedup", "Find source-level restatements without building imports", ""⟩,
  ⟨"duplicate", "dedup", "Find equal canonical theorem types", ""⟩,
  ⟨"specialCase", "dedup", "Prove a statement by specializing another theorem", ""⟩,
  ⟨"fasterTactic", "tactics", "Replay alternatives and compare elaboration heartbeats", ""⟩,
  ⟨"unneededOption", "tactics", "Remove scoped option overrides after re-elaboration", ""⟩,
  ⟨"unneededSeal", "tactics", "Remove `seal … in` when the command elaborates as cheaply without it", ""⟩,
  ⟨"reuseProof", "compress", "Replace a proof with a shorter local or library term", ""⟩,
  ⟨"reprove", "compress", "Search for a shorter derivation from the original premises and local hypotheses", ""⟩,
  ⟨"shorterSignature", "compress", "Shorten a theorem statement with the same exported type", ""⟩,
  ⟨"unusedHave", "compress", "Remove local proofs the remaining theorem can do without", ""⟩,
  ⟨"restatedType", "compress", "Drop a `have` or `obtain` type that Lean infers from the value", ""⟩,
  ⟨"redundantAscription", "compress", "Drop `(e : T)` or a `fun` binder type that restates the expected type", ""⟩,
  ⟨"redundantShow", "compress", "Delete a `show` that leaves the goal unchanged", ""⟩,
  ⟨"unneededClassical", "compress", "Delete a `classical` the proof does not need", ""⟩,
  ⟨"unneededErasure", "compress", "Delete `-f` from a `simp` that gives the same result without it", ""⟩,
  ⟨"shorterSimp", "compress", "Shorten a simplifier argument list while leaving the same goals", ""⟩,
  ⟨"contractPair", "compress", "Replace two adjacent steps with one that leaves a proof the rest of the block finishes", ""⟩,
  ⟨"unneededStep", "compress", "Delete a tactic step that the rest of its block does without", ""⟩,
  ⟨"inlineHave", "compress", "Use a local proof where it is needed when the rest of its block names it once", "have"⟩,
  ⟨"obtainProjection", "compress", "Use projections of a local in place of a flat `obtain` or `rcases` pattern", ""⟩,
  ⟨"sharedHaveBinders", "compress", "Drop the binders of a `have` that the theorem binds the same way, with the arguments its uses pass", "have"⟩,
  ⟨"haveToRefine", "compress", "Prove a `have` that only the last `exact` uses as a hole of that step, `refine e ?_`", "have"⟩,
  ⟨"termExact", "compress", "Write the term for `by exact e`, and `fun x ↦ e` for `by intro x; exact e`", "exact"⟩,
  ⟨"termCompile", "compress", "Write structural tactic blocks as terms with short tactic proofs for subgoals", "by"⟩,
  ⟨"simpaUsing", "compress", "Replace `simp at h` followed by a final `exact h` with `simpa using h`", "simp"⟩,
  ⟨"rwaAt", "compress", "Replace `rw [L] at h` followed by a final `exact h` with `rwa [L] at h`", "rw"⟩,
  ⟨"mergeRw", "compress", "Merge consecutive `rw` steps at the same location when they fit on one line", "rw"⟩,
  ⟨"shortProjection", "compress", "Write `.1` and `.2` for `.mp` and `.mpr`", ""⟩,
  ⟨"shortNames", "compress", "Give the locals a proof binds the shortest free names", ""⟩,
  ⟨"foldHelper", "compress", "Fold a lemma that one theorem of the module uses, and no other module, into that theorem", ""⟩,
  ⟨"shorterBlock", "compress", "Close a proof block, or its last steps, with one shorter tactic", ""⟩,
  ⟨"unusedInstance", "compress", "Delete an instance argument that neither the statement nor the proof uses", ""⟩,
  ⟨"unusedTheorem", "unused", "Delete a theorem that nothing else in the project mentions", ""⟩,
  ⟨"rewrite", "propose", "Replace a theorem with a shorter one that a proposer suggests and Lean accepts", ""⟩,
  ⟨"joinLines", "layout", "Join a line to the one above when the command parses to the same syntax", ""⟩,
  ⟨"stripComments", "layout", "Delete the comments inside a declaration (only with `--rules`)", ""⟩]

/-- Lints that run only when `--rules` names them: deleting comments is a choice about the source,
    not a fix. -/
def optIn : List String := ["stripComments"]

/-- Compression lints that only save bytes: they leave the steps and declarations of a proof as
    they are. `--compress` runs them only with `--cosmetic` or when `--rules` names them. -/
def cosmetic : List String :=
  ["restatedType", "redundantAscription", "unneededErasure", "shorterSimp", "shortProjection", "shortNames",
   "sharedHaveBinders", "shorterSignature", "unusedInstance"]

/-- The compression lints that replay one proof step. -/
def redundant : List String :=
  ["restatedType", "redundantShow", "unneededClassical", "unneededErasure", "redundantAscription"]

def names (group : String) : List String := (catalog.filter (·.group == group)).map (·.name)

end LeanPerf.Lints
