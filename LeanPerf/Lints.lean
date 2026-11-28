namespace LeanPerf.Lints

/-- Where a lint belongs in the shrinking pipeline: `cut` deletes what is not needed, `compress`
    writes what remains in fewer steps and declarations, `optimize` makes it cheaper to elaborate,
    and `layout` arranges the source. -/
inductive Stage where
  | cut | compress | optimize | layout | none
  deriving BEq, Repr, Inhabited

structure Lint where
  name : String
  /-- The mode that offers it: `syntax`, `dedup`, `tactics`, `compress`, `unused`, `layout`, `propose`. -/
  group : String
  description : String
  token : String := ""
  stage : Stage := .none
  /-- It only saves bytes, leaving the steps and declarations as they are: `--compress` runs it with
      `--cosmetic` or when `--rules` names it. -/
  cosmetic : Bool := false
  /-- It runs only when `--rules` names it: deleting comments is a choice about the source. -/
  optIn : Bool := false
  /-- Its edits rest on replaying one step, so the command is also elaborated with them. -/
  replayed : Bool := false
  /-- Its rewrite can keep as many steps as before; one that takes none out is dropped. -/
  mustRemoveSteps : Bool := false
  /-- It reads the command's info trees, which elaboration then records. -/
  info : Bool := false

def catalog : List Lint := [
  { name := "splitObtain", group := "syntax", description := "Bind the application before destructuring it", token := "obtain" },
  { name := "exactUsing", group := "syntax", description := "Use the hypothesis whose type matches the goal", token := "simpa" },
  { name := "simpRfl", group := "syntax", description := "Use reflexivity for this equality", token := "simp" },
  { name := "rflTerm", group := "syntax", description := "Use the reflexivity proof term directly", token := "rfl" },
  { name := "syntacticDuplicate", group := "dedup", description := "Find source-level restatements without building imports", stage := .cut },
  { name := "duplicate", group := "dedup", description := "Find equal canonical theorem types", stage := .cut },
  { name := "specialCase", group := "dedup", description := "Prove a statement by specializing another theorem", stage := .cut },
  { name := "fasterTactic", group := "tactics", description := "Replay alternatives and compare elaboration heartbeats", stage := .optimize, replayed := true, info := true },
  { name := "unneededOption", group := "tactics", description := "Remove scoped option overrides after re-elaboration", stage := .cut },
  { name := "unneededSeal", group := "tactics", description := "Remove `seal … in` when the command elaborates as cheaply without it", stage := .cut },
  { name := "reuseProof", group := "compress", description := "Replace a proof with a shorter local or library term", stage := .compress, replayed := true, mustRemoveSteps := true, info := true },
  { name := "reprove", group := "compress", description := "Search for a shorter derivation from the original premises and local hypotheses", stage := .compress, mustRemoveSteps := true, info := true },
  { name := "shorterSignature", group := "compress", description := "Shorten a theorem statement with the same exported type", stage := .compress, cosmetic := true, info := true },
  { name := "unusedHave", group := "compress", description := "Remove local proofs the remaining theorem can do without", stage := .cut },
  { name := "restatedType", group := "compress", description := "Drop a `have` or `obtain` type that Lean infers from the value", stage := .cut, cosmetic := true, replayed := true, info := true },
  { name := "redundantAscription", group := "compress", description := "Drop `(e : T)` or a `fun` binder type that restates the expected type", stage := .cut, cosmetic := true, replayed := true, info := true },
  { name := "redundantShow", group := "compress", description := "Delete a `show` that leaves the goal unchanged", stage := .cut, replayed := true, info := true },
  { name := "unneededClassical", group := "compress", description := "Delete a `classical` the proof does not need", stage := .cut, replayed := true, info := true },
  { name := "unneededErasure", group := "compress", description := "Delete `-f` from a `simp` that gives the same result without it", stage := .cut, cosmetic := true, replayed := true, info := true },
  { name := "shorterSimp", group := "compress", description := "Shorten a simplifier argument list while leaving the same goals", stage := .cut, cosmetic := true, replayed := true, info := true },
  { name := "contractPair", group := "compress", description := "Replace two adjacent steps with one that leaves a proof the rest of the block finishes", stage := .compress, replayed := true, info := true },
  { name := "unneededStep", group := "compress", description := "Delete a tactic step that the rest of its block does without", stage := .cut, replayed := true, info := true },
  { name := "inlineHave", group := "compress", description := "Use a local proof where it is needed when the rest of its block names it once", token := "have", stage := .compress },
  { name := "obtainProjection", group := "compress", description := "Use projections of a local in place of a flat `obtain` or `rcases` pattern", stage := .compress, info := true },
  { name := "sharedHaveBinders", group := "compress", description := "Drop the binders of a `have` that the theorem binds the same way, with the arguments its uses pass", token := "have", stage := .compress, cosmetic := true },
  { name := "haveToRefine", group := "compress", description := "Prove a `have` that only the last `exact` uses as a hole of that step, `refine e ?_`", token := "have", stage := .compress },
  { name := "termExact", group := "compress", description := "Write the term for `by exact e`, and `fun x ↦ e` for `by intro x; exact e`", token := "exact", stage := .compress },
  { name := "termCompile", group := "compress", description := "Write structural tactic blocks as terms with short tactic proofs for subgoals", token := "by", stage := .compress, mustRemoveSteps := true },
  { name := "simpaUsing", group := "compress", description := "Replace `simp at h` followed by a final `exact h` with `simpa using h`", token := "simp", stage := .compress },
  { name := "rwaAt", group := "compress", description := "Replace `rw [L] at h` followed by a final `exact h` with `rwa [L] at h`", token := "rw", stage := .compress },
  { name := "mergeRw", group := "compress", description := "Merge consecutive `rw` steps at the same location when they fit on one line", token := "rw", stage := .compress },
  { name := "shortProjection", group := "compress", description := "Write `.1` and `.2` for `.mp` and `.mpr`", stage := .compress, cosmetic := true },
  { name := "shortNames", group := "compress", description := "Give the locals a proof binds the shortest free names", stage := .compress, cosmetic := true, info := true },
  { name := "foldHelper", group := "compress", description := "Fold a lemma that one theorem of the module uses, and no other module, into that theorem", stage := .compress },
  { name := "shorterBlock", group := "compress", description := "Close a proof block, or its last steps, with one shorter tactic", stage := .compress, replayed := true, info := true },
  { name := "unusedInstance", group := "compress", description := "Delete an instance argument that neither the statement nor the proof uses", stage := .cut, cosmetic := true },
  { name := "unusedTheorem", group := "unused", description := "Delete a theorem that nothing else in the project mentions", stage := .cut },
  { name := "rewrite", group := "propose", description := "Replace a theorem with a shorter one that a proposer suggests and Lean accepts", stage := .compress },
  { name := "joinLines", group := "layout", description := "Join a line to the one above when the command parses to the same syntax", stage := .layout },
  { name := "stripComments", group := "layout", description := "Delete the comments inside a declaration (only with `--rules`)", stage := .layout, optIn := true }]

def find? (name : String) : Option Lint := catalog.find? (·.name == name)

def optIn : List String := (catalog.filter (·.optIn)).map (·.name)

def cosmetic : List String := (catalog.filter (·.cosmetic)).map (·.name)

def replayed : List String := (catalog.filter (·.replayed)).map (·.name)

def mustRemoveSteps : List String := (catalog.filter (·.mustRemoveSteps)).map (·.name)

def names (group : String) : List String := (catalog.filter (·.group == group)).map (·.name)

end LeanPerf.Lints
