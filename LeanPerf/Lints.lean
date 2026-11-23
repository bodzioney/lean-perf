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
  ⟨"reuseProof", "compress", "Replace a proof with a shorter local or library term", ""⟩,
  ⟨"shorterSignature", "compress", "Shorten a theorem statement with the same exported type", ""⟩,
  ⟨"unusedHave", "compress", "Remove local proofs the remaining theorem can do without", ""⟩]

def names (group : String) : List String := (catalog.filter (·.group == group)).map (·.name)

end LeanPerf.Lints
