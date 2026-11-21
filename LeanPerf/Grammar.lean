import Lean

/-! Parser declarations for common Mathlib notation in proof signatures. These have no
elaborators. The standalone parser uses only this grammar and its toolchain imports. -/
namespace LeanPerf.Grammar

syntax:max "⊤" : term
syntax:max "⊥" : term
syntax:max "Type*" : term
syntax:25 term:26 " →₀ " term:25 : term

syntax:25 term:26 " →* " term:25 : term
syntax:max "ℤ_[" term "]" : term
syntax "{" ident " | " term "}" : term

open Lean.Parser.Command in
syntax (name := lemmaDecl) declModifiers "lemma " declId declSig declVal : command

end LeanPerf.Grammar
