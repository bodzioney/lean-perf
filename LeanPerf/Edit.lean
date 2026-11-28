import Lean

/-!
# Edits and what a lint sees

Every lint proposes `Edit`s: a byte range of the module and the text that replaces it. A lint that
works on one command at a time gets that command as `Elaborated`: its syntax, the states before
and after it, its info trees and what it cost to elaborate.
-/

open Lean Elab

namespace LeanPerf

/-- Whether `LEANPERF_DEBUG`, a comma-separated list such as `golf,fold,pair`, names `topic`: the
    lints of that topic then say on standard error what they try and why they give up. -/
def debugging (topic : String) : IO Bool := do
  return ((← IO.getEnv "LEANPERF_DEBUG").getD "").splitOn "," |>.contains topic

/-- A replacement of source text that a lint proposes. -/
structure Edit where
  rule : String
  message : String
  range : Syntax.Range
  newText : String
  /-- The steps the edit takes out of its command, or 1000 for each declaration it removes
      (`Steps.worth`). -/
  gain : Nat := 0
  deriving Inhabited

/-- The most valuable set of pairwise disjoint intervals among `order`, which lists them by where they
    end: interval `i` is `[start i, stop i)` and is worth `worth i`. Weighted interval scheduling. An
    interval is taken only when it adds value, so of two equal choices the one listed first wins.
    Returns the chosen intervals in the order of `order`. -/
def bestDisjoint (order : Array Nat) (start stop : Nat → Nat) (worth : Nat → Int) : Array Nat := Id.run do
  let order := order.filter (worth · > 0)
  let mut best : Array Int := #[0]
  let mut prev : Array Nat := #[]
  for h : k in [:order.size] do
    let i := order[k]
    -- The intervals listed before `i` that end by its start.
    let mut lo := 0
    let mut hi := k
    while lo < hi do
      let mid := (lo + hi) / 2
      if stop order[mid]! ≤ start i then lo := mid + 1 else hi := mid
    prev := prev.push lo
    best := best.push (max best[k]! (best[lo]! + worth i))
  let mut out := #[]
  let mut k := order.size
  while k > 0 do
    if best[k]! > best[k-1]! then
      out := out.push order[k-1]!
      k := prev[k-1]!
    else k := k - 1
  return out.reverse

/-- One command of the module, elaborated without errors. -/
structure Elaborated where
  input : String
  map : FileMap
  fileName : String
  cmd : Syntax
  pctx : Parser.ParserModuleContext
  ctx : Command.Context
  before : Command.State
  after : Command.State
  /-- The command's info trees, read in the environment before it, so that a replayed `simp`
      cannot use the lemma the command declares. -/
  trees : Array InfoTree
  /-- Raw heartbeats the command took to elaborate. -/
  spent : Nat

end LeanPerf
