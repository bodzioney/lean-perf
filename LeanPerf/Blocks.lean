import LeanPerf.Edit
import LeanPerf.Replay
import LeanPerf.Steps
import LeanPerf.Prune

/-!
# Tactic blocks that one closer finishes

The compact edition of the Riemann development proves the lemmas of the readable one in about half
the bytes. Much of the difference is that it states fewer steps: a `have` proved by four rewrites
and a `simp` there is `by grind` here, and a `calc` chain is one `bound`. This pass finds such
blocks. For every tactic sequence that ends a proof of a proposition, it tries a few closers on the
goal where the whole sequence starts, and on the goals where its last few steps start. A closer is
kept when it closes every goal that the steps closed, at most twice as slowly as the steps plus a
fixed number of heartbeats for each byte it saves.

Closers come in two kinds: automation such as `simp`, `grind` or `bound`, and `simp`, `simp_all` or
`grind` given the rewrite and simplification rules that the replaced steps name.
-/

open Lean Elab Meta

namespace LeanPerf.Blocks

/-- Automation tried on every site, cheapest first. -/
def closers : Array String :=
  #["rfl", "simp", "ring", "omega", "positivity", "linarith", "norm_num", "fun_prop", "bound",
    "simp_all", "grind", "aesop"]

/-- The rules that the `rw` and `simp` calls in `stx` name, as written. -/
partial def rules (input : String) (stx : Syntax) : Array String :=
  go stx #[]
where
  go (s : Syntax) (acc : Array String) : Array String :=
    if s.isOfKind ``Parser.Tactic.rwRule || s.isOfKind ``Parser.Tactic.simpLemma then
      match s.getRange? (canonicalOnly := true) with
      | some r =>
        let t := (String.Pos.Raw.extract input r.start r.stop).trimAscii.toString
        if acc.contains t then acc else acc.push t
      | none => acc
    else s.getArgs.foldl (fun acc a => go a acc) acc


/-- Constants that every elaborated proof uses as glue, which no tactic needs to be told. -/
private def glue (n : Name) : Bool :=
  let s := n.toString
  [`Eq.mpr, `Eq.mp, `Eq.symm, `Eq.trans, `Eq.refl, `Eq.subst, `congrArg, `congrFun, `congr, `id,
   `of_eq_true, `eq_true, `eq_self, `eq_false, `rfl, `Iff.mpr, `Iff.mp, `Iff.intro, `Iff.refl,
   `propext, `funext, `True.intro, `trivial, `And.intro, `Exists.intro, `absurd, `False.elim,
   `Classical.byContradiction, `Classical.em, `Decidable.byContradiction, `cast, `HEq.refl,
   `eq_of_heq, `ne_eq, `not_false_eq_true, `implies_true, `forall_const, `and_self, `and_true,
   `true_and, `iff_self, `Or.inl, `Or.inr, `Not.intro, `id_eq].contains n ||
  s.startsWith "Lean." || s.startsWith "Std." || s.startsWith "Classical." ||
  s.startsWith "Decidable." || s.startsWith "inst"

/-- The theorems that a proof term uses, by the shortest names that resolve where it was
    written, in order of first use. -/
def premises (proof : Expr) : MetaM (Array String) := do
  let env ← getEnv
  let mut out := #[]
  for n in proof.getUsedConstants do
    if Replay.generated n || n.isInternalDetail || isPrivateName n || glue n then continue
    let some c := env.find? n | continue
    -- A theorem imported from a module can be an axiom here, its proof left out.
    unless c matches .thmInfo _ | .axiomInfo _ do continue
    if (← isInstance n) || !(← isProp c.type) then continue
    let short := (← unresolveNameGlobal n).toString
    unless out.contains short do out := out.push short
    if out.size == 16 then break
  return out

private structure Run where
  ci : ContextInfo
  mctx : MetavarContext
  goal : MVarId

private def key (r : Syntax.Range) : Nat × Nat := (r.start.byteIdx, r.stop.byteIdx)

/-- Every goal list a tactic at each source range ran on, without the repeats that macro
    expansion records. -/
private def runsByRange (tree : InfoTree) : Std.HashMap (Nat × Nat) (Array (Option Run)) :=
  tree.foldInfo (init := {}) fun ci info acc => Id.run do
    let .ofTacticInfo ti := info | return acc
    let some r := ti.stx.getRange? (canonicalOnly := true) | return acc
    let run := match ti.goalsBefore with
      | [g] => some { ci, mctx := ti.mctxBefore, goal := g }
      | _ => none
    acc.alter (key r) fun xs => some <| Id.run do
      let xs := xs.getD #[]
      if xs.any (fun x => match x, run with
          | some a, some b => a.goal == b.goal
          | _, _ => false) then xs else xs.push run

private def sequences (tree : InfoTree) : Array Syntax :=
  tree.foldInfo (init := #[]) fun _ info acc => Id.run do
    let .ofTacticInfo ti := info | return acc
    unless ti.stx.isOfKind ``Parser.Tactic.tacticSeq1Indented do return acc
    if acc.any (·.getRange? == ti.stx.getRange?) then acc else acc.push ti.stx


/-- Whether the goal of a run is a proposition, so that any proof of it can take the place of
    another. -/
private def isPropGoal (map : FileMap) (r : Run) : IO Bool := do
  let some decl := r.mctx.findDecl? r.goal | return false
  try
    Replay.inFile map r.ci decl.lctx do
      setMCtx r.mctx
      isProp (← instantiateMVars decl.type)
  catch _ => return false

/-- Closers for the proofs in one info tree, each one step in place of several. A closer may cost
    twice the steps it replaces and `perStep` raw heartbeats more for each step it saves: automation
    that searches is slower than the steps it finds. Of the closers that work, the cheapest. `suffixes` is the
    number of final steps tried as a group besides each whole sequence. -/
def edits (input : String) (map : FileMap) (tree : InfoTree) (perStep : Nat := 100000)
    (suffixes : Nat := 3) (spent : Nat := 0) : IO (Array Edit) := do
  let runs := runsByRange tree
  -- Outer sequences first: a closer for a whole block makes its inner blocks moot.
  let seqs := (sequences tree).qsort fun a b =>
    match a.getRange?, b.getRange? with
    | some x, some y => x.start < y.start || (x.start == y.start && y.stop < x.stop)
    | _, _ => false
  let mut out : Array Edit := #[]
  let mut taken : Array Syntax.Range := #[]
  for seq in seqs do
    let args := seq[0].getArgs
    let steps := (Array.range ((args.size + 1) / 2)).map (2 * ·)
    let n := steps.size
    if n == 0 then continue
    let some last := args[steps[n-1]!]!.getTailPos? (canonicalOnly := true) | continue
    -- A step whose goals the rest of the sequence closes one bullet each, as after `constructor`.
    let fan := Id.run do
      let mut j := n
      while j > 0 && args[steps[j-1]!]!.isOfKind `Lean.cdot do j := j - 1
      return if j ≥ 1 && n - j ≥ 2 then some (j - 1) else none
    let starts := #[0] ++ ((Array.range (min suffixes n)).map (n - 1 - ·)).reverse.filter (· > 0)
    let starts := match fan with
      | some j => if starts.contains j then starts else (starts.push j).qsort (· < ·)
      | none => starts
    for i in starts do
      let tac := args[steps[i]!]!
      let some first := tac.getPos? (canonicalOnly := true) | continue
      let r : Syntax.Range := ⟨first, last⟩
      if taken.any fun t => t.start ≤ r.start && r.stop ≤ t.stop then break
      let text := String.Pos.Raw.extract input r.start r.stop
      unless Steps.uncommented text do continue
      let some sites := runs[key (tac.getRange? (canonicalOnly := true)).get!]? | continue
      let some sites := sites.mapM id | continue
      if sites.isEmpty then continue
      unless ← sites.allM (isPropGoal map) do continue
      let suffix := mkNode ``Parser.Tactic.tacticSeq
        #[mkNode ``Parser.Tactic.tacticSeq1Indented #[mkNullNode (args.extract steps[i]! args.size)]]
      let some s0 := sites[0]? | continue
      let kinds := Steps.tacticKinds s0.ci.env
      -- A closer is one step, or two with the step it follows: only longer blocks are worth one.
      let had := Steps.count kinds suffix
      if had < 2 then continue
      let mut bases := #[]
      for s in sites do
        let some b ← Replay.run s.ci map s.mctx s.goal suffix (Replay.capFor s.ci spent) | break
        unless b.goals.isEmpty do break
        bases := bases.push b.heartbeats
      if bases.size < sites.size then continue
      let named := rules input suffix
      let informed := if named.isEmpty then #[] else
        let l := " [" ++ ", ".intercalate named.toList ++ "]"
        #["simp" ++ l, "simp_all" ++ l, "grind" ++ l]
      -- `step <;> closer` in place of the step and its bullets.
      let fanned := Id.run do
        unless fan == some i do return #[]
        let some sr := tac.getRange? (canonicalOnly := true) | return #[]
        let t := String.Pos.Raw.extract input sr.start sr.stop
        if t.contains '\n' then return #[]
        return (closers ++ informed).map (t ++ " <;> " ++ ·)
      -- Of the closers with fewer steps that work, the cheapest: `simp [h]` before `grind`.
      let mut found : Option (String × Nat) := none
      for c in closers ++ informed ++ fanned do
        let .ok stx := Parser.runParserCategory s0.ci.env `tactic c "<leanperf>" | continue
        let fewer := had - min had (Steps.count kinds stx)
        if fewer == 0 then continue
        let stx := Replay.relocate r stx
        let mut ok := true
        let mut cost := 0
        for (s, base) in sites.zip bases do
          let budget := 2 * base + perStep * fewer
          let some run ← Replay.run s.ci map s.mctx s.goal stx budget | ok := false; break
          unless run.goals.isEmpty do ok := false; break
          cost := cost + run.heartbeats
        if ok then
          match found with
          | some (b, k) => if cost < k || (cost == k && c.utf8ByteSize < b.utf8ByteSize) then found := some (c, cost)
          | none => found := some (c, cost)
      if let some (c, cost) := found then
        -- A whole block that starts on the line after its `by` moves up to that line when it fits.
        let (start, newText) := Id.run do
          if i != 0 then return (r.start, c)
          let mut p := r.start
          while p.byteIdx > 0 && ((p.prev input).get input).isWhitespace do p := p.prev input
          let kw := String.Pos.Raw.extract input ⟨p.byteIdx - min 3 p.byteIdx⟩ p
          let kw := if kw.length == 3 && (kw.front.isAlphanum || kw.front == '_') then "" else kw.trimAscii.toString
          let lineStart := map.ofPosition { map.toPosition p with column := 0 }
          let width := (String.Pos.Raw.extract input lineStart p).length + 1 + c.length
          if kw == "by" && p != r.start && width ≤ 100 then return (p, " " ++ c) else return (r.start, c)
        out := out.push { rule := "shorterBlock", range := ⟨start, r.stop⟩, newText,
                          message := s!"`{c}` closes the goal of these {had} steps: " ++
                            s!"{bases.foldl (· + ·) 0 / 1000} → {cost / 1000} heartbeats" }
        taken := taken.push r
        break
  return out

/-- Steps that the rest of their sequence does without: with the step deleted, the remaining
    steps still close the goal where the sequence starts, at most twice as slowly plus `perByte`
    raw heartbeats for each byte saved. Steps are tried from the first, and each deletion is kept
    for the steps after it. A step is deleted only with the whole lines it takes. -/
def unneededSteps (input : String) (map : FileMap) (tree : InfoTree) (perByte : Nat := 5000)
    (maxSteps : Nat := 24) (spent : Nat := 0) : IO (Array Edit) := do
  let runs := runsByRange tree
  let mut out : Array Edit := #[]
  for seq in sequences tree do
    let args := seq[0].getArgs
    let n := (args.size + 1) / 2
    if n < 2 || n > maxSteps then continue
    let some r0 := args[0]!.getRange? (canonicalOnly := true) | continue
    let some sites := runs[key r0]? | continue
    let some sites := sites.mapM id | continue
    if sites.isEmpty then continue
    unless ← sites.allM (isPropGoal map) do continue
    let build (kept : Array Nat) : Syntax :=
      let parts := kept.foldl (fun acc j => acc.push args[2 * j]! |>.push (args[2 * j + 1]?.getD mkNullNode)) #[]
      mkNode ``Parser.Tactic.tacticSeq #[mkNode ``Parser.Tactic.tacticSeq1Indented #[mkNullNode parts]]
    let mut bases := #[]
    for s in sites do
      let some b ← Replay.run s.ci map s.mctx s.goal (build (Array.range n)) (Replay.capFor s.ci spent) | break
      unless b.goals.isEmpty do break
      bases := bases.push b.heartbeats
    if bases.size < sites.size then continue
    let mut kept := Array.range n
    -- The last step closes the goal; the steps before it may be detours.
    for i in [:n - 1] do
      let some ri := args[2 * i]!.getRange? (canonicalOnly := true) | continue
      let some lines := Prune.wholeLines? input map ri | continue
      let saved := lines.stop.byteIdx - lines.start.byteIdx
      let candidate := build (kept.filter (· != i))
      let mut ok := true
      for (s, base) in sites.zip bases do
        let some run ← Replay.run s.ci map s.mctx s.goal candidate (2 * base + perByte * saved) | ok := false; break
        unless run.goals.isEmpty do ok := false; break
      if ok then
        kept := kept.filter (· != i)
        out := out.push { rule := "unneededStep", range := lines, newText := "",
                          message := s!"The rest of the proof does without this step ({saved} bytes)" }
  return out

/-- The location of a `rw` or `simp` step written as text after its rules: `" at h ⊢"` or `""`. -/
private def locationText (input : String) (stx : Syntax) : Option String := do
  let locs := (stx.find? (·.isOfKind ``Parser.Tactic.location)).bind fun l => l.getRange? (canonicalOnly := true)
  match locs with
  | none => return ""
  | some r => return " " ++ (String.Pos.Raw.extract input r.start r.stop)

/-- One step that may do the work of the adjacent steps `a` and `b` (their texts `ta`, `tb`): the steps' rules in one `rw` or `simp`, two `intro`s as one, `intro` then `exact` as a
    `fun`, `apply f` then `exact e` as `exact f e`. -/
private def pairCandidates (input : String) (a b : Syntax) (ta tb : String) : Array String := Id.run do
  let ha := Steps.head ta
  let hb := Steps.head tb
  let rewriting := ["rw", "rewrite", "simp", "simp_rw", "dsimp", "simp_all", "norm_num"]
  let mut out := #[]
  -- Rules of rewriting steps at the same location, together.
  if rewriting.contains ha && rewriting.contains hb then
    if let (some la, some lb) := (locationText input a, locationText input b) then
      if la == lb then
        let rs := rules input a ++ (rules input b).filter (!(rules input a).contains ·)
        if !rs.isEmpty then
          let l := " [" ++ ", ".intercalate rs.toList ++ "]"
          if ha == "rw" && hb == "rw" then out := out.push ("rw" ++ l ++ la)
          out := out ++ #["simp only" ++ l ++ la, "simp" ++ l ++ la]
          if la.isEmpty then out := out.push ("simp_all" ++ l)
  if ha == "intro" && hb == "intro" then
    out := out.push (ta ++ " " ++ (tb.drop 5).trimAsciiStart.toString)
  if ha == "intro" && hb == "exact" && ta.length > 6 then
    out := out.push s!"exact fun {(ta.drop 5).trimAsciiStart} ↦ {(tb.drop 5).trimAsciiStart}"
  if ha == "apply" && hb == "exact" then
    out := out.push s!"exact {(ta.drop 5).trimAsciiStart} ({(tb.drop 5).trimAsciiStart})"
  return out.qsort (·.utf8ByteSize < ·.utf8ByteSize)

/-- The goal a run starts from, as the infoview prints it; empty when it cannot be printed. -/
private def goalText (map : FileMap) (r : Run) : IO String := do
  let some decl := r.mctx.findDecl? r.goal | return ""
  try
    Replay.inFile map r.ci decl.lctx do
      setMCtx r.mctx
      return toString (← ppGoal r.goal)
  catch _ => return ""

/-- Candidates from the command `model` (see scripts/pair-dict), given the theorem, the steps before
    the window, the goal where the window starts and its steps; none when it fails. -/
private def modelCandidates (model statement : String) (previous : Array String) (goal : String)
    (steps : Array String) : IO (Array String) := do
  try
    let child ← IO.Process.spawn
      { cmd := "sh", args := #["-c", model], stdin := .piped, stdout := .piped, stderr := .null }
    let req := Json.mkObj [("statement", statement), ("previous", toJson previous), ("goal", goal),
      ("steps", toJson steps), ("first", toJson (steps[0]?.getD "")), ("second", toJson (steps[1]?.getD ""))]
    let child ← do
      let (stdin, child) ← child.takeStdin
      stdin.putStr req.compress
      stdin.flush
      pure child
    let out ← IO.asTask child.stdout.readToEnd
    let _ ← child.wait
    let some text := (out.get).toOption | return #[]
    match Json.parse text >>= (·.getObjValAs? (Array String) "candidates") with
    | .ok cs => return cs
    | .error _ => return #[]
  catch _ => return #[]

/-- `scripts/pair-dict` of the checkout that this program was built in, quoted for `sh`, if it is there. -/
private def defaultProposer : IO (Option String) := do
  let some root := (← IO.appPath).parent >>= (·.parent) >>= (·.parent) >>= (·.parent) | return none
  let script := root / "scripts" / "pair-dict"
  unless ← script.pathExists do return none
  return some ("'" ++ script.toString.replace "'" "'\\''" ++ "'")

/-- A peephole pass: adjacent steps that one step does the work of. In every tactic sequence that
    proves a proposition, a window of two single-line steps, and of three where two give nothing,
    is tried against `pairCandidates` (for two) and the proposer's candidates, such as the dictionary
    of learned rules. A candidate must have fewer steps than the window (`Steps.count`), and is kept
    when the sequence with it in place of the window still closes every goal it closed, at most
    twice as slowly plus `perStep` raw heartbeats for each step saved; of those, the cheapest. Any
    proof will do, so the goals between steps may differ. After a contraction the window steps back
    one, so a run of steps can shrink to one. -/
def contractPairs (input : String) (map : FileMap) (tree : InfoTree) (perStep : Nat := 100000)
    (maxSteps : Nat := 24) (maxChecks : Nat := 40) (statement := "") (width := 100) (spent : Nat := 0) :
    IO (Array Edit) := do
  let runs := runsByRange tree
  -- A proposer finds steps that no fixed rule knows: the command LEANPERF_PAIR_MODEL names, none
  -- when it is empty, and else the dictionary of LeanPerf's checkout (scripts/pair-dict).
  let model ← match ← IO.getEnv "LEANPERF_PAIR_MODEL" with
    | some "" => pure none
    | some m => pure (some m)
    | none => defaultProposer
  let debug ← debugging "pair"
  let trace (what : String) : IO Unit := do
    if debug then IO.eprintln s!"contractPair: {what}"; (← IO.getStderr).flush
  let mut out : Array Edit := #[]
  for seq in sequences tree do
    let args := seq[0].getArgs
    let n := (args.size + 1) / 2
    if n < 2 || n > maxSteps then continue
    let some r0 := args[0]!.getRange? (canonicalOnly := true) | continue
    let some sites := runs[key r0]? | continue
    let some sites := sites.mapM id | continue
    if sites.isEmpty then continue
    trace s!"sequence at line {(map.toPosition r0.start).line}: prop goal?"
    unless ← sites.allM (isPropGoal map) do continue
    -- Each step: its syntax, text, the source it replaces, whether it is new, and where it starts
    -- (for a new step, where the first step it replaces started).
    let mut cur : Array (Syntax × String × Syntax.Range × Bool × Option Run) := #[]
    let mut ok := true
    for k in [:n] do
      let st := args[2 * k]!
      let some r := st.getRange? (canonicalOnly := true) | ok := false; break
      cur := cur.push (st, String.Pos.Raw.extract input r.start r.stop, r, false,
        (runs[key r]?).bind (·.findSome? id))
    unless ok do continue
    let build (steps : Array Syntax) : Syntax :=
      mkNode ``Parser.Tactic.tacticSeq #[mkNode ``Parser.Tactic.tacticSeq1Indented
        #[mkNullNode (steps.foldl (fun acc s => acc.push s |>.push mkNullNode) #[] |>.pop)]]
    let mut bases := #[]
    trace s!"  replay {cur.size} steps"
    for s in sites do
      let some b ← Replay.run s.ci map s.mctx s.goal (build (cur.map (·.1))) (Replay.capFor s.ci spent) | break
      unless b.goals.isEmpty do break
      bases := bases.push b.heartbeats
    if bases.size < sites.size then continue
    let some s0 := sites[0]? | continue
    let mut i := 0
    let mut checks := 0
    while i + 1 < cur.size && checks < maxChecks do
      let (_, _, ra, _, ga) := cur[i]!
      let prefixChanged := (cur.extract 0 i).any (·.2.2.2.1)
      let kinds := Steps.tacticKinds s0.ci.env
      let previous := (cur.extract 0 i).map (·.2.1)
      -- A window of two steps, then of three where two give nothing.
      let mut merged := false
      for k in [2, 3] do
        if merged || i + k > cur.size || checks ≥ maxChecks then break
        let win := cur.extract i (i + k)
        let texts := win.map (·.2.1)
        let some (_, _, rb, _, _) := win.back? | break
        -- Every step on one line, without comments, each on the line after the one before.
        let span : Syntax.Range := ⟨ra.start, rb.stop⟩
        let adjacent := (List.range (k - 1)).all fun j =>
          (String.Pos.Raw.extract input win[j]!.2.2.1.stop win[j + 1]!.2.2.1.start).trimAscii.isEmpty
        unless texts.all (!·.contains '\n') && adjacent &&
            Steps.uncommented (String.Pos.Raw.extract input span.start span.stop) do break
        let had := win.foldl (fun n w => n + Steps.count kinds w.1) 0
        -- Of the candidates with fewer steps that work, the cheapest, then the shortest: `rwa [h]`
        -- before `grind` when both close the goal.
        let mut found : Option (Syntax × String × Nat) := none
        let fixed := if k == 2 then pairCandidates input win[0]!.1 win[1]!.1 texts[0]! texts[1]! else #[]
        trace s!"  window {" / ".intercalate (texts.toList.map fun t => (t.take 50).toString)}"
        let goal ← match model, ga with
          | some _, some g => goalText map g
          | _, _ => pure ""
        let proposed ← match model with
          | some m => modelCandidates m statement previous goal texts
          | none => pure #[]
        let cands := (fixed ++ proposed.filter (!fixed.contains ·)).qsort (·.utf8ByteSize < ·.utf8ByteSize)
        for c in cands do
          if checks ≥ maxChecks then break
          let .ok stx := Parser.runParserCategory s0.ci.env `tactic c "<leanperf>" | continue
          let fewer := had - min had (Steps.count kinds stx)
          if fewer == 0 then continue
          -- The step stays on one line, within 100 columns.
          if (map.toPosition span.start).column + c.length > width then continue
          let stx := Replay.relocate span stx
          checks := checks + 1
          let after := (cur.extract (i + k) cur.size).map (·.1)
          let candidate := build ((cur.extract 0 i).map (·.1) ++ #[stx] ++ after)
          let mut works := true
          -- While the steps before the window are the original ones, the goal recorded before it
          -- is where a replay of the whole sequence gets to, so a candidate that fails from there
          -- fails: only it and the steps after it are run. Most candidates fail.
          trace s!"    candidate {c.take 80}"
          if let some g := ga then
            if !prefixChanged then
              let budget := 2 * bases.foldl max 0 + perStep * fewer
              match ← Replay.run g.ci map g.mctx g.goal (build (#[stx] ++ after)) budget with
              | some run => unless run.goals.isEmpty do works := false
              | none => works := false
          unless works do continue
          let mut cost := 0
          for (s, base) in sites.zip bases do
            let budget := 2 * base + perStep * fewer
            let some run ← Replay.run s.ci map s.mctx s.goal candidate budget | works := false; break
            unless run.goals.isEmpty do works := false; break
            cost := cost + run.heartbeats
          if works then
            match found with
            | some (_, b, k) =>
              if cost < k || (cost == k && c.utf8ByteSize < b.utf8ByteSize) then found := some (stx, c, cost)
            | none => found := some (stx, c, cost)
        if let some (stx, c, _) := found then
          -- Accepted contractions are training data for the dictionary and the model.
          if let some log ← IO.getEnv "LEANPERF_PAIR_LOG" then
            let h ← IO.FS.Handle.mk log .append
            h.putStrLn (Json.mkObj [("source", "leanperf"), ("statement", statement),
              ("previous", toJson previous), ("goal", goal), ("steps", toJson texts), ("merged", c)]).compress
          cur := (cur.extract 0 i).push (stx, c, span, true, ga) ++ cur.extract (i + k) cur.size
          merged := true
      -- After a contraction the step before may merge with the new one.
      if !merged then i := i + 1
      else if i > 0 then i := i - 1
    for (_, t, r, changed, _) in cur do
      if changed then
        out := out.push { rule := "contractPair", range := r, newText := t,
                          message := s!"One step does the work of these: {t}" }
  return out

end LeanPerf.Blocks
