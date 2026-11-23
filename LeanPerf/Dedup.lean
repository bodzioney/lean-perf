import LeanPerf.Build
import LeanPerf.Project
import LeanPerf.Tactics

/-!
# Duplicate and specialized theorems

Finds theorems whose statement repeats an existing one up to binder names, binder order, binder
annotations and universe names, and theorems that are a syntactic instance of a more general
lemma. The analysis needs elaborated statements, but not proofs: unbuilt project modules are
elaborated as *skeletons* where every theorem proof is `sorry`. Proof irrelevance makes this sound
for statements, and it skips the part of the build that usually dominates.
-/

open Lean Meta Elab

namespace LeanPerf.Dedup

/-! ## Canonical statements -/

private partial def occOrderM (e : Expr) : StateM (Std.HashSet Expr × Array FVarId) Unit := do
  if !e.hasFVar || (← get).1.contains e then return
  modify fun (seen, acc) => (seen.insert e, acc)
  match e with
  | .fvar id => modify fun (seen, acc) => (seen, if acc.contains id then acc else acc.push id)
  | .app f a => occOrderM f; occOrderM a
  | .lam _ t b _ | .forallE _ t b _ => occOrderM t; occOrderM b
  | .letE _ t v b _ => occOrderM t; occOrderM v; occOrderM b
  | .mdata _ b | .proj _ _ b => occOrderM b
  | _ => pure ()

/-- Extend `acc` with the free variables of `e` in left-to-right first-occurrence order. -/
def occOrder (e : Expr) (acc : Array FVarId := #[]) : Array FVarId :=
  ((occOrderM e).run ({}, acc)).2.2

/-- Lean already encodes each bound occurrence as a de Bruijn index. Strip the remaining
    display names and binder annotations throughout the term, including binder domains.
    The original type stays in the elaborator for printing and checking suggested proofs. -/
private partial def nameless (type : Expr) : Expr :=
  runST fun ω => (visit (ω := ω) type).run
where
  visit {ω} (e : Expr) : MonadCacheT Expr Expr (ST ω) Expr := checkCache e fun _ => do
    match e with
    | .forallE _ t b _ => return .forallE .anonymous (← visit t) (← visit b) .default
    | .lam _ t b _ => return .lam .anonymous (← visit t) (← visit b) .default
    | .letE _ t v b _ => return .letE .anonymous (← visit t) (← visit v) (← visit b) false
    | .app f a => return e.updateApp! (← visit f) (← visit a)
    | .proj _ _ b => return e.updateProj! (← visit b)
    | .mdata _ b => visit b
    | _ => return e

/-- Rename universe parameters `u.0, u.1, …` in order of first occurrence. -/
def normLevels (e : Expr) : Expr :=
  let ps := (collectLevelParams {} e).params
  e.instantiateLevelParams ps.toList ((List.range ps.size).map fun i => mkLevelParam (.num `u i))

/-- Refine otherwise indistinguishable binders by their roles in the dependent telescope.
    Each round mixes the ordered dependencies of a binder and the unordered collection of
    places where other binders depend on it. Renaming or permuting the telescope preserves
    these colors. Hashes only guide ordering; duplicate reports require exact equality. -/
private def binderColors (ids anchors : Array FVarId) : MetaM (Std.HashMap FVarId UInt64) := do
  let mut colors : Std.HashMap FVarId UInt64 := {}
  let mut deps : Std.HashMap FVarId (Array FVarId) := {}
  let mut users : Std.HashMap FVarId (Array (FVarId × Nat)) := {}
  for id in ids do
    let ty ← id.getType
    let shape := normLevels (nameless (ty.replace fun e => if e.isFVar then some (mkConst `_) else none))
    colors := colors.insert id (hash (shape, anchors.idxOf? id))
    let ds := occOrder ty
    deps := deps.insert id ds
    for (dep, i) in ds.zipIdx do
      users := users.alter dep fun old => some ((old.getD #[]).push (id, i))
  let mut distinct := (Std.HashSet.ofArray colors.valuesArray).size
  for _ in [:ids.size] do
    let mut next := colors
    for id in ids do
      let inputs := deps[id]!.map (colors[·]!)
      let uses := (users[id]?.getD #[]).map fun (owner, i) => (colors[owner]!, i)
      let uses := uses.qsort fun (a, i) (b, j) => a < b || (a == b && i < j)
      next := next.insert id (hash (colors[id]!, inputs, uses))
    colors := next
    let n := (Std.HashSet.ofArray colors.valuesArray).size
    if n == distinct then break
    distinct := n
  return colors

/--
A representative of `type` up to binder names (bound occurrences use de Bruijn indices), binder annotations,
universe names and any reordering of binders that respects dependencies. Binders are ordered by
first occurrence in the conclusion, then in already-ordered binder types, ties broken by the
shape of their types, then stably sorted so that each binder follows its dependencies.

Equal representatives are a proof of equivalence. Unequal ones are not a proof of inequivalence.
-/
private def canonicalWithOrder (type : Expr) : MetaM (Expr × Array Nat) :=
  forallTelescope type fun xs body => do
    let ids := xs.map (·.fvarId!)
    let mut order := occOrder body
    let anchors := order
    let mut colors : Option (Std.HashMap FVarId UInt64) := none
    let mut i := 0
    while order.size < ids.size do
      if h : i < order.size then
        order := occOrder (← order[i].getType) order
        i := i + 1
      else
        let ordered := order.map mkFVar
        let shape (id : FVarId) : MetaM UInt64 := do
          let t := (← id.getType).abstract ordered
          return hash (normLevels (nameless (t.replace fun e => if e.isFVar then some (mkConst `_) else none)))
        let rest := ids.filter (!order.contains ·)
        let mut best := rest[0]!
        let mut bestKey ← shape best
        for id in rest.extract 1 rest.size do
          let k ← shape id
          if k < bestKey then
            best := id
            bestKey := k
          else if k == bestKey then
            let cs ← colors.getDM (binderColors ids anchors)
            colors := some cs
            if cs[id]! < cs[best]! then best := id
        order := order.push best
    let mut sorted : Array FVarId := #[]
    let mut pending := order
    while !pending.isEmpty do
      let mut pick := none
      for id in pending do
        if (occOrder (← id.getType)).all sorted.contains then
          pick := some id
          break
      let some id := pick | throwError "binder dependency cycle"
      sorted := sorted.push id
      pending := pending.erase id
    return (normLevels (nameless (← mkForallFVars (sorted.map mkFVar) body)), sorted.map ids.idxOf)

def canonical (type : Expr) : MetaM Expr := return (← canonicalWithOrder type).1

/-- Whether an imported theorem is something a person would cite. -/
def citable (env : Environment) (n : Name) : CoreM Bool := do
  if LazyDiscrTree.blacklistInsertion env n || n.isInternalDetail || n.isMetaprogramming then
    return false
  if Linter.isDeprecated env n then return false
  return !(← isAutoDeclOrPrivate_Internal n)

/-! ## Skeleton elaboration -/

/-- The source of a theorem-like command whose proof was removed. -/
structure Target where
  declId : Syntax
  declVal : Syntax

/--
`:= no_implicit_lambda% sorry`. Without the annotation, Lean would wrap the proof in a `fun` for
each implicit binder after the colon, and the proof's leading `fun`s would no longer be exactly
the binders that a proof can name.
-/
private def sorryVal : Syntax :=
  let body := mkNode ``Parser.Term.noImplicitLambda
    #[mkAtom "no_implicit_lambda%", mkNode ``Parser.Term.sorry #[mkAtom "sorry"]]
  mkNode ``Parser.Command.declValSimple #[mkAtom ":=", body,
    mkNode ``Parser.Termination.suffix #[mkNullNode, mkNullNode], mkNullNode]

/--
Replace a theorem proof with `sorry`. Returns `none` for a command that declares nothing worth
keeping (`example`), and the original command for anything else, since definitions can be
unfolded while elaborating later statements.
-/
partial def skeleton (cmd : Syntax) : Option (Syntax × Option Target) := do
  if cmd.isOfKind ``Parser.Command.in then
    let (inner, t) ← skeleton cmd[2]
    return (cmd.setArg 2 inner, t)
  if cmd.isOfKind ``Parser.Command.declaration then
    let d := cmd[1]
    if d.isOfKind ``Parser.Command.example then none
    if d.isOfKind ``Parser.Command.theorem then
      return (cmd.setArg 1 (d.setArg 3 sorryVal), some ⟨d[1], d[3]⟩)
    return (cmd, none)
  -- Mathlib's `lemma`: `declModifiers group("lemma " declId declSig declVal)`.
  if cmd.getKind matches .str _ "lemma" then
    let g := cmd[1]
    if g.getNumArgs == 4 then
      return (cmd.setArg 1 (g.setArg 3 sorryVal), some ⟨g[1], g[3]⟩)
  return (cmd, none)

/-- Set while elaborating a skeleton command. -/
builtin_initialize skeletonMode : IO.Ref Bool ← IO.mkRef false

/--
In a skeleton, a tactic block whose goal is a proposition becomes `sorry`, wherever it occurs:
proof fields of structures and instances usually cost more than the statements around them.
Everything else falls through to Lean's own elaborator, which this one precedes.
-/
@[builtin_term_elab Lean.Parser.Term.byTactic]
def elabSkeletonProof : Term.TermElab := fun _ expectedType? => do
  unless ← skeletonMode.get do throwUnsupportedSyntax
  let some type := expectedType? | throwUnsupportedSyntax
  unless ← isProp type do throwUnsupportedSyntax
  mkSorry type (synthetic := false)

/-- Workers elaborate one command at a time. Compilable definitions remain available to
    metaprograms in modules that import this skeleton. -/
private def withSkeleton (x : IO α) (enabled : Bool) : IO α := do
  skeletonMode.set enabled
  try x finally skeletonMode.set false

/-- A theorem written in an analyzed source file. -/
structure Decl where
  name : Name
  /-- Position of the declaration name. -/
  nameRange : Lsp.Range
  /-- The proof, when it can be replaced by a term without losing auxiliary declarations. -/
  proof : Option Lsp.Range
  /-- How many of the statement's binders are in scope in the proof (those before the colon). -/
  inScope : Nat
  /-- The environment just before the declaration, which is what its proof can use. -/
  env : Environment

structure FileResult where
  decls : Array Decl := #[]
  parseErrors : Nat := 0
  elabErrors : Nat := 0
  /-- The first few error messages, with positions. -/
  messages : Array String := #[]
  deriving Inhabited

private partial def lambdas : Expr → Nat
  | .lam _ _ b _ => lambdas b + 1
  | .mdata _ b => lambdas b
  | _ => 0

private def lspRange? (map : FileMap) (stx : Syntax) : Option Lsp.Range :=
  stx.getRange?.map map.utf8RangeToLspRange

/-- A private name as written in source. -/
def sourceName (n : Name) : Name :=
  if !isPrivateName n then n else
  let cs := n.components
  match cs.reverse.findIdx? (· matches .num _ _) with
  | some i => cs.drop (cs.length - i) |>.foldl (· ++ ·) .anonymous
  | none => n

/--
Elaborate a source file's skeleton on top of `env`, which must contain its imports, as main
module `main`. With `full`, elaborate the file as written, including its proofs.
-/
def elabSource (env : Environment) (main : Name) (fileName input : String) (opts : Options)
    (full := false) : IO (Environment × FileResult) := do
  let ictx := Parser.mkInputContext input fileName
  let (_, ps0, headerLog) ← Parser.parseHeader ictx
  let mut s := Command.mkState (env.setMainModule main) {} opts
  s := { s with infoState.enabled := false }
  let mut ps := ps0
  let mut res : FileResult := {}
  for msg in headerLog.toList do
    if msg.severity == .error then
      res := { res with parseErrors := res.parseErrors + 1, messages := res.messages.push (← msg.toString) }
  -- Undocumented: compare skeleton elaboration with full elaboration of the same modules.
  let full := full || (← IO.getEnv "LEANPERF_FULL").isSome
  repeat
    let scope := s.scopes.head!
    let pctx : Parser.ParserModuleContext :=
      { env := s.env, options := scope.opts
        currNamespace := scope.currNamespace, openDecls := scope.openDecls }
    let (cmd, ps', log) := Parser.parseCommand ictx pctx ps {}
    if log.hasErrors then
      res := { res with parseErrors := res.parseErrors + 1 }
      for msg in log.toList do
        if msg.severity == .error && res.messages.size < 5 then
          res := { res with messages := res.messages.push (← msg.toString) }
    let pos := ps.pos
    ps := ps'
    if Parser.isTerminalCommand cmd then break
    let some (cmd', target) := (if full then some (cmd, none) else skeleton cmd) | continue
    let ctx : Command.Context :=
      { fileName, fileMap := ictx.fileMap, cmdPos := pos, snap? := none, cancelTk? := none }
    let t0 ← IO.monoMsNow
    let run := ((Command.elabCommandTopLevel cmd').run ctx |>.run { s with messages := {} }).toIO'
    let before := s.env
    let r ← withSkeleton run (!full)
    if let some limit := (← IO.getEnv "LEANPERF_PROFILE").bind (·.toNat?) then
      let dt := (← IO.monoMsNow) - t0
      if dt ≥ limit then
        let text := (cmd.getRange?.map fun r => String.Pos.Raw.extract input r.start r.stop).getD ""
        IO.eprintln s!"{dt} ms {cmd.getKind} {fileName}: {(text.take 150).toString.replace "\n" " "}"
    match r with
    | .error e => res := { res with
        elabErrors := res.elabErrors + 1
        messages := res.messages.push s!"{fileName}: {← e.toMessageData.toString}" }
    | .ok ((), s') =>
      s := s'
      if s'.messages.hasErrors then
        res := { res with elabErrors := res.elabErrors + 1 }
        for msg in s'.messages.toList do
          if msg.severity == .error && res.messages.size < 5 then
            let text := s!"{msg.pos.line}:{msg.pos.column + 1}: {(← msg.data.toString).trimAscii}"
            res := { res with messages := res.messages.push text }
      let some t := target | continue
      let id := t.declId[0].getId
      let full := if id.getRoot == `_root_ then id.replacePrefix `_root_ .anonymous
        else scope.currNamespace ++ id
      let some name := [full, mkPrivateName s.env full].find? s.env.contains | continue
      let some nameRange := lspRange? ictx.fileMap t.declId[0] | continue
      let simple := t.declVal.isOfKind ``Parser.Command.declValSimple && t.declVal[3].isNone
      let proof := if simple then lspRange? ictx.fileMap t.declVal else none
      -- The skeleton proof is `fun <binders before the colon> => sorry`.
      let some (.thmInfo val) := s.env.find? name | continue
      let inScope := lambdas val.value
      res := { res with decls := res.decls.push { name, nameRange, proof, inScope, env := before } }
  return (s.env, res)

/-! ## Indexes -/

def runMeta (env : Environment) (opts : Options) (x : MetaM α) : IO α := do
  let ctx : Core.Context :=
    { fileName := "<leanperf-dedup>", fileMap := default, options := opts, maxHeartbeats := 0 }
  let (a, _) ← (x.run' {} {}).toIO ctx { env }
  return a

/-- A constant at the head of an application survives substitution for telescope variables.
    An application headed by a variable can change shape entirely, including its arguments. -/
private def rigidHead : Expr → Name
  | .app f _ | .mdata _ f => rigidHead f
  | .const n _ => n
  | _ => .anonymous

private structure ConclusionShape where
  head : Name := .anonymous
  penultimate : Name := .anonymous
  last : Name := .anonymous
  deriving Inhabited, BEq, Hashable

private def conclusionShape (e : Expr) : ConclusionShape := Id.run do
  let head := rigidHead e
  if head.isAnonymous then return {}
  let .app f a := e.consumeMData | return { head }
  let penultimate := match f.consumeMData with
    | .app _ b => rigidHead b
    | _ => .anonymous
  return { head, penultimate, last := rigidHead a }

/-- A cheap necessary condition for equality of canonical types. The domain sum is invariant
    under telescope permutation. Variable indices, binder names and universe names are omitted;
    the exact comparison still uses the closed de Bruijn expressions. -/
private def duplicateKey (type : Expr) : UInt64 := go type 0 0
where
  go (e : Expr) (count domains : UInt64) : UInt64 :=
    match e with
    | .mdata _ b => go b count domains
    | .forallE _ d b _ => go b (count + 1) (domains + hash (conclusionShape d))
    | _ => mixHash (mixHash count domains) (hash (conclusionShape e))

private def treeEntry (project : Option (Std.HashMap Name (Name × Nat))) (name : Name)
    (c : AsyncConstantInfo) : MetaM (Array (LazyDiscrTree.InitEntry Name)) := do
  unless c.kind == .thm do return #[]
  match project with
  | some decls => unless decls.contains name do return #[]
  | none => unless ← citable (← getEnv) name do return #[]
  forallTelescope c.toConstantVal.type fun _ type => return #[← LazyDiscrTree.InitEntry.fromExpr type name]

private def droppedKeys : List (List LazyDiscrTree.Key) :=
  [[.star], [.const ``Eq 3, .star, .star, .star]]

private structure ImportedTheorem where
  order : Nat
  moduleName : Name
  info : ConstantInfo
  deriving Inhabited

private structure ImportedIndex where
  duplicates : Std.HashMap UInt64 (Array Name)
  exact : IO.Ref (Std.HashMap UInt64 (Std.HashMap Expr (Array Name)))
  patterns : Std.HashMap ConclusionShape (Array ImportedTheorem)
  trees : IO.Ref (Std.HashMap ConclusionShape (LazyDiscrTree.ModuleDiscrTreeRef Name))

private def importedIndex (base : Environment) (general : Bool) : IO ImportedIndex := do
  let mut duplicates := {}
  let mut patterns := {}
  let mut order := 0
  for mod in base.header.moduleNames, data in base.header.moduleData do
    for c in data.constants do
      let .thmInfo thm := c | continue
      duplicates := duplicates.alter (duplicateKey thm.type) fun a => some ((a.getD #[]).push thm.name)
      if general then
        let shape := conclusionShape thm.type.getForallBody
        patterns := patterns.alter shape fun a => some ((a.getD #[]).push ⟨order, mod, c⟩)
        order := order + 1
  return { duplicates, patterns, exact := ← IO.mkRef {}, trees := ← IO.mkRef {} }

private def importDuplicates (idx : ImportedIndex) (bucket : UInt64) (key : Expr) : MetaM (Array Name) := do
  let some names := idx.duplicates[bucket]? | return #[]
  if let some exact := (← idx.exact.get)[bucket]? then return exact[key]?.getD #[]
  let env ← getEnv
  let mut exact := {}
  for n in names do
    if n.isInternalDetail || isPrivateName n then continue
    let some info := env.find? n | continue
    let ty ← canonical info.type
    exact := exact.alter ty fun ns => some ((ns.getD #[]).push n)
  idx.exact.modify (·.insert bucket exact)
  return exact[key]?.getD #[]

/-- The old search already required syntactic equality after instantiation. Only these disjoint
    buckets can satisfy that check. Wildcard operands include higher-order variable applications. -/
private def compatibleShapes (q : ConclusionShape) : Array ConclusionShape := Id.run do
  let mut keys := #[{}]
  if q.head.isAnonymous then return keys
  keys := keys.push { head := q.head }
  if !q.penultimate.isAnonymous then keys := keys.push { q with last := .anonymous }
  if !q.last.isAnonymous then keys := keys.push { q with penultimate := .anonymous }
  if !q.penultimate.isAnonymous && !q.last.isAnonymous then keys := keys.push q
  return keys

private def importMatches (idx : ImportedIndex) (goal : Expr) :
    MetaM (LazyDiscrTree.MatchResult Name) := do
  let shape := conclusionShape goal
  let tree ← (← idx.trees.get)[shape]?.getDM do
    let mut candidates := #[]
    for key in compatibleShapes shape do
      candidates := candidates ++ idx.patterns[key]?.getD #[]
    -- Lean breaks ties in import order. Restore that order after merging the buckets.
    let sorted := candidates.qsort (·.order < ·.order)
    let ctx := LazyDiscrTree.createTreeCtx (← readThe Core.Context)
    let env ← getEnv
    let errors ← LazyDiscrTree.ImportData.new
    let cache ← IO.mkRef (LazyDiscrTree.Cache.empty (← LazyDiscrTree.getChildNgen))
    let mut pre := {}
    for c in sorted do
      pre ← LazyDiscrTree.addConstImportData ctx env c.moduleName errors cache pre
        (treeEntry none) (.ofConstantInfo c.info)
    for e in ← errors.errors.get do LazyDiscrTree.logImportFailure e
    let ref := { ref := ← IO.mkRef (← LazyDiscrTree.dropKeys pre.toLazy droppedKeys) }
    idx.trees.modify (·.insert shape ref)
    return ref
  LazyDiscrTree.findModuleMatches tree goal

private structure Index where
  localDups : Std.HashMap Expr (Array Name)
  imports : ImportedIndex
  project : Option (LazyDiscrTree.ModuleDiscrTreeRef Name)

private def buildIndex (env : Environment) (decls : Std.HashMap Name (Name × Nat)) (opts : Options)
    (imports : ImportedIndex) (general : Bool) : IO Index := do
  let localDups ← runMeta env opts do
    let mut dups : Std.HashMap Expr (Array Name) := {}
    for (n, _) in decls do
      let k ← canonical (← getConstInfo n).type
      dups := dups.alter k fun a => some ((a.getD #[]).push n)
    return dups
  let project ← if general then runMeta env opts do
    let t ← LazyDiscrTree.createModuleDiscrTree (treeEntry (some decls))
    return some { ref := ← IO.mkRef (← LazyDiscrTree.dropKeys t droppedKeys) }
  else pure none
  return { localDups, imports, project }

/-! ## Queries -/

/-- An existing theorem that proves a new one. -/
structure Match where
  lemma : Name
  /-- Same statement up to renaming and reordering, rather than a special case. -/
  duplicate : Bool
  reordered : Bool
  /-- Proof term for the new theorem, checked by the elaborator, if the lemma is visible. -/
  term : Option String

private def accessible (xs : Array Expr) (i : Nat) : MetaM (Option Name) := do
  let n ← xs[i]!.fvarId!.getUserName
  if n.hasMacroScopes || n.isInternal then return none
  -- A later binder with the same name shadows this one in the proof.
  for j in [i+1:xs.size] do
    if (← xs[j]!.fvarId!.getUserName) == n then return none
  return some n

private def withIntros (term : String) (xs : Array Expr) (inScope : Nat) : MetaM String := do
  if inScope == xs.size then return term
  let mut names := #[]
  for i in [inScope:xs.size] do
    names := names.push (((← accessible xs i).map toString).getD "_")
  return s!"by intro {" ".intercalate names.toList}; exact {term}"

/-- Equal canonical types provide a bijection even for a parameter that does not occur in the
    conclusion or in any hypothesis. Unification alone cannot infer such an argument. -/
private def alignedProof (x : Name) (candidate target : Array Nat) (xs : Array Expr)
    (inScope : Nat) : MetaM String := do
  let mut args := Array.replicate xs.size "_"
  for i in candidate, j in target do
    if let some n ← accessible xs j then args := args.set! i n.toString
    else if ← isProp (← inferType xs[j]!) then args := args.set! i "(by assumption)"
  withIntros (" ".intercalate (s!"@{sourceName x}" :: args.toList)) xs inScope

/-- Alternative premise assignments matter when a conclusion leaves an argument undetermined.
    Every premise must hold for the same substitution. Conjunction projections are ordinary
    proof terms, so they can be printed in the final theorem application. -/
private def premiseFacts : MetaM (Array (Expr × Expr)) := do
  let mut facts := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail || !(← isProp d.type) then continue
    facts := facts.push (d.toExpr, d.type)
    if d.type.isAppOfArity ``And 2 then
      facts := facts.push (← mkAppM ``And.left #[d.toExpr], d.type.appFn!.appArg!)
      facts := facts.push (← mkAppM ``And.right #[d.toExpr], d.type.appArg!)
  return facts.reverse

private def matchPremises (facts : Array (Expr × Expr)) (remaining : IO.Ref Nat) :
    List Expr → MetaM Bool
  | [] => pure true
  | arg :: rest => do
    let m := arg.mvarId!
    let ty ← m.getType
    if (← m.isAssigned) || !(← isProp ty) then return ← matchPremises facts remaining rest
    let saved ← saveState
    for (value, type) in facts do
      if ← withReducible (isDefEq type ty) then
        let fuel ← remaining.get
        if fuel == 0 then saved.restore; return false
        remaining.set (fuel - 1)
        m.assign value
        if ← matchPremises facts remaining rest then return true
      saved.restore
    return false

/--
Check that lemma `x` proves `concl` by instantiating its arguments, with the instantiated
conclusion syntactically equal to `concl`. Hypotheses are closed by a local assumption or by
instance synthesis. `pre` are the theorem's binders in scope in its proof, and `post` those after
the colon, which the proof must introduce. Returns the text of a proof.
-/
def instantiate (x : Name) (pre post : Array Expr) (concl : Expr) : MetaM (Option String) :=
  withNewMCtxDepth do
  let info ← getConstInfo x
  let lem := mkConst x (← info.levelParams.mapM fun _ => mkFreshLevelMVar)
  let (ms, bis, xConcl) ← forallMetaTelescope (← inferType lem)
  unless ← withReducible (isDefEq xConcl concl) do return none
  if (← instantiateMVars xConcl) != concl then return none
  -- Hypotheses first: matching one against a local can assign arguments the conclusion lacks.
  let start ← saveState
  for m in ms do
    let m := m.mvarId!
    if !(← m.isAssigned) && (← isProp (← m.getType)) then
      unless ← m.assumptionCore do
        start.restore
        unless ← matchPremises (← premiseFacts) (← IO.mkRef 64) ms.toList do return none
        break
  for m in ms do
    let m := m.mvarId!
    if ← m.isAssigned then continue
    let ty ← instantiateMVars (← m.getType)
    unless (← isClass? ty).isSome do return none
    let some inst ← synthInstance? ty | return none
    unless ← isDefEq (.mvar m) inst do return none
  let xs := pre ++ post
  let mut names : Array (Option Name) := #[]
  for i in [0:xs.size] do
    names := names.push (← accessible xs i)
  let mut args := #[]
  for m in ms, bi in bis do
    let v ← instantiateMVars m
    if v.hasExprMVar then return none
    let arg ← match xs.idxOf? v |>.bind (names[·]?) |>.join with
      | some n => pure n.toString
      | none =>
        if bi.isInstImplicit then pure "_"
        else if ← isProp (← inferType v) then
          if v.isFVar then pure "(by assumption)" else pure s!"({(← ppExpr v).pretty 200})"
        else pure "_"
    args := args.push arg
  let term := " ".intercalate (s!"@{sourceName x}" :: args.toList)
  return some (← withIntros term xs pre.size)

abbrev confirm := ProofCompression.confirm

/--
Run `x` with a fresh heartbeat budget, treating exhaustion as failure. Heartbeat exhaustion is a
runtime exception, which `try … catch` does not catch.
-/
private def budget (x : MetaM (Option α)) (n : Nat := 200000) : MetaM (Option α) :=
  tryCatchRuntimeEx
    (withCurrHeartbeats <| withTheReader Core.Context ({ · with maxHeartbeats := n * 1000 }) x)
    fun _ => return none

/-- Search the module's own declarations and imports. Check each proof in the declaration's environment. -/
private def search (idx : Index) (decl : Name) (inScope : Nat)
    (visible : Name → Bool) (duplicates : Bool) (checkEnv : Environment) :
    MetaM (Option Match) := do
  let ty := (← getConstInfo decl).type
  let (key, targetOrder) ← canonicalWithOrder ty
  let env ← getEnv
  let mut dups := #[]
  let bucket := duplicateKey ty
  let found := idx.localDups[key]?.getD #[] ++ (← importDuplicates idx.imports bucket key)
  for x in found do
    if x == decl || !env.contains x then continue
    if (env.getModuleIdxFor? x).isSome && !(← citable env x) then continue
    dups := dups.push x
  dups := dups.qsort (·.toString < ·.toString)
  let plain (n : Name) : MetaM Expr := return normLevels (nameless (← getConstInfo n).type)
  -- `pre` are in scope in the proof; the proof's own type `rest` binds the others.
  forallBoundedTelescope ty inScope fun pre rest => do
    let attempt (x : Name) (duplicate : Bool) : MetaM (Option Match) := do
      let reordered := duplicate && (← plain x) != (← plain decl)
      if !visible x then return some { lemma := x, duplicate, reordered, term := none }
      let term? ← forallTelescope rest fun post concl => do
        if duplicate then
          let (_, order) ← canonicalWithOrder (← getConstInfo x).type
          return some (← alignedProof x order targetOrder (pre ++ post) inScope)
        budget (instantiate x pre post concl)
      let some term := term? | return none
      -- Elaborate the proof where it will be: no later declarations, no later modules.
      let ok := (← budget do return some (← withEnv checkEnv (confirm rest term))).getD false
      return some { lemma := x, duplicate, reordered, term := if ok then some term else none }
    -- Prefer what the new theorem can cite: a restatement, then a more general lemma.
    let mut fallback := none
    -- Prefer a restatement whose arguments line up, then any, deterministically.
    let ranked ← (if duplicates then dups.filter visible else #[]).mapM fun x => return ((← plain x) != (← plain decl), x)
    let ranked := ranked.qsort fun (r, x) (r', x') => (!r && r') || (r == r' && x.toString < x'.toString)
    for (_, x) in ranked do
      if let some m ← attempt x true then
        if m.term.isSome then return some m
        fallback := fallback <|> some m
    if let some project := idx.project then
      let cands ← forallTelescope rest fun _ concl => do
        let imported ← importMatches idx.imports concl
        let local_ ← LazyDiscrTree.findModuleMatches project concl
        return local_.appendResults (imported.appendResults #[])
      -- Most specific patterns (highest match scores) come last.
      for x in cands.reverse do
        if x == decl || !visible x || !env.contains x || dups.contains x then continue
        if let some m ← attempt x false then
          if m.term.isSome then return some m
    return fallback

/-! ## Reports -/

structure Finding where
  rule : String
  message : String
  /-- The existing theorem, as the suggested proof cites it. -/
  lemma : String
  range : Lsp.Range
  edit : Option Lsp.TextEdit
  deriving ToJson, FromJson

structure Report where
  findings : Array Finding := #[]
  skippedCommands : Nat := 0
  elabErrors : Nat := 0
  deriving ToJson, FromJson

def message (decl : Name) (m : Match) (visible : Bool) : String :=
  let how := if !m.duplicate then "is a special case of"
    else if m.reordered then "restates (with arguments reordered)" else "restates"
  let fix := if visible then ""
    else if isPrivateName m.lemma then ", which is private to another module"
    else ", which this module does not import"
  s!"{sourceName decl} {how} {sourceName m.lemma}{fix}"

/-- Every declaration is checked in its own module with precisely its direct imports. -/
private def report (opts : Options) (mod : Name) (env : Environment) (res : FileResult)
    (general duplicates : Bool) (imports : ImportedIndex) : IO Report := do
  let position : Std.HashMap Name (Name × Nat) := res.decls.foldl (init := {}) fun acc d =>
    acc.insert d.name (mod, acc.size)
  let idx ← buildIndex env position opts imports general
  let visibleFrom (k : Nat) (x : Name) : Bool :=
    match position[x]? with
    | some (_, j) => j < k
    | none => !isPrivateName x && (env.getModuleIdxFor? x).isSome
  let mut findings := #[]
  for h : k in [0:res.decls.size] do
    let d := res.decls[k]
    let found ← runMeta env opts do
      tryCatchRuntimeEx
        (search idx d.name d.inScope (visibleFrom k) duplicates d.env)
        fun _ => return none
    let some found := found | continue
    let edit := do
      let term ← found.term
      let range ← d.proof
      return { range, newText := s!":= {term}" : Lsp.TextEdit }
    let rule := if found.duplicate then "duplicate" else "specialCase"
    let msg := message d.name found (visibleFrom k found.lemma)
    findings := findings.push
      { rule, message := msg, lemma := (sourceName found.lemma).toString, range := d.nameRange, edit }
  return { findings, skippedCommands := res.parseErrors, elabErrors := res.elabErrors }

/-- Options in `-Dname=value` form, typed the way `lean -D` types them for simple values. -/
def parseOption (opts : Options) (s : String) : Options :=
  match s.splitOn "=" with
  | [k, v] =>
    let name := k.toName
    if v == "true" then opts.setBool name true
    else if v == "false" then opts.setBool name false
    else match v.toNat? with
      | some n => opts.insert name (.ofNat n)
      | none => opts.insert name (.ofString v)
  | _ => opts

open System (FilePath)

private def optionsOf (args : Array String) : IO Options := do
  let opts := ({} : Options).setBool `Elab.async false |>.setBool `linter.all false
  let opts := opts.setBool `debug.skipKernelTC (← IO.getEnv "LEANPERF_FULL").isNone
  let opts := args.foldl (fun opts arg =>
    if arg.startsWith "-D" then parseOption opts (arg.drop 2).toString else opts) opts
  return opts.setBool `Elab.async false

private def baseEnv (job : Build.Job) (input : String) (opts : Options) : IO Environment := do
  let ctx := Parser.mkInputContext input job.source.toString
  let (header, _, msgs) ← Parser.parseHeader ctx
  let hdr : HeaderSyntax := header
  let (env, msgs) ← processHeaderCore hdr.startPos hdr.imports hdr.isModule opts msgs ctx
    (mainModule := job.mod) (arts := ← Build.artifactMap job.deps)
  for msg in msgs.toList do
    if msg.severity == .error then throw <| IO.userError (← msg.toString)
  return env

private abbrev Types := Array (Expr × Expr)

/-- Keep the exact expressions on disk. The workspace index needs only their hashes and ranges. -/
private def saveTypes (dir : FilePath) (env : Environment) (res : FileResult) (opts : Options) :
    IO (Array Build.Signature) := do
  let (sigs, types) ← runMeta env opts do
    let mut sigs := #[]
    let mut types : Types := #[]
    for d in res.decls do
      let ty := (← getConstInfo d.name).type
      let key ← canonical ty
      if key.hasFVar || key.hasMVar || key.hasLooseBVars then
        throwError "open canonical type for {d.name}"
      sigs := sigs.push { name := d.name, key := key.hash, range := d.nameRange : Build.Signature }
      types := types.push (key, normLevels (nameless ty))
    return (sigs, types)
  let _ ← unsafe CompactedRegion.save (dir / "types") (.str env.mainModule "types") types #[] none
  return sigs

private structure Context where
  imports : Array Import
  isModule : Bool
  deps : Array FilePath
  options : Array String
  base : Environment
  index : IO.Ref (Option ImportedIndex)
  proofIndex : IO.Ref (Option ProofCompression.Index)

private def worker (context : IO.Ref (Option Context)) (dir : FilePath) (query : Bool) : IO Unit := do
  let job : Build.Job ← Build.readJson (dir / "job.json")
  let req : Json ← if query then Build.readJson (dir / "request.json") else pure .null
  let input ← (req.getObjValAs? String "text").toOption.getDM (IO.FS.readFile job.source)
  if !(req.getObjVal? "text").isOk && hash input != job.sourceHash then
    throw <| IO.userError s!"{job.source} changed while planning the build"
  let checking := (req.getObjValAs? Bool "check").toOption.getD false
  let tactics := (req.getObjValAs? Bool "tactics").toOption.getD false
  let opts ← optionsOf job.options
  let opts := if checking then opts.setBool `debug.skipKernelTC false else opts
  let (header, _, _) ← Parser.parseHeader (Parser.mkInputContext input job.source.toString)
  let hdr : HeaderSyntax := header
  let deps := job.deps.map (·.dir)
  let cached := (← context.get).filter fun c => c.imports == hdr.imports &&
    c.isModule == hdr.isModule && c.deps == deps && c.options == job.options
  let ctx ← cached.getDM do
    let c := { imports := hdr.imports, isModule := hdr.isModule, deps, options := job.options,
               base := ← baseEnv job input opts, index := ← IO.mkRef none, proofIndex := ← IO.mkRef none : Context }
    context.set (some c)
    return c
  let base := ctx.base.setMainModule job.mod
  let enabled (name : String) := !job.options.contains ("--skip-lint=" ++ name)
  if tactics then
    let minSaving := (req.getObjValAs? Nat "minSaving").toOption.getD 1000
    let compress := (req.getObjValAs? Bool "compress").toOption.getD false
    let compression ← if compress && enabled "reuseProof" then do
        let idx ← (← ctx.proofIndex.get).getDM do
          let idx := ProofCompression.importIndex ctx.base
          ctx.proofIndex.set (some idx)
          return idx
        pure (some idx)
      else pure none
    let r ← Tactics.analyze base job.mod job.source.toString input opts minSaving
      (tactics := enabled "fasterTactic") (options := enabled "unneededOption")
      (shorter := (req.getObjValAs? Bool "shorter").toOption.getD false)
      (compression := compression)
      (signatures := compress && enabled "shorterSignature") (prune := compress && enabled "unusedHave")
    let findings := r.edits.map fun e =>
      { rule := e.rule, message := e.message, lemma := "", range := e.range
        edit := some { range := e.range, newText := e.newText } : Finding }
    IO.FS.writeFile (dir / "result.json")
      (toJson ({ findings, elabErrors := r.errors.size } : Report)).compress
    for e in r.errors do IO.eprintln s!"{job.source}: {e}"
    return
  let (env, res) ← elabSource base job.mod job.source.toString input opts (full := checking)
  if checking then
    IO.FS.writeFile (dir / "result.json") (Json.mkObj [
      ("errors", toJson res.messages), ("elabErrors", res.elabErrors)]).compress
    return
  if !query && res.parseErrors + res.elabErrors > 0 then
    throw <| IO.userError s!"{job.source}: incomplete skeleton\n{String.intercalate "\n" res.messages.toList}"
  let sigs ← saveTypes dir env res opts
  if !query then
    let p := dir / "module.olean"
    writeModule env p
    let final := job.dir / "module.olean"
    let parts : ImportArtifacts := if env.header.isModule then
      .ofArrays #[#[final, final.addExtension "server", final.addExtension "private"],
        #[final.withExtension "ir.sig", final.withExtension "ir"]]
      else .ofArrays #[#[final]]
    let manifest : Build.Manifest := { decls := sigs, deps := job.deps, parts }
    IO.FS.writeFile (dir / "info.json") (toJson manifest).compress
  else
    IO.FS.writeFile (dir / "decls.json") (toJson sigs).compress
  if query || job.requested then
    let mut r : Report := { skippedCommands := res.parseErrors, elabErrors := res.elabErrors }
    unless res.decls.isEmpty do
      let imports ← (← ctx.index.get).getDM do
        let idx ← importedIndex base (!job.options.contains "--no-general")
        ctx.index.set (some idx)
        return idx
      r ← report opts job.mod env res (!job.options.contains "--no-general") (enabled "duplicate") imports
    IO.FS.writeFile (dir / "result.json") (toJson r).compress

structure Entry where
  mod : Name
  decl : Build.Signature
  idx : Nat
  deriving Inhabited

structure Workspace where
  plan : Build.Plan
  cache : FilePath
  sigs : Std.HashMap Name (Array Build.Signature)
  index : Std.HashMap UInt64 (Array Entry)

private def prepare (root cache : FilePath) (files : Array FilePath) (opts : Array String)
    (workers : Nat) (tactics : Bool) : IO Workspace := do
  let plan ← Build.plan root cache files opts (dependenciesOnly := tactics)
  Build.build plan workers
  if tactics then return { plan, cache, sigs := {}, index := {} }
  let mut sigs := {}
  let mut index : Std.HashMap UInt64 (Array Entry) := {}
  for m in plan.order do
    let info : Build.Manifest ← Build.readJson (plan.jobs[m]!.dir / "info.json")
    sigs := sigs.insert m info.decls
    for h : i in [:info.decls.size] do
      let d := info.decls[i]
      index := index.alter d.key fun a => some <| (a.getD #[]).push ⟨m, d, i⟩
  return { plan, cache, sigs, index }

private def importsModule (p : Build.Plan) (mod target : Name) : Bool := Id.run do
  let mut todo := #[mod]
  let mut seen : Std.HashSet Name := {}
  while let some m := todo.back? do
    todo := todo.pop
    if seen.contains m then continue
    seen := seen.insert m
    if let some src := p.sources[m]? then
      if src.imports.contains target then return true
      todo := todo ++ src.imports
  return false

/-- Both mappings contain exactly the type written by saveTypes. Only booleans escape. -/
private unsafe def compareTypes (a : FilePath) (i : Nat) (b : FilePath) (j : Nat) :
    IO (Bool × Bool) := do
  let (xs, r) ← CompactedRegion.read (α := Types) (a / "types") #[]
  try
    let (ys, s) ← CompactedRegion.read (α := Types) (b / "types") #[]
    try
      let x := xs[i]!
      let y := ys[j]!
      return (x.1 == y.1, x.2 != y.2)
    finally s.free
  finally r.free

private unsafe def projectReport (w : Workspace) (m : Name) (dir : FilePath)
    (sigs : Array Build.Signature) (r : Report) : IO Report := do
  if w.plan.jobs[m]!.options.contains "--skip-lint=duplicate" then return r
  let mut findings := r.findings
  let reported := Std.HashSet.ofArray (r.findings.map fun f => (f.range.start.line, f.range.start.character))
  for h : i in [:sigs.size] do
    let d := sigs[i]
    if reported.contains (d.range.start.line, d.range.start.character) then continue
    let candidates := (w.index[d.key]?.getD #[]).qsort fun x y => x.decl.name.toString < y.decl.name.toString
    for e in candidates do
      if e.mod == m then continue
      if !isPrivateName e.decl.name && importsModule w.plan m e.mod then continue
      if !isPrivateName d.name && importsModule w.plan e.mod m then continue
      let (same, reordered) ← compareTypes dir i w.plan.jobs[e.mod]!.dir e.idx
      unless same do continue
      let match_ : Match := { lemma := e.decl.name, duplicate := true, reordered, term := none }
      findings := findings.push {
        rule := "duplicate", message := message d.name match_ false
        lemma := (sourceName e.decl.name).toString, range := d.range, edit := none }
      break
  return { r with findings := findings.qsort fun x y => x.range.start < y.range.start }

private unsafe def answer (slot : Build.Slot) (w : Workspace) (m : Name) (req : Json) : IO Json := do
  let job := w.plan.jobs[m]!
  let text := (req.getObjValAs? String "text").toOption
  if text.isNone && hash (← IO.FS.readFile job.source) != job.sourceHash then
    throw <| IO.userError s!"{job.source} changed after skeleton analysis"
  let saved := text.all (hash · == job.sourceHash)
  let resultFile := job.dir / "result.json"
  let checking := (req.getObjValAs? Bool "check").toOption.getD false
  let tactics := (req.getObjValAs? Bool "tactics").toOption.getD false
  let raw := checking || tactics
  -- A leaf may have no skeleton directory. Keep its tactic report independent of skeleton
  -- publication. The job key already covers the source, imports, options and executable.
  let minSaving := (req.getObjValAs? Nat "minSaving").toOption.getD 1000
  let shorter := (req.getObjValAs? Bool "shorter").toOption.getD false
  let compress := (req.getObjValAs? Bool "compress").toOption.getD false
  let tacticReport := w.cache / "tactics" / s!"{job.dir.fileName.get!}-{minSaving}-{shorter}-{compress}.json"
  let cacheTactics := tactics && !checking && saved
  if cacheTactics && (← tacticReport.pathExists) then return ← Build.readJson tacticReport
  if saved && !raw && (← resultFile.pathExists) then
    return toJson (← projectReport w m job.dir w.sigs[m]! (← Build.readJson resultFile))
  IO.FS.withTempDir fun dir => do
    IO.FS.writeFile (dir / "job.json") (toJson job).compress
    IO.FS.writeFile (dir / "request.json") req.compress
    -- Lean initializers run once per process. An unsaved buffer can change the imports even
    -- when it still has the same path and planned dependency artifacts.
    let headerKey ← if let some source := text.filter (fun _ => !saved) then do
        let (stx, _, _) ← Parser.parseHeader (Parser.mkInputContext source job.source.toString)
        let hdr : HeaderSyntax := stx
        pure (hash (hdr.isModule, hdr.imports))
      else pure job.headerKey
    Build.submit slot (hash (headerKey, job.options, job.deps.map (·.dir.toString))) dir true
    if raw then
      let result : Json ← Build.readJson (dir / "result.json")
      if cacheTactics && (result.getObjValAs? Nat "elabErrors").toOption == some 0 then
        IO.FS.createDirAll tacticReport.parent.get!
        let tmp := tacticReport.addExtension s!"tmp-{← IO.Process.getPID}"
        try
          IO.FS.writeFile tmp result.compress
          IO.FS.rename tmp tacticReport
        finally
          if ← tmp.pathExists then IO.FS.removeFile tmp
      return result
    let r : Report ← Build.readJson (dir / "result.json")
    if saved then
      -- This object was first built as a dependency. Publish its local report atomically.
      let tmp := job.dir / s!"report-{← IO.Process.getPID}.tmp"
      IO.FS.writeFile tmp (toJson r).compress
      IO.FS.rename tmp resultFile
    return toJson (← projectReport w m dir (← Build.readJson (dir / "decls.json")) r)

/-- Batch callers consume files in source order and can ask for a check immediately after each
    report. Keep at most one in-flight report per slot and reuse the just-finished worker to check
    the edited text in its initialized import environment. -/
private structure ReplayWindow where
  remaining : List Name
  idle : List Build.Slot
  pending : Std.HashMap Name (Build.Slot × Task (Except IO.Error Json)) := {}

private unsafe def replayAnswer (state : IO.Ref ReplayWindow) (fallback : Build.Slot)
    (w : Workspace) (m : Name) (req config : Json) : IO Json := do
  let mut q ← state.get
  if (req.getObjValAs? Bool "check").toOption.getD false then
    return ← answer (q.idle.headD fallback) w m req
  while let slot :: slots := q.idle do
    let next :: rest := q.remaining | break
    let task ← BaseIO.asTask ((answer slot w next config).toBaseIO) .dedicated
    q := { remaining := rest, idle := slots, pending := q.pending.insert next (slot, task) }
  state.set q
  let some (slot, task) := q.pending[m]? | return ← answer fallback w m req
  let result ← IO.wait task
  state.set { q with idle := slot :: q.idle, pending := q.pending.erase m }
  -- A snapshot can change between planning and a request. Reuse a prefetched report only for
  -- the exact source it analyzed. The ordinary path handles a new buffer or a changed file.
  let job := w.plan.jobs[m]!
  let text ← (req.getObjValAs? String "text").toOption.getDM (IO.FS.readFile job.source)
  if hash text != job.sourceHash then return ← answer slot w m (req.setObjVal! "text" text)
  IO.ofExcept result

end LeanPerf.Dedup

open LeanPerf LeanPerf.Dedup in
/-- The skeleton builder and elaborated passes: `--project`, `--configured` and `--worker-loop`. -/
unsafe def LeanPerf.Dedup.run (args : List String) : IO UInt32 := do
  if args == ["--help"] then
    IO.println "leanperf-dedup --project [--jobs=N] [--build-only | --shorter] PATH...
Run from the target Lake project. Reports checked proof terms and their locations."
    return 0
  if let "--project" :: rest := args then return ← Project.launch rest
  initSearchPath (← findSysroot)
  enableInitializersExecution
  if args == ["--worker-loop"] then
    let ctx ← IO.mkRef none
    let stdin ← IO.getStdin
    let stdout ← IO.getStdout
    repeat
      let line ← stdin.getLine
      if line.trimAscii.isEmpty then break
      let reply ← try
        let req ← IO.ofExcept (Json.parse line)
        let dir ← IO.ofExcept (req.getObjValAs? System.FilePath "dir")
        let query ← IO.ofExcept (req.getObjValAs? Bool "query")
        IO.withStdout (← IO.getStderr) (worker ctx dir query)
        pure Json.null
      catch e => pure (Json.mkObj [("error", toString e)])
      stdout.putStrLn reply.compress
      stdout.flush
    return 0
  let cmd :: rest := args | throw <| IO.userError "expected --project or a source root"
  let (root, defaults) ← if cmd == "--configured" then Project.settings else pure (cmd, #[])
  let root ← IO.FS.realPath root
  let batch := cmd == "--configured" && !rest.contains "--serve"
  let buildOnly := rest.contains "--build-only"
  let compress := rest.contains "--compress"
  let shorter := compress || rest.contains "--shorter"
  let tactics := compress || rest.contains "--tactics"
  let mut minSaving := 1000
  let cache : System.FilePath := (← IO.getEnv "LEANPERF_CACHE_DIR").map System.FilePath.mk
    |>.getD ((← IO.currentDir) / ".lake" / "leanperf")
  let mut options := defaults
  let mut files : Array System.FilePath := #[]
  let mut workers := (← IO.getEnv "LEANPERF_JOBS").getD "2"
  for a in rest do
    if ["--serve", "--batch-replay", "--build-only", "--shorter", "--tactics", "--compress"].contains a then continue
    if let some n := a.dropPrefix? "--min-saving=" then
      minSaving := (n.toString.toNat?.getD 1) * 1000
      continue
    if a.startsWith "-D" || a == "--no-general" || a.startsWith "--skip-lint=" then options := options.push a
    else if let some n := a.dropPrefix? "--jobs=" then workers := n.toString
    else if let some p := a.dropPrefix? "--file-list=" then
      let paths : Array System.FilePath ← Build.readJson p.toString
      files := files ++ (← paths.mapM (IO.FS.realPath ·))
    else if a.startsWith "--" then throw <| IO.userError s!"unknown option {a}"
    else files := files.push a
  let some jobs := workers.toNat? | throw <| IO.userError "jobs must be a positive integer"
  if jobs == 0 then throw <| IO.userError "jobs must be a positive integer"
  if batch && files.isEmpty then throw <| IO.userError "supply a Lean file or directory"
  files ← Project.files files
  if buildOnly then
    let p ← Build.plan root cache files options
    Build.build { p with jobs := p.jobs.map fun _ j => { j with requested := false } } jobs
    return 0
  let mut world ← prepare root cache files options jobs tactics
  let slot ← IO.mkRef none
  let tacticConfig := Json.mkObj [("tactics", true), ("minSaving", minSaving),
    ("shorter", shorter), ("compress", compress)]
  if batch && tactics then
    let mut failed := 0
    for path in files do
      let m := Build.moduleOf root path
      let req := tacticConfig.setObjVal! "path" path.toString
      let r : Report ← IO.ofExcept (fromJson? (← answer slot world m req))
      for f in r.findings do
        IO.println s!"{path}:{f.range.start.line + 1}:{f.range.start.character + 1}: {f.rule}: {f.message}"
      if r.elabErrors > 0 then
        failed := failed + 1
        IO.eprintln s!"{path}: {r.elabErrors} commands failed to elaborate; edits there are not suggested"
    Build.stop slot
    return if failed > 0 then 1 else 0
  if batch then
    for path in files do
      let m := Build.moduleOf root path
      let req := Json.mkObj [("path", path.toString)]
      let r : Report ← IO.ofExcept (fromJson? (← answer slot world m req))
      let file := FileMap.ofString (← IO.FS.readFile path)
      for f in r.findings do
        let replacement := f.edit.map fun e => e.newText
        if shorter then
          let some e := f.edit | continue
          let old := file.lspRangeToUtf8Range e.range
          if e.newText.utf8ByteSize >= old.stop.byteIdx - old.start.byteIdx then continue
        IO.println s!"{path}:{f.range.start.line + 1}:{f.range.start.character + 1}: {f.rule}: {f.message}"
        if let some term := replacement then IO.println s!"  {term}"
    Build.stop slot
    return 0
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let parallel := rest.contains "--batch-replay" && tactics && files.size > 1 && jobs > 1
  let slots ← (List.range (if parallel then min jobs files.size else 0)).mapM fun _ => IO.mkRef none
  let window ← IO.mkRef { remaining := files.toList.map (Build.moduleOf root), idle := slots : ReplayWindow }
  try
    repeat
      let line ← stdin.getLine
      if line.isEmpty then break
      let reply ← try
        let req ← IO.ofExcept (Json.parse line)
        let path ← IO.FS.realPath (← IO.ofExcept (req.getObjValAs? String "path"))
        let m := Build.moduleOf root path
        unless world.plan.jobs.contains m do
          files := files.push path
          world ← prepare root cache files options jobs tactics
        let req := if tactics && !(req.getObjValAs? Bool "check").toOption.getD false then
          req.mergeObj tacticConfig
          else req
        if parallel then replayAnswer window slot world m req tacticConfig else answer slot world m req
      catch e => pure (Json.mkObj [("error", toString e)])
      stdout.putStrLn reply.compress
      stdout.flush
  finally
    for (_, (_, t)) in (← window.get).pending do discard <| IO.wait t
    for s in slot :: slots do Build.stop s
  return 0
