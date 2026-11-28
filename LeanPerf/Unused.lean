import LeanPerf.SyntaxDedup

/-!
# Theorems that nothing mentions

A project-wide pass over source text, which needs nothing built and runs no Lean. It removes the
lemmas that contributors to the Riemann development deleted by hand in hundreds of commits titled
"remove unused …".

A used command, or a comment in it, uses a theorem when it mentions the theorem by a name that
Lean would resolve there: the name itself, or the name relative to an enclosing namespace, an
opened namespace, or the namespace of the declaration being made. A mention that resolves to no
declaration of the project, such as `h.foo` with a local `h`, could be field notation for any
`….foo`, so it uses every theorem whose last name component is `foo`. Uses are overestimated,
so a mistake keeps a theorem rather than deleting a used one. The commands every analysis starts
from are

* every command that is not a theorem: definitions, instances, notation, `attribute` and so on,
* every theorem with an attribute, which tactics or generated names can use without spelling it,
* every theorem in a module that no other project module imports, such as the main theorems.

A theorem that no command reached from these mentions is unused. It is deleted only together
with every unused theorem that mentions it, so analyzing some files never breaks another one.
-/

open Lean System

namespace LeanPerf.Unused

open SyntaxDedup (blankComments tokenize commandStarts stripModifiers headerImports moduleName lspPos isIdent)

/-- First words of a line that starts a command. A line at the left margin that starts with
    another word, such as `termination_by` or a proof step, continues the previous command. -/
def commandWords : Std.HashSet String := Std.HashSet.ofList [
  "theorem", "lemma", "def", "abbrev", "instance", "structure", "class", "inductive",
  "coinductive", "example", "axiom", "opaque", "noncomputable", "private", "protected", "public",
  "partial", "unsafe", "nonrec", "namespace", "section", "end", "open", "export", "variable",
  "universe", "set_option", "attribute", "local", "scoped", "macro", "macro_rules", "syntax",
  "notation", "infix", "infixl", "infixr", "prefix", "postfix", "elab", "elab_rules",
  "declare_syntax_cat", "initialize", "builtin_initialize", "mutual", "deriving", "omit",
  "include", "alias", "irreducible_def", "register_simp_attr", "add_decl_doc", "library_note",
  "suppress_compilation", "seal", "unseal", "compile_inductive", "run_cmd", "import", "module",
  "meta", "assert_not_exists", "simproc", "dsimproc", "grind_pattern", "binder_predicate",
  "unif_hint", "noncomputable", "recall", "lemma"]

/-- Comments as `(start, stop, module doc)` code-point intervals. -/
def comments (s : Array Char) : Array (Nat × Nat × Bool) := Id.run do
  let n := s.size
  let mut out := #[]
  let mut i := 0
  while i < n do
    let c := s[i]!
    let next := s[i+1]?.getD ' '
    if c == '-' && next == '-' then
      let mut j := i
      while j < n && s[j]! != '\n' do j := j + 1
      out := out.push (i, j, false)
      i := j
    else if c == '/' && next == '-' then
      let mut depth := 1
      let mut j := i + 2
      while j < n && depth > 0 do
        if s[j]! == '/' && s[j+1]?.getD ' ' == '-' then depth := depth + 1; j := j + 2
        else if s[j]! == '-' && s[j+1]?.getD ' ' == '/' then depth := depth - 1; j := j + 2
        else j := j + 1
      out := out.push (i, j, s[i+2]?.getD ' ' == '!')
      i := j
    else if c == '"' then
      let mut j := i + 1
      while j < n && s[j]! != '"' do j := j + (if s[j]! == '\\' then 2 else 1)
      i := j + 1
    else i := i + 1
  return out

/-- The components of an identifier, `Foo.«bar.baz»` giving `Foo` and `bar.baz`. -/
def components (t : String) : Array String := Id.run do
  let mut out := #[]
  let mut cur := ""
  let mut quoted := false
  for c in t.toList do
    if c == '«' then quoted := true
    else if c == '»' then quoted := false
    else if c == '.' && !quoted then
      unless cur.isEmpty do out := out.push cur
      cur := ""
    else cur := cur.push c
  unless cur.isEmpty do out := out.push cur
  return out

/-- The last name components of the identifiers that `text` applies with `@`, which pass
    arguments by position. -/
def explicitlyApplied (text : String) : Array String := Id.run do
  let s := blankComments text.toList.toArray
  let toks := tokenize s
  let mut out := #[]
  for h : i in [1:toks.size] do
    if toks[i-1]!.1 == "@" then
      if let some c := (components toks[i].1).back? then out := out.push c
  return out

/-- A command with the modifier and `… in` lines in front of it. -/
structure Command where
  /-- The start of the comments directly above it, except module documentation. -/
  lead : Nat
  /-- After the newline that ends its last line, and one following blank line if one precedes it. -/
  stop : Nat
  /-- The last name component of an unattributed theorem. -/
  «theorem» : Option String
  name : String
  /-- The full name of the declaration it makes, or `""`. -/
  full : String := ""
  /-- The namespaces a name in it resolves in, innermost first, ending with the root `""`. -/
  bases : Array String := #[""]
  /-- The identifiers it mentions, comments included; `.foo` for a leading-dot name. -/
  idents : Array String := #[]
  deriving Inhabited

structure File where
  path : FilePath
  module : String
  imports : Array String
  commands : Array Command
  /-- What the text between commands mentions. -/
  free : Array String
  deriving Inhabited

/-- The identifiers that `s[a:b]` mentions, comments included, with `.foo` for a name written
    after a dot that ends no identifier. -/
def identsIn (s : Array Char) (a b : Nat) : Array String := Id.run do
  let toks := tokenize s a b
  let mut out := #[]
  for h : i in [:toks.size] do
    let (t, p) := toks[i]
    unless isIdent t do continue
    let dotted := i > 0 && toks[i-1]!.1 == "." && toks[i-1]!.2 + 1 == p
    out := out.push (if dotted then "." ++ t else t)
  return out

/-- The declaration keywords whose next word is the declared name. -/
def declWords : List String :=
  ["theorem", "lemma", "def", "abbrev", "instance", "structure", "class", "inductive",
   "coinductive", "axiom", "opaque", "irreducible_def", "alias"]

/-- `A.B` and its prefixes, innermost first. -/
private def prefixes (ns : String) : Array String := Id.run do
  let cs := components ns
  let mut out := #[]
  for k in (List.range cs.size).reverse do
    out := out.push (".".intercalate (cs.extract 0 (k + 1)).toList)
  return out

def parse (path : FilePath) (module text : String) : File := Id.run do
  let raw := text.toList.toArray
  let s := blankComments raw
  let notes := comments raw
  let starts := (commandStarts s).filter fun a =>
    let toks := tokenize s a (min s.size (a + 64))
    match toks[0]? with
    | some (t, _) => t == "@" || t.startsWith "#" || commandWords.contains t
    | none => false
  let mut commands := #[]
  let mut i := 0
  let mut noteIdx := 0
  -- Each open scope: its namespace, if it is one, and what was opened in it.
  let mut scopes : Array (Option String × Array String) := #[(none, #[])]
  while i < starts.size do
    -- Attribute, modifier and `… in` lines belong to the command after them.
    let mut j := i
    while j + 1 < starts.size do
      let toks := tokenize s starts[j]! starts[j+1]!
      if !toks.isEmpty && (stripModifiers (toks.map (·.1))).1.isEmpty then j := j + 1 else break
    let a := starts[i]!
    let b := starts[j+1]?.getD s.size
    i := j + 1
    let toks := tokenize s a b
    let (words, _) := stripModifiers (toks.map (·.1))
    let prefix_ := (toks.extract 0 (toks.size - words.size)).map (·.1)
    let attributed := prefix_.any (· == "@")
    let ns := ".".intercalate (scopes.filterMap (·.1)).toList
    let opened := scopes.foldl (fun acc sc => acc ++ sc.2) #[]
    -- `open A B in` opens for this command only.
    let localOpens := Id.run do
      let mut out := #[]
      let mut inOpen := false
      for t in prefix_ do
        if t == "open" then inOpen := true
        else if t == "in" then inOpen := false
        else if inOpen && isIdent t && !["scoped", "hiding", "renaming"].contains t then out := out.push t
      return out
    match words[0]? with
    | some "namespace" => if let some n := words[1]? then scopes := scopes.push (some n, #[])
    | some "section" => scopes := scopes.push (none, #[])
    | some "end" => if scopes.size > 1 then scopes := scopes.pop
    | some "open" =>
      let names := (words.extract 1 words.size).filter fun t =>
        isIdent t && !["scoped", "hiding", "renaming"].contains t
      scopes := scopes.modify (scopes.size - 1) fun (n, os) => (n, os ++ names)
    | _ => pure ()
    let declared := match words[0]?, words[1]? with
      | some w, some n => if declWords.contains w && isIdent n then n else ""
      | _, _ => ""
    let full := if declared.isEmpty then "" else
      match declared.dropPrefix? "_root_." with
      | some rest => rest.toString
      | none => if ns.isEmpty then declared else ns ++ "." ++ declared
    -- The body of `theorem A.foo` also resolves names in `A`.
    let own := match (components full).pop with
      | cs => if cs.isEmpty then #[] else prefixes (".".intercalate cs.toList)
    let bases := own ++ (if ns.isEmpty then #[] else prefixes ns) ++ opened ++ localOpens ++ #[""]
    let name := if words.size > 1 && (words[0]! == "theorem" || words[0]! == "lemma") then words[1]! else ""
    let thm := if name.isEmpty || attributed then none else (components name).back?
    -- The command's text ends at its last character outside a comment.
    let mut e := b
    while e > a && s[e-1]!.isWhitespace do e := e - 1
    let mut stop := e
    while stop < s.size && s[stop]! != '\n' do stop := stop + 1
    if stop < s.size then stop := stop + 1
    -- Comments directly above, with no blank line between, document the command.
    while noteIdx < notes.size && notes[noteIdx]!.2.1 ≤ a do noteIdx := noteIdx + 1
    let mut lead := a
    let mut k := noteIdx
    while k > 0 do
      let (cs, ce, moduleDoc) := notes[k-1]!
      if moduleDoc || ce > lead then break
      let gap := (raw.extract ce lead).toList
      if gap.any (!·.isWhitespace) || gap.count '\n' > 1 then break
      let mut ls := cs
      while ls > 0 && raw[ls-1]! != '\n' do ls := ls - 1
      if (raw.extract ls cs).any (!·.isWhitespace) then break
      lead := ls
      k := k - 1
    -- Keep one blank line between the neighbours of a deleted command.
    if lead ≥ 2 && raw[lead-1]! == '\n' && raw[lead-2]! == '\n' && stop < raw.size && raw[stop]! == '\n' then
      stop := stop + 1
    commands := commands.push { lead, stop, «theorem» := thm, name, full, bases, idents := identsIn raw lead stop }
  -- Text outside every command, such as module documentation, is a root.
  let mut cursor := 0
  let mut free : Array String := #[]
  for c in commands do
    free := free ++ identsIn raw cursor (max cursor c.lead)
    cursor := max cursor c.stop
  free := free ++ identsIn raw cursor raw.size
  return { path, module, imports := headerImports text, commands, free }

/-- A finding for an unused theorem, with the edit that deletes it. -/
structure Finding where
  name : String
  range : Lsp.Range
  deriving Inhabited

/-- Whether the declaration named `full` is `root`: by its full name or a suffix of its components. -/
def names (full root : String) : Bool := full == root || full.endsWith ("." ++ root)

/-- Unused theorems of the `targets`, among all project `files`. With `roots`, the theorems that
    count as used are those that the named theorems use, directly or through others, rather than
    every theorem of a module that no other module imports; text between declarations, such as
    module documentation, then uses nothing. Commands that are not theorems stay roots either way:
    a tactic can use an instance or a `simp` set without naming it. -/
def analyze (files : Array File) (targets : Std.HashSet String) (roots : Array String := #[]) :
    Std.HashMap String (Array (Nat × Command)) := Id.run do
  let imported := files.foldl (init := ({} : Std.HashSet String)) fun acc f => acc.insertMany f.imports
  -- Theorems by last name component.
  let mut byName : Std.HashMap String (Array (Nat × Nat)) := {}
  for h : fi in [:files.size] do
    for h' : ci in [:files[fi].commands.size] do
      if let some n := files[fi].commands[ci].«theorem» then
        byName := byName.alter n fun xs => some ((xs.getD #[]).push (fi, ci))
  -- Every declaration by full name, to tell a resolved mention from field notation.
  let mut known : Std.HashMap String (Array (Nat × Nat)) := {}
  for h : fi in [:files.size] do
    for h' : ci in [:files[fi].commands.size] do
      let c := files[fi].commands[ci]
      unless c.full.isEmpty do
        known := known.alter c.full fun xs => some ((xs.getD #[]).push (fi, ci))
  let isTheorem (x : Nat × Nat) : Bool := (files[x.1]!.commands[x.2]!).«theorem».isSome
  -- The theorems that identifier `t` can name in a command that resolves names in `bases`.
  let resolve (bases : Array String) (t : String) : Array (Nat × Nat) := Id.run do
    let cs := components t
    let byLast (from_ : Nat) := (cs.extract from_ cs.size).foldl (fun acc c => acc ++ (byName[c]?.getD #[])) #[]
    if t.startsWith "." then return byLast 0
    for k in (List.range cs.size).reverse do
      let head := ".".intercalate (cs.extract 0 (k + 1)).toList
      let mut hit := #[]
      for b in bases do
        if let some xs := known[if b.isEmpty then head else b ++ "." ++ head]? then hit := hit ++ xs
      -- The rest of the identifier is field notation on what the head names.
      unless hit.isEmpty do return hit.filter isTheorem ++ byLast (k + 1)
    return byLast 0
  let refs (fi ci : Nat) : Array (Nat × Nat) :=
    let c := files[fi]!.commands[ci]!
    c.idents.foldl (fun acc t => acc ++ resolve c.bases t) #[]
  let isRoot (f : File) (c : Command) := c.«theorem».isNone ||
    (if roots.isEmpty then !imported.contains f.module else roots.any (names c.full))
  let mut seen : Std.HashSet (Nat × Nat) := {}
  let mut stack := #[]
  for h : fi in [:files.size] do
    for h' : ci in [:files[fi].commands.size] do
      if isRoot files[fi] files[fi].commands[ci] then
        seen := seen.insert (fi, ci)
        stack := stack.push (fi, ci)
  let mut frontier : Array (Nat × Nat) := if !roots.isEmpty then #[] else
    files.foldl (init := #[]) fun acc f => f.free.foldl (fun acc t => acc ++ resolve #[""] t) acc
  repeat
    for x in frontier do
      unless seen.contains x do
        seen := seen.insert x
        stack := stack.push x
    let some (fi, ci) := stack.back? | break
    stack := stack.pop
    frontier := refs fi ci
  -- Delete a theorem only together with every unused theorem that mentions it.
  let unused := byName.fold (init := #[]) fun acc _ xs => acc ++ xs.filter (!seen.contains ·)
  let mut chosen : Std.HashSet (Nat × Nat) :=
    Std.HashSet.ofArray (unused.filter fun (fi, _) => targets.contains files[fi]!.path.toString)
  repeat
    let mut dropped := false
    for (fi, ci) in unused do
      if chosen.contains (fi, ci) then continue
      for x in refs fi ci do
        if chosen.contains x && x != (fi, ci) then
          chosen := chosen.erase x
          dropped := true
    unless dropped do break
  let mut out : Std.HashMap String (Array (Nat × Command)) := {}
  for (fi, ci) in chosen.toArray.qsort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)) do
    let f := files[fi]!
    out := out.alter f.path.toString fun xs => some ((xs.getD #[]).push (ci, f.commands[ci]!))
  return out

end LeanPerf.Unused
