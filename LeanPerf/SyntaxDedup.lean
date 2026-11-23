import Lean.Data.Lsp.Basic
import Std.Data.HashMap

/-!
# Restated theorems from source text alone

Nothing is built and no Lean code runs. A statement's key is its token sequence with binder names
replaced by positions and its binders in a canonical order, as the elaborated pass canonicalizes
`Expr`s. Equal spelling is weaker evidence than equal elaborated statements: names resolve through
`open` and namespaces, and notation through imports. A match is a likely restatement, and a
difference in spelling hides one.

Positions inside this module are code-point offsets into an `Array Char`.
-/

open Lean System

namespace LeanPerf.SyntaxDedup

abbrev Toks := Array String

def pairs : List (String × String) :=
  [("(", ")"), ("{", "}"), ("[", "]"), ("⦃", "⦄"), ("⟨", "⟩")]
def isOpen (t : String) : Bool := pairs.any (·.1 == t)
def isClose (t : String) : Bool := pairs.any (·.2 == t)
/-- Tokens after which identifiers are bound, up to `,` (or `=>`, `↦`). -/
def binderToks : List String :=
  ["∀", "∃", "∃!", "∀ᶠ", "∃ᶠ", "fun", "λ", "Σ", "Π", "∑", "∏", "⋃", "⋂", "⨆", "⨅"]
/-- `∀ x ∈ s, p x`: a binder predicate ends the names. -/
def predicates : List String := ["∈", "∉", "<", ">", "≤", "≥", "≠", "⊆", "⊂", "⊇", "⊃", "in"]
def modifiers : List String :=
  ["private", "protected", "noncomputable", "nonrec", "partial", "unsafe", "scoped", "local"]

/-! ## Characters and tokens -/

def isSuper (c : Char) : Bool :=
  let n := c.toNat
  (0x2B0 ≤ n && n ≤ 0x2FF) || (0x1D2C ≤ n && n ≤ 0x1D61) || (0x1D9C ≤ n && n ≤ 0x1DBF) ||
  (0x2070 ≤ n && n ≤ 0x207F)

/-- Characters that are part of words, including those Lean does not allow in identifiers. -/
def isWord (c : Char) : Bool :=
  c.isAlphanum || c == '_' || isLetterLike c || isSubScriptAlnum c || isSuper c

def isIdentStart (c : Char) : Bool := isIdFirst c && !isSuper c
def isIdentPart (c : Char) : Bool := isIdRest c && !isSuper c
def binderChars : List Char := ['∀', '∃', 'λ', 'Π', 'Σ', '∑', '∏', '⋃', '⋂', '⨆', '⨅']
def bracketChars : List Char := ['(', ')', '[', ']', '{', '}', '⦃', '⦄', '⟨', '⟩']

def str (s : Array Char) (i j : Nat) : String := (s.extract i j).foldl String.push ""

/-- Replace comments and the contents of string literals with spaces, keeping every offset. -/
def blankComments (s : Array Char) : Array Char := Id.run do
  let n := s.size
  let mut out := s
  let mut i := 0
  let blank (out : Array Char) (a b : Nat) : Array Char := Id.run do
    let mut o := out
    for k in [a:min b n] do
      if o[k]! != '\n' then o := o.set! k ' '
    return o
  while i < n do
    let c := s[i]!
    let next := s[i+1]?.getD ' '
    if c == '-' && next == '-' then
      let mut j := i
      while j < n && s[j]! != '\n' do j := j + 1
      out := blank out i j
      i := j
    else if c == '/' && next == '-' then
      let mut depth := 1
      let mut j := i + 2
      while j < n && depth > 0 do
        if s[j]! == '/' && s[j+1]?.getD ' ' == '-' then depth := depth + 1; j := j + 2
        else if s[j]! == '-' && s[j+1]?.getD ' ' == '/' then depth := depth - 1; j := j + 2
        else j := j + 1
      out := blank out i j
      i := j
    else if c == '"' then
      -- Blank the contents but keep the quotes, so a string still separates tokens.
      let mut j := i + 1
      while j < n && s[j]! != '"' do j := j + (if s[j]! == '\\' then 2 else 1)
      out := blank out (i + 1) j
      i := j + 1
    else i := i + 1
  return out

/-- (token, offset) pairs of `s[start:stop]`. -/
def tokenize (s : Array Char) (start : Nat := 0) (stop : Nat := s.size) : Array (String × Nat) := Id.run do
  let mut out := #[]
  let mut i := start
  let at_ (k : Nat) : Char := if k < stop then s[k]! else ' '
  -- An identifier component: `«…»` or a start character followed by parts.
  let comp (k : Nat) : Option Nat := Id.run do
    if at_ k == '«' then
      let mut j := k + 1
      while j < stop && s[j]! != '»' && s[j]! != '\n' do j := j + 1
      return if at_ j == '»' then some (j + 1) else none
    if !isIdentStart (at_ k) then return none
    let mut j := k + 1
    while j < stop && isIdentPart s[j]! do j := j + 1
    return some j
  while i < stop do
    let c := s[i]!
    if c.isWhitespace then i := i + 1; continue
    if let some j := comp i then
      let mut e := j
      repeat
        if at_ e != '.' then break
        if let some j' := comp (e + 1) then e := j'
        else if (at_ (e + 1)).isDigit then
          let mut d := e + 1
          while d < stop && s[d]!.isDigit do d := d + 1
          e := d
        else break
      out := out.push (str s i e, i)
      i := e
      continue
    if c.isDigit then
      let mut j := i
      while j < stop && s[j]!.isDigit do j := j + 1
      if at_ j == '.' && (at_ (j + 1)).isDigit then
        j := j + 1
        while j < stop && s[j]!.isDigit do j := j + 1
      while j < stop && isWord s[j]! do j := j + 1
      out := out.push (str s i j, i)
      i := j
      continue
    if (c == '∀' || c == '∃') && at_ (i + 1) == 'ᶠ' then
      out := out.push (str s i (i + 2), i); i := i + 2; continue
    if c == '∃' && at_ (i + 1) == '!' then
      out := out.push (str s i (i + 2), i); i := i + 2; continue
    if binderChars.contains c || bracketChars.contains c then
      out := out.push (c.toString, i); i := i + 1; continue
    if c == ':' && at_ (i + 1) == '=' then
      out := out.push (":=", i); i := i + 2; continue
    if c == ',' || c == ':' then
      out := out.push (c.toString, i); i := i + 1; continue
    let symChar (d : Char) : Bool := !d.isWhitespace && !isWord d && d != '«' &&
      !bracketChars.contains d && d != ',' && d != ':' && !binderChars.contains d
    if symChar c then
      let mut j := i
      while j < stop && symChar s[j]! do j := j + 1
      out := out.push (str s i j, i)
      i := j
      continue
    out := out.push (c.toString, i)
    i := i + 1
  return out

def isIdent (t : String) : Bool :=
  match t.toList with
  | c :: _ => (c == '«' || isIdentStart c) && !binderToks.contains t && t != "fun"
  | [] => false

/-- Index of the first token in `stops` outside brackets. -/
def splitDepth0 (ts : Toks) (stops : List String) : Option Nat := Id.run do
  let mut depth : Int := 0
  for h : i in [:ts.size] do
    let t := ts[i]
    if depth == 0 && stops.contains t then return some i
    if isOpen t then depth := depth + 1
    else if isClose t then depth := depth - 1
  return none

/-- Index of the bracket closing `ts[i]`. -/
def matching (ts : Toks) (i : Nat) : Nat := Id.run do
  let mut depth : Int := 0
  for j in [i:ts.size] do
    if isOpen ts[j]! then depth := depth + 1
    else if isClose ts[j]! then
      depth := depth - 1
      if depth == 0 then return j
  return ts.size - 1

abbrev Binder := Option String × Option Toks

/-- Binders `(a b : T)`, `{a}`, `[C a]`, `x` as (name, type) pairs. -/
def binderGroups (ts : Toks) : Option (Array Binder) := Id.run do
  let mut out : Array Binder := #[]
  let mut i := 0
  while i < ts.size do
    let t := ts[i]!
    if isOpen t && t != "⟨" then
      let j := matching ts i
      let mut inner := ts.extract (i + 1) j
      if t == "{" && inner[0]? == some "{" then inner := inner.extract 1 (inner.size - 1)
      match splitDepth0 inner [":"] with
      | none =>
        if t == "[" then out := out.push (none, some inner)
        else
          for n in inner do
            if isIdent n || n == "_" then out := out.push (some n, none)
      | some colon =>
        let names := inner.extract 0 colon
        let ty := inner.extract (colon + 1) inner.size
        let ty := match splitDepth0 ty [":="] with | some d => ty.extract 0 d | none => ty
        if t == "[" then out := out.push (names[0]?, some ty)
        else for n in names do out := out.push (some n, some ty)
      i := j + 1
    else if isIdent t || t == "_" then
      out := out.push (some t, none)
      i := i + 1
    else return none
  return some out

/-- Leading `∀ binders,` and `A →` of a type as binders, the way Lean's telescope opens them. -/
def flatten (ty : Toks) : Array Binder × Toks := Id.run do
  let mut bs : Array Binder := #[]
  let mut ty := ty
  while ty.size > 0 do
    if ty[0]! == "∀" then
      let some comma := splitDepth0 ty [","] | break
      let head := ty.extract 1 comma
      if (splitDepth0 head predicates).isSome then break
      let colon := splitDepth0 head [":"]
      let group := if colon.isSome && !(head.size > 0 && isOpen head[0]!) then
        binderGroups (#["("] ++ head ++ #[")"]) else binderGroups head
      let some g := group | break
      bs := bs ++ g
      ty := ty.extract (comma + 1) ty.size
      continue
    -- Lower-precedence operators than `→` make the arrow part of an operand.
    if (splitDepth0 ty ["↔", "<|", "$", "|>", "|>.", "=>"]).isSome then break
    let some arrow := splitDepth0 ty ["→"] | break
    if arrow == 0 || (splitDepth0 (ty.extract 0 arrow) (binderToks ++ ["fun"])).isSome then break
    bs := bs.push (none, some (ty.extract 0 arrow))
    ty := ty.extract (arrow + 1) ty.size
  return (bs, ty)

/-- `#b<binder>@<depth><suffix>`: a reference to a telescope binder before reordering. -/
def topRef? (t : String) : Option (Nat × Nat × String) := do
  let r ← t.dropPrefix? "#b"
  let r := r.toString
  let [k, rest] := r.splitOn "@" | none
  let k ← k.toNat?
  let digits := (rest.takeWhile Char.isDigit).toString
  let d ← digits.toNat?
  let suffix := (rest.drop digits.length).toString
  unless suffix.isEmpty || (suffix.startsWith "." && suffix.length > 1) do none
  return (k, d, suffix)

/-- Resolve the binders the syntax pass recognizes. Index zero is the nearest binder. -/
partial def resolve (ts : Toks) (env : Std.HashMap String Nat) (enclosing : Array (Option String) := #[]) :
    Toks := Id.run do
  let mut out : Toks := #[]
  let mut scopes : Array (Int × Nat) := #[]
  let mut depth : Int := 0
  let mut bound := enclosing
  let delimiters := [",", "=>", "↦", "|"]
  let mut i := 0
  while i < ts.size do
    let t := ts[i]!
    -- For a semicolon-delimited let, the variable enters scope after its value.
    if t == "let" && i + 2 < ts.size && isIdent ts[i+1]! then
      if let some eq := splitDepth0 (ts.extract (i + 2) ts.size) [":=", ";"] then
        let eq := eq + i + 2
        if let some e := splitDepth0 (ts.extract (eq + 1) ts.size) [";"] then
          if ts[eq]! == ":=" && (eq == i + 2 || ts[i+2]! == ":") then
            let e := e + eq + 1
            out := out ++ #["let", "#bind"] ++ resolve (ts.extract (i + 2) eq) env bound ++ #[":="]
            out := out ++ resolve (ts.extract (eq + 1) e) env bound
            out := out.push ";"
            scopes := scopes.push (depth, bound.size)
            bound := bound.push (some ts[i+1]!)
            i := e + 1
            continue
    let setbuilder := t == "{" && i + 2 < ts.size && isIdent ts[i+1]! && (ts[i+2]! == "|" || ts[i+2]! == ":")
    if binderToks.contains t || setbuilder then
      out := out.push t
      if setbuilder then depth := depth + 1
      scopes := scopes.push (depth, bound.size)
      i := i + 1
      let mut pending : Array (Option String) := #[]
      while i < ts.size && !delimiters.contains ts[i]! do
        let tk := ts[i]!
        if isOpen tk then
          bound := bound ++ pending
          pending := #[]
          let j := matching ts i
          let inner := ts.extract (i + 1) j
          let colon := splitDepth0 inner [":"]
          if tk == "[" && colon.isNone then
            out := out ++ #[tk] ++ resolve inner env bound ++ #[ts[j]!]
            bound := bound.push none
            i := j + 1
            continue
          let names := match colon with | some c => inner.extract 0 c | none => inner
          out := out.push tk
          out := out ++ names.map fun n => if isIdent n || n == "_" then "#bind" else n
          if let some c := colon then
            out := out.push ":"
            out := out ++ resolve (inner.extract (c + 1) inner.size) env bound
          out := out.push ts[j]!
          for n in names do
            if isIdent n then bound := bound.push (some n)
            else if n == "_" then bound := bound.push none
          i := j + 1
        else if (isIdent tk || tk == "_") && !predicates.contains tk then
          pending := pending.push (if tk == "_" then none else some tk)
          out := out.push "#bind"
          i := i + 1
        else
          -- The newly declared names are outside their own type annotation.
          let rest := ts.extract i ts.size
          let stop := match splitDepth0 rest delimiters with | some s => i + s | none => ts.size
          out := out ++ resolve (ts.extract i stop) env bound
          i := stop
          break
      bound := bound ++ pending
      continue
    if isOpen t then depth := depth + 1
    else if isClose t then
      depth := depth - 1
      while scopes.size > 0 && scopes.back!.1 > depth do
        bound := bound.extract 0 scopes.back!.2
        scopes := scopes.pop
    if isIdent t then
      -- `x.foo` refers to binder `x`.
      let (hd, suffix) := if t.startsWith "«" && t.contains '»' then
          let k := (t.takeWhile (· != '»')).toString.length + 1
          ((t.take k).toString, (t.drop k).toString)
        else match t.splitOn "." with
          | h :: rest@(_ :: _) => (h, "." ++ ".".intercalate rest)
          | _ => (t, "")
      let mut found : Option String := none
      for idx in [:bound.size] do
        if bound[bound.size - 1 - idx]! == some hd then
          found := some s!"#{idx}{suffix}"; break
      match found with
      | some r => out := out.push r
      | none => match env[hd]? with
        | some k => out := out.push s!"#b{k}@{bound.size}{suffix}"
        | none => out := out.push t
    else out := out.push t
    i := i + 1
  return out

def coercions : List String := ["↑", "⇑", "↥"]

/-- Drop spelling that elaboration erases: coercion arrows, and parentheses around one token or
    around another parenthesized group. -/
partial def normalize (ts : Toks) : Toks :=
  let ts := ts.filter (!coercions.contains ·)
  go ts
where
  go (ts : Toks) : Toks := Id.run do
    for h : i in [:ts.size] do
      if ts[i] != "(" then continue
      let j := matching ts i
      let inner := ts.extract (i + 1) j
      if (inner.size == 1 && !isClose inner[0]!) ||
          (inner.size > 0 && inner[0]! == "(" && matching inner 0 == inner.size - 1) then
        return go (ts.extract 0 i ++ inner ++ ts.extract (j + 1) ts.size)
    return ts

/-- Key, and binder-order-sensitive key, of a statement with binders `(name, type)`. -/
def canonical (bs : Array Binder) (concl : Toks) : String × String := Id.run do
  let mut env : Std.HashMap String Nat := {}
  let mut types : Array Toks := #[]
  for h : k in [:bs.size] do
    let (name, ty) := bs[k]
    types := types.push (resolve (normalize (ty.getD #["_"])) env)
    if let some n := name then
      if n != "_" then env := env.insert n k
  let body := resolve (normalize concl) env
  let refs (ts : Toks) : Array Nat := ts.filterMap fun t => (topRef? t).map (·.1)
  let mut order : Array Nat := #[]
  for r in refs body do
    unless order.contains r do order := order.push r
  let mut i := 0
  while order.size < bs.size do
    if i < order.size then
      for r in refs types[order[i]!]! do
        unless order.contains r do order := order.push r
      i := i + 1
      continue
    let pos : Std.HashMap Nat Nat := order.zipIdx.foldl (fun m (b, p) => m.insert b p) {}
    let shape (b : Nat) : String := " ".intercalate (types[b]!.toList.map fun t =>
      match topRef? t with
      | some (k, d, sfx) => s!"#{(pos[k]?.map toString).getD "_"}@{d}{sfx}"
      | none => t)
    let mut best : Option (String × Nat) := none
    for b in [:bs.size] do
      if order.contains b then continue
      let s := shape b
      if best.all fun (s', b') => s < s' || (s == s' && b < b') then best := some (s, b)
    order := order.push best.get!.2
  -- Universe names, renamed in order of first occurrence as the elaborated pass does.
  let mut universes : Std.HashSet String := {}
  for ts in types.push body do
    for k in [:ts.size - 1] do
      let t := ts[k]!
      let nxt := ts[k+1]!
      if (t == "Type" || t == "Sort") && isIdent nxt then universes := universes.insert nxt
      else if ((t == "Type" || t == "Sort") && nxt == "(") || (t == "." && nxt == "{") then
        for u in ts.extract (k + 2) (matching ts (k + 1)) do
          if isIdent u && u != "max" && u != "imax" then universes := universes.insert u
  let mut placed : Array Nat := #[]
  let mut pending := order
  while pending.size > 0 do
    let some b := pending.find? fun b => (refs types[b]!).all placed.contains | break
    placed := placed.push b
    pending := pending.erase b
  let render (perm : Array Nat) : String := Id.run do
    let pos : Std.HashMap Nat Nat := perm.zipIdx.foldl (fun m (b, p) => m.insert b p) {}
    let mut levels : Std.HashMap String String := {}
    let mut parts : Array String := #[]
    let parts0 := perm.zipIdx.map (fun (b, i) => (types[b]!, i)) |>.push (body, perm.size)
    for (ts, depth) in parts0 do
      let mut o : Array String := #[]
      for t in ts do
        let mut t := t
        if universes.contains t then
          match levels[t]? with
          | some u => t := u
          | none => let u := s!"#u{levels.size}"; levels := levels.insert t u; t := u
        if let some (k, d, sfx) := topRef? t then
          let p := pos[k]?.getD 0
          t := s!"#{(depth : Int) + d - 1 - p}{sfx}"
        o := o.push t
      parts := parts.push (" ".intercalate o.toList)
    return " ⊢ ".intercalate parts.toList
  return (render placed, render (Array.range bs.size))

/-! ## Modules -/

structure Scope where
  name : Option String := none
  variables : Array (Option String × Toks) := #[]

def mentions (ts : Toks) : Std.HashSet String :=
  ts.foldl (init := {}) fun s t => if isIdent t then s.insert ((t.splitOn ".").head!) else s

/-- Section variables Lean includes in a theorem that mentions the names in `used`. -/
def includedVariables (scopes : Array Scope) (used : Std.HashSet String) : Array Binder := Id.run do
  let vars := scopes.foldl (· ++ ·.variables) #[]
  let mut named : Std.HashMap String Nat := {}
  for h : k in [:vars.size] do
    if let some n := vars[k].1 then named := named.insert n k
  let mut take : Std.HashSet Nat := {}
  let mut stack := used.toArray.filterMap (named[·]?)
  while let some k := stack.back? do
    stack := stack.pop
    if take.contains k then continue
    take := take.insert k
    stack := stack ++ (mentions vars[k]!.2).toArray.filterMap (named[·]?)
  -- Instance arguments about included variables come along.
  for h : k in [:vars.size] do
    let (n, ty) := vars[k]
    if n.isNone then
      let deps := (mentions ty).toArray.filterMap (named[·]?)
      if deps.size > 0 && deps.all take.contains then take := take.insert k
  return (take.toArray.qsort (· < ·)).map fun k => (vars[k]!.1, some vars[k]!.2)

structure Decl where
  name : String
  module : String
  index : Nat
  range : Lsp.Range
  private_ : Bool
  key : String
  plain : String
  deriving Inhabited

/-- Offsets of commands: a line whose first character is `@`, `#` or a word character. -/
def commandStarts (s : Array Char) : Array Nat := Id.run do
  let mut out := #[]
  for h : i in [:s.size] do
    if (i == 0 || s[i-1]! == '\n') && (s[i] == '@' || s[i] == '#' || isWord s[i]) then out := out.push i
  return out

def stripModifiers (ts : Toks) : Toks × Bool := Id.run do
  let mut ts := ts
  let mut priv := false
  while ts.size > 0 do
    let t := ts[0]!
    if t == "@" || t.startsWith "@[" then
      let some i := ts.findIdx? (· == "[") | return (ts, priv)
      ts := ts.extract (matching ts i + 1) ts.size
    else if modifiers.contains t then
      priv := priv || t == "private"
      ts := ts.extract 1 ts.size
    else if ["open", "set_option", "omit", "include"].contains t && ts.contains "in" then
      ts := ts.extract ((ts.findIdx? (· == "in")).get! + 1) ts.size
    else return (ts, priv)
  return (ts, priv)

/-- LSP position (UTF-16 columns) of a code-point offset. -/
def lspPos (s : Array Char) (off : Nat) : Lsp.Position := Id.run do
  let mut line := 0
  let mut start := 0
  for i in [:min off s.size] do
    if s[i]! == '\n' then line := line + 1; start := i + 1
  let mut col := 0
  for i in [start:off] do col := col + (if s[i]!.toNat > 0xFFFF then 2 else 1)
  return { line, character := col }

/-- Theorem declarations of a source file, and how many theorems could not be read. -/
def parseModule (text : String) (module : String) : Array Decl × Nat := Id.run do
  let s := blankComments text.toList.toArray
  let mut scopes : Array Scope := #[{}]
  let mut decls : Array Decl := #[]
  let mut skipped := 0
  let starts := commandStarts s
  for h : ci in [:starts.size] do
    let a := starts[ci]
    let b := starts[ci+1]?.getD s.size
    let toks := tokenize s a b
    let (words, priv) := stripModifiers (toks.map (·.1))
    if words.isEmpty then continue
    let located := toks.extract (toks.size - words.size) toks.size
    let kw := words[0]!
    if kw == "namespace" && words.size > 1 then scopes := scopes.push { name := some words[1]! }
    else if kw == "section" || (words.size ≥ 2 && words[0]! == "noncomputable" && words[1]! == "section") then
      scopes := scopes.push {}
    else if kw == "end" then
      if scopes.size > 1 then scopes := scopes.pop
    else if kw == "variable" then
      for (n, ty) in (binderGroups (words.extract 1 words.size)).getD #[] do
        if let some ty := ty then
          scopes := scopes.modify (scopes.size - 1) fun sc => { sc with variables := sc.variables.push (n, ty) }
    else if (kw == "theorem" || kw == "lemma") && words.size > 2 then
      let name := words[1]!
      let mut rest := words.extract 2 words.size
      let mut loc := located.extract 2 located.size
      if rest.size ≥ 2 && rest[0]! == "." && rest[1]! == "{" then
        let skip := matching rest 1 + 1
        rest := rest.extract skip rest.size
        loc := loc.extract skip loc.size
      -- The proof starts at `:=`, `where`, or a `|` alternative at the start of a line.
      let mut stop := splitDepth0 rest [":=", "where"]
      for k in [:(stop.getD loc.size)] do
        let (t, off) := loc[k]!
        if t == "|" then
          let mut ls := off
          while ls > 0 && s[ls-1]! != '\n' do ls := ls - 1
          if (str s ls off).trimAscii.isEmpty && splitDepth0 (rest.extract 0 (k + 1)) ["|"] == some k then
            stop := some k
            break
      let sig := match stop with | some e => rest.extract 0 e | none => rest
      let own := (splitDepth0 sig [":"]).bind fun c => binderGroups (sig.extract 0 c)
      let some own := own | skipped := skipped + 1; continue
      let colon := (splitDepth0 sig [":"]).get!
      let (post, concl) := flatten (sig.extract (colon + 1) sig.size)
      let mut used := mentions concl
      for (_, ty) in own ++ post do
        for m in mentions (ty.getD #[]) do used := used.insert m
      for (n, _) in own do
        if let some n := n then used := used.erase n
      let vars := includedVariables scopes used
      let (key, plain) := canonical (vars ++ own ++ post) concl
      let ns := ".".intercalate (scopes.filterMap (·.name)).toList
      let full := match name.dropPrefix? "_root_." with
        | some r => r.toString
        | none => if ns.isEmpty then name else ns ++ "." ++ name
      let off := toks[toks.size - words.size + 1]!.2
      let range : Lsp.Range := ⟨lspPos s off, lspPos s (off + name.length)⟩
      decls := decls.push { name := full, module, index := decls.size, range, private_ := priv, key, plain }
  return (decls, skipped)

/-- Modules imported by a source file's header. -/
def headerImports (text : String) : Array String := Id.run do
  let s := blankComments text.toList.toArray
  let text := str s 0 s.size
  let mut out := #[]
  for line in text.splitOn "\n" do
    let ws := (line.splitOn " ").filter (· != "") |>.map (·.trimAscii.toString) |>.filter (· != "")
    match ws with
    | [] => continue
    | w :: _ =>
      unless ["module", "prelude", "import", "public", "meta"].contains w do break
      let rec find : List String → Option String
        | "import" :: "all" :: m :: _ => some m
        | "import" :: m :: _ => some m
        | _ :: r => find r
        | [] => none
      if let some m := find ws then out := out.push m
  return out

def moduleName (root path : FilePath) : String :=
  let r := root.toString ++ "/"
  let p := path.toString
  let rel := if p.startsWith r then (p.drop r.length).toString else (path.fileStem.getD p)
  ".".intercalate ((rel.dropSuffix? ".lean").map (·.toString) |>.getD rel |>.splitOn "/")

/-! ## Reachability -/

/-- Whether one module transitively imports another, without storing closures: each of a few
    randomized post-order traversals labels a module with the interval of ranks below it (GRAIL,
    Yildirim et al. 2010). Other queries search, skipping modules whose intervals exclude the target. -/
structure Reach where
  imports : Std.HashMap String (Array String)
  labels : Array (Std.HashMap String (Nat × Nat))

def Reach.build (imports : Std.HashMap String (Array String)) (rounds := 3) : Reach := Id.run do
  let mut seed : UInt64 := 0x9E3779B97F4A7C15
  let mut labels := #[]
  let nodes0 := imports.toArray.map (·.1) |>.qsort (· < ·)
  for _ in [:rounds] do
    -- Fisher–Yates with a fixed LCG, so labels are deterministic.
    let mut nodes := nodes0
    for i' in [:nodes.size] do
      let i := nodes.size - 1 - i'
      seed := seed * 6364136223846793005 + 1442695040888963407
      let j := (seed >>> 33).toNat % (i + 1)
      nodes := nodes.swapIfInBounds i j
    let mut label : Std.HashMap String (Nat × Nat) := {}
    let mut rank := 0
    for root in nodes do
      if label.contains root then continue
      label := label.insert root (0, 0)
      let mut stack : Array (String × Nat) := #[(root, 0)]
      while let some (node, k) := stack.back? do
        let kids := imports[node]?.getD #[]
        if h : k < kids.size then
          stack := stack.set! (stack.size - 1) (node, k + 1)
          let c := kids[k]
          unless label.contains c do
            label := label.insert c (0, 0)
            stack := stack.push (c, 0)
        else
          stack := stack.pop
          let low := kids.foldl (fun m c => min m ((label[c]?.getD (rank, rank)).1)) rank
          label := label.insert node (low, rank)
          rank := rank + 1
    labels := labels.push label
  return { imports, labels }

def Reach.mayReach (r : Reach) (a b : String) : Bool :=
  r.labels.all fun l => match l[a]?, l[b]? with
    | some (la, ha), some (lb, hb) => la ≤ lb && hb ≤ ha
    | _, _ => false

def Reach.reaches (r : Reach) (a b : String) : Bool := Id.run do
  if a == b || !r.mayReach a b then return false
  let mut stack := #[a]
  let mut seen : Std.HashSet String := ({} : Std.HashSet String).insert a
  while let some x := stack.back? do
    stack := stack.pop
    for c in r.imports[x]?.getD #[] do
      if c == b then return true
      if !seen.contains c && r.mayReach c b then
        seen := seen.insert c
        stack := stack.push c
  return false

/-! ## Index -/

structure Finding where
  rule : String
  message : String
  lemma : String
  range : Lsp.Range
  deriving ToJson, FromJson

structure Index where
  src : FilePath
  modules : Std.HashMap String (Array String × Array Decl × Nat) := {}
  keys : Std.HashMap String (Array Decl) := {}
  reach : Option Reach := none

def Index.add (ix : Index) (module text : String) : Index := Id.run do
  let mut ix := ix
  let old := ix.modules[module]?
  if let some (_, ds, _) := old then
    for d in ds do
      ix := { ix with keys := ix.keys.modify d.key (·.filter (·.module != module)) }
  let imports := headerImports text
  let (decls, skipped) := parseModule text module
  ix := { ix with modules := ix.modules.insert module (imports, decls, skipped) }
  if old.all (·.1 != imports) then ix := { ix with reach := none }
  for d in decls do
    ix := { ix with keys := ix.keys.alter d.key fun a => some ((a.getD #[]).push d) }
  return ix

def Index.pathOf (ix : Index) (module : String) : IO (Option FilePath) := do
  let p := (module.splitOn ".").foldl (· / ·) ix.src |>.addExtension "lean"
  if ← p.isDir then return none
  return if ← p.pathExists then some p else none

/-- Index the files and, transitively, the project modules they import. -/
def Index.load (ix : Index) (paths : Array FilePath) : IO Index := do
  let mut ix := ix
  let mut stack ← paths.mapM fun p => return (moduleName ix.src p, p)
  while let some (m, p) := stack.back? do
    stack := stack.pop
    if ix.modules.contains m then continue
    ix := ix.add m (← IO.FS.readFile p)
    for i in (ix.modules[m]?.map (·.1)).getD #[] do
      if !ix.modules.contains i then
        if let some q ← ix.pathOf i then stack := stack.push (i, q)
  return ix

def Index.imports (ix : Index) : Index × (String → String → Bool) :=
  let r := ix.reach.getD (Reach.build (ix.modules.fold (init := {}) fun acc m (imps, _, _) =>
    acc.insert m (imps.filter ix.modules.contains)))
  ({ ix with reach := some r }, r.reaches)

def canCite (reaches : String → String → Bool) (user used : Decl) : Bool :=
  if used.module == user.module then used.index < user.index
  else !used.private_ && reaches user.module used.module

def Index.analyze (ix : Index) (path : FilePath) (text : Option String := none) :
    IO (Index × Array Finding × Nat) := do
  let path ← IO.FS.realPath path
  let module := moduleName ix.src path
  let mut ix := ix
  if let some t := text then ix := ix.add module t
  ix ← ix.load #[path]
  let (ix', reaches) := ix.imports
  ix := ix'
  let some (_, decls, skipped) := ix.modules[module]? | return (ix, #[], 0)
  let mut out := #[]
  for d in decls do
    let others := (ix.keys[d.key]?.getD #[]).filter (fun x => !(x.module == d.module && x.index == d.index))
      |>.qsort (·.name < ·.name)
    -- Prefer a restatement that can be cited and whose arguments line up.
    let cited := others.filter (canCite reaches d ·)
    let cited := cited.filter (·.plain == d.plain) ++ cited.filter (·.plain != d.plain)
    let (x, how) ← match cited[0]? with
      | some x => pure (x, "")
      | none =>
        -- When the other theorem can cite this one, it reports the pair.
        let unrelated := others.filter (!canCite reaches · d)
        let some x := unrelated[0]? | continue
        pure (x, if x.private_ then ", which is private to another module"
          else ", which this module does not import")
    let reordered := if x.plain != d.plain then " (with arguments reordered)" else ""
    out := out.push { rule := "syntacticDuplicate", lemma := x.name, range := d.range
                      message := s!"{d.name} restates{reordered} {x.name}{how} (matched by syntax)" }
  return (ix, out, skipped)

end LeanPerf.SyntaxDedup
