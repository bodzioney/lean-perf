"""The context a small model sees beside a declaration: the statements of the declarations above it in the
same file that share the most names with it, so that the model can use lemmas that really exist instead of
guessing names.

The same function builds the prompt for training (scripts/ml/build.py, from the file at the commit before
a change) and for proposing (scripts/propose-local, from the request's `context`), so they always agree.
"""
import math
import re

# A top-level declaration starts at the beginning of a line, after any docstring and attributes.
DECL = re.compile(r"^(?:@\[[^\n]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|unsafe|partial) )*"
                  r"(theorem|lemma|def|abbrev|instance|structure|class|inductive)\b", re.M)
COMMENT = re.compile(r"/-.*?-/|--[^\n]*", re.S)
IDENT = re.compile(r"[^\W\d][\w'.!?₀-₉]*")
# Names too common to say anything about which declarations are related.
COMMON = set("""Type Prop Sort fun by have show from exact at with simp rw intro theorem lemma def instance
    let in if then else match this rfl Nat Int Real ℕ ℤ ℝ ℂ ℚ True False Iff And Or Not Eq Ne Set Finset
    List Function id x y z a b c n m k i j f g h s t u v e p q r""".split())


def statement(text):
    """A declaration's text up to its proof, with comments dropped and whitespace collapsed."""
    text = COMMENT.sub("", text)
    depth = 0
    for i, c in enumerate(text[:-1]):
        if c in "([{⟨⦃":
            depth += 1
        elif c in ")]}⟩⦄":
            depth -= 1
        elif depth == 0 and (text.startswith(":=", i) or text.startswith(" where", i) or
                             (c == "\n" and text[i + 1:i + 3] == "| ")):
            text = text[:i]
            break
    return re.sub(r"\s+", " ", text).strip()


def names(text):
    out = set()
    for t in IDENT.findall(text):
        for part in [t] + t.split("."):
            if part and part not in COMMON:
                out.add(part)
    return out


def related(prefix, declaration, budget=1200):
    """The statements of declarations in `prefix` (the file above `declaration`) that share the most names
    with `declaration`, in file order, at most `budget` bytes in all."""
    starts = [m.start() for m in DECL.finditer(prefix)]
    decls = [prefix[a:b] for a, b in zip(starts, starts[1:] + [len(prefix)])]
    if not decls:
        return ""
    want = names(declaration)
    sigs = [statement(d) for d in decls]
    # How many statements mention each name: a name in few of them says more.
    df = {}
    for s in sigs:
        for n in names(s):
            df[n] = df.get(n, 0) + 1
    scored = []
    for k, s in enumerate(sigs):
        if len(s) < 12 or len(s.encode()) > budget // 2:
            continue
        m = DECL.match(s)
        own = s[m.end():].split()[0] if m and s[m.end():].split() else ""
        shared = names(s) & want
        score = sum(1 / math.log(2 + df[n]) for n in shared)
        # A declaration that the original proof names is the likeliest to be useful.
        if own and (own in want or own.split(".")[-1] in want):
            score += 3
        if score > 0:
            # Nearer declarations break ties.
            scored.append((score + k / (10 * len(sigs)), k, s))
    scored.sort(reverse=True)
    chosen, used = [], 0
    for _, k, s in scored:
        size = len(s.encode()) + 1
        if used + size > budget:
            continue
        chosen.append((k, s))
        used += size
    return "\n".join(s for _, s in sorted(chosen))


def message(related_statements, declaration):
    """The user message: the related statements, if any, then the declaration to shorten. Without related
    statements it is the declaration alone, as models trained without context saw it."""
    if related_statements:
        return f"Earlier in the file:\n{related_statements}\n\nShorten:\n{declaration}"
    return declaration
