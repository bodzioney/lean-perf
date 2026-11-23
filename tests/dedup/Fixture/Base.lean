def Wrap (n : Nat) : Prop := n = n

theorem wrap_two (a b : Nat) (h : Wrap a) (k : Wrap b) : Wrap (a + b) := rfl

private theorem wrap_hidden (n : Nat) (h : Wrap n) : Wrap (n + 0) := rfl
