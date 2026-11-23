import Fixture.Base

theorem my_add_comm (n m : Nat) : n + m = m + n := by
  omega

theorem my_lt_le (a b c : Nat) (h₂ : b ≤ c) (h₁ : a < b) : a < c := by omega

theorem two_eq : 1 + 1 = Nat.succ 1 := rfl

theorem wrap_sum (y x : Nat) (k : Wrap y) (h : Wrap x) : Wrap (x + y) := rfl

theorem wrap_zero (m : Nat) (h : Wrap m) : Wrap (m + 0) := rfl

private theorem wrap_one (n : Nat) (h : Wrap n) : Wrap (n + 1) := rfl

theorem wrap_succ (k : Nat) (hk : Wrap k) : Wrap (k + 1) := rfl

theorem wrap_self (n : Nat) : Wrap n := rfl

theorem wrap_mul (a : Nat) (h : Wrap a) : Wrap (a * 2) := rfl

theorem wrap_iff (a : Nat) : Wrap a ↔ a = a := Iff.rfl

theorem comm_after (n : Nat) : ∀ m, n + m = m + n := fun m => Nat.add_comm n m

theorem lt_le_after (a b c : Nat) : b ≤ c → a < b → a < c := fun h₂ h₁ => Nat.lt_of_lt_of_le h₁ h₂

theorem comm_implicit (m : Nat) : ∀ {m : Nat} (n : Nat), m + n = n + m := Nat.add_comm _
