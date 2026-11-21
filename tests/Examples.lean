example (f : Unit → True ∧ True) (hObtained : True) : True := by
  obtain ⟨left, _⟩ := f
    ()
  exact left

example (𝒫 : Prop) (h : 𝒫) : 𝒫 := by simpa using h
example (n : Nat) : n = n := by simp
example (n : Nat) (h : 0 + n = 1) : n = 1 := by simpa using h
example (n : Nat) : 0 + n = n := by simp
