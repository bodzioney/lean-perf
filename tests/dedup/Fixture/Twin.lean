import Fixture.Base

-- The same private name as in Base, which a build allows.
private theorem wrap_hidden (n : Nat) (h : Wrap n) : Wrap (n + 0) := rfl
