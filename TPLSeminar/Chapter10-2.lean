/-
	Chaining Instances
-/
instance [Inhabited a] [Inhabited b] : Inhabited (a × b) where
  default := (default, default)

#eval (Inhabited.default : Nat × Bool)
-- (0, true)

variable (a b : Type u)

instance [Inhabited b] : Inhabited (a → b) where
  default := fun _ => Inhabited.default

example (n : Nat) : (Inhabited.default : (Nat → Nat)) n = 0 := rfl

#check (inferInstance : Inhabited Nat) -- Inhabited Nat

def foo : Inhabited (Nat × Nat) :=
  inferInstance

#eval foo.default  -- (0, 0)

theorem ex : foo.default = (default, default) :=
  rfl

#print inferInstance
