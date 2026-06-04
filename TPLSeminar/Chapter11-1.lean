/-
	Basic navigation and rewriting
-/
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    -- ⊢ a * (b * c) = a * (c * b)
    lhs
    -- ⊢ a * (b * c) = mul a (b * c)
    congr
    -- 2 goals: ⊢ a, ⊢ b * c
    rfl
    -- ⊢ b * c
    rw [Nat.mul_comm]

example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  rw [Nat.mul_comm b c]

example (a b c : Nat) : a * (b * c) = (a * b) * c := by
  conv =>
    lhs
    rw [← Nat.mul_assoc]


example : (fun x : Nat => 0 + x) = (fun x => x) := by
  conv =>
    lhs
    intro x
    rw [Nat.zero_add]

example : (fun x : Nat => 0 + x) = (fun x => x) := by
  funext x; rw [Nat.zero_add]

example : (fun x : Nat => 0 + x) = (fun x => x) := by
  simp
