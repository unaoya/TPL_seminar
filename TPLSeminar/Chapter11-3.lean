/-
	Structuring conversion tactics
-/
example (a b c : Nat) : (0 + a) * (b * c) = a * (c * b) := by
  conv =>
    lhs
    congr
    . rw [Nat.zero_add]
    . rw [Nat.mul_comm]

example (a b c : Nat) : (0 + a) * (b * c) = a * (c * b) := by
  conv =>
    pattern 0 + a
    rw [Nat.zero_add]
  conv =>
    pattern b * c
    rw [Nat.mul_comm]

example (a b c : Nat) : (0 + a) * (b * c) = a * (c * b) := by
  conv in 0 + a => rw [Nat.zero_add]
  conv in b * c => rw [Nat.mul_comm]
