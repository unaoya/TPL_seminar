/-
  Exercises
-/

example (p q r : Prop) (hp : p)
  : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  apply And.intro <;> try (apply And.intro)
  · repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)
  · repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)
  · repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)

theorem h (p q r : Prop) (hp : p)
  : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  (apply And.intro <;> try (apply And.intro)) <;> repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)


#check h
#print h

-- example (p q r : Prop) (hp : p)
--   : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
--   (all_goals (try (apply And.intro))) <;> repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)
