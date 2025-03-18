/-
	Decidable Propositions
-/
variable (p : Nat → Prop)


-- error : failed to synthesize instance
--   Decidable (p n)

-- #synth Decidable (p 0)

/-
def bad_foo : Nat → Bool :=
  fun (n : Nat) =>
  if p n then true
  else false
-/

open Classical

noncomputable def foo : Nat → Bool :=
  fun (n : Nat) =>
  if p n then true
  else false

#print axioms foo
-- 'foo' depends on axioms: [Classical.choice, Quot.sound, propext]

namespace Hidden

class inductive Decidable (p : Prop) where
  | isFalse (h : ¬p) : Decidable p
  | isTrue  (h : p)  : Decidable p

def ite {α : Sort u} (c : Prop) [h : Decidable c] (t e : α) : α :=
  Decidable.casesOn (motive := fun _ => α) h (fun _ => e) (fun _ => t)

def dite {α : Sort u} (c : Prop) [h : Decidable c] (t : c → α) (e : Not c → α) : α :=
  Decidable.casesOn (motive := fun _ => α) h e t
-- c（または¬c）が仮定された定理を使うことができる。

end Hidden

#check @instDecidableAnd
  -- {p q : Prop} → [Decidable p] → [Decidable q] → Decidable (And p q)

#check @instDecidableOr
#check @instDecidableNot

def step (a b x : Nat) : Nat :=
  if x < a ∨ x > b then 0 else 1

set_option pp.explicit true  -- 暗黙の引数を表示する
#print step


namespace Hidden
open Classical

noncomputable scoped
instance (priority := low) propDecidable (a : Prop) : Decidable a :=
  choice <| match em a with
    | Or.inl h => ⟨isTrue h⟩
    | Or.inr h => ⟨isFalse h⟩

end Hidden

example : 10 < 5 ∨ 1 > 0 := by
  decide

example : ¬ (True ∧ False) := by
  decide

example : 10 * 20 = 200 := by
  decide

theorem ex : True ∧ 2 = 1+1 := by
  decide

#print ex
-- theorem ex : True ∧ 2 = 1 + 1 :=
-- of_decide_eq_true (Eq.refl true)

#check @of_decide_eq_true
-- ∀ {p : Prop} [Decidable p], decide p = true → p

#check @decide
-- (p : Prop) → [Decidable p] → Bool
