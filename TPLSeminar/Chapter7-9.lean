/-
  Axiomatic Details
-/


/-
  Mutual and Nested Inductive Types
-/

mutual
  inductive Even : Nat → Prop where
    | even_zero : Even 0
    | even_succ : (n : Nat) → Odd n → Even (n + 1)

  inductive Odd : Nat → Prop where
    | odd_succ : (n : Nat) → Even n → Odd (n + 1)
end

open Even Odd

example : Even 2 := even_succ 1 (odd_succ 0 even_zero)

mutual
    inductive Tree (α : Type u) where
      | node : α → TreeList α → Tree α

    inductive TreeList (α : Type u) where
      | nil  : TreeList α
      | cons : Tree α → TreeList α → TreeList α
end

namespace Hidden

inductive Tree (α : Type u) where
  | mk : α → List (Tree α) → Tree α

end Hidden

/-
  Exercises
-/
