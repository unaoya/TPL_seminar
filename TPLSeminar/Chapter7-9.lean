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

#check Even 2
#check Even 1

example : Even 2 := Even.even_succ 1 (Odd.odd_succ 0 Even.even_zero)

open Even Odd

example : Even 2 := even_succ 1 (odd_succ 0 even_zero)

mutual
    inductive Tree (α : Type u) where
      | node : α → TreeList α → Tree α

    inductive TreeList (α : Type u) where
      | nil  : TreeList α
      | cons : Tree α → TreeList α → TreeList α
end

#print List

namespace Hidden

inductive Tree (α : Type u) where
  | mk : α → List (Tree α) → Tree α

end Hidden

/-
  Exercises
-/

inductive Term where
  | const (n : Nat) : Term
  | plus (s t : Term) : Term
  | times (s t : Term) : Term

def eval : Term → Nat
  | Term.const n => n
  | Term.plus s t => eval s + eval t
  | Term.times s t => eval s * eval t

#eval eval (Term.times (Term.const 2) (Term.plus (Term.const 3) (Term.const 4)))

inductive Term₁ where
  | const (n : Nat) : Term₁
  | var (n : Nat) : Term₁
  | plus (s t : Term₁) : Term₁
  | times (s t : Term₁) : Term₁

def eval₁ : Term₁ → (Nat → Nat) → Nat
  | Term₁.const n => fun _ => n
  | Term₁.var n => fun f => f n
  | Term₁.plus s t => fun f => eval₁ s f + eval₁ t f
  | Term₁.times s t => fun f => eval₁ s f * eval₁ t f

def f : Nat → Nat
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | _ => 0

#eval eval₁ (Term₁.times (Term₁.const 2) (Term₁.plus (Term₁.var 1) (Term₁.const 4))) f

-- def Range (n : Nat) := { m : Nat // m < n }

-- inductive Term₁ (n : Nat) where
--   | const (m : Nat) : Term₁ n
--   | var (m : Range n) : Term₁ n
--   | plus : Term₁ n → Term₁ n → Term₁ n
--   | times : Term₁ n → Term₁ n
