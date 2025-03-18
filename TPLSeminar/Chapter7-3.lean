/-
  Inductively Defined Propositions
-/

namespace Hidden
inductive False : Prop

inductive True : Prop where
  | intro : True

inductive And (a b : Prop) : Prop where
  | intro : a → b → And a b

inductive Or (a b : Prop) : Prop where
  | inl : a → Or a b
  | inr : b → Or a b

inductive Exists {α : Sort u} (p : α → Prop) : Prop where
  | intro (w : α) (h : p w) : Exists p

inductive Subtype {α : Type u} (p : α → Prop) where
  | mk : (x : α) → p x → Subtype p

-- structure Subtype {α : Sort u} (p : α → Prop) where
--   val : α
--   property : p val

def even (n : Nat) : Prop := ∃ m, 2 * m = n

theorem evensum (x y : Nat) (hx : even x) (hy : even y) : even (x + y) := by
  rcases hx with ⟨m, hm⟩
  rcases hy with ⟨n, hn⟩
  exact ⟨m + n, by rw [Nat.mul_add, hn, hm]⟩

def evenNat := Subtype even

def x : evenNat := ⟨2, ⟨1, rfl⟩⟩

example (x y : evenNat) : even (x.1 + y.1) := by
  match x with
  | ⟨x, hx⟩ =>
    match y with
    | ⟨y, hy⟩ => exact evensum x y hx hy


end Hidden
