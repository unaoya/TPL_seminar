/-
  Inductive Families
-/

namespace Hidden

inductive List (α : Type u) : Type u where
  | nil  : List α
  | cons : α → List α → List α

inductive Vector (α : Type u) : Nat → Type u where
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)

#check Vector
#check Vector.nil
#check Vector.cons

#check Vector.rec

#check Or
#check Or.rec

#check And.rec

#check Eq
#check Eq.rec

#check Vector Bool 2
#check Vector.cons false (Vector.cons true (Vector.nil))

def F (α : Type) : Nat → Type :=
  fun n =>
  match n with
  | 0 => Bool
  | n+1 => Bool

def x : Type := Nat

inductive X where
  | mk : X


  -- Vector α n

inductive Eq {α : Sort u} (a : α) : α → Prop where
  | refl : Eq a a

  -- Eq {α} a x


end Hidden
universe u v

#check (@Eq.rec : {α : Sort u} → {a : α} → {motive : (x : α) → a = x → Sort v}
                  → motive a rfl → {b : α} → (h : a = b) → motive b h)

namespace Hidden
theorem subst {α : Type u} {a b : α} {p : α → Prop}
    (h₁ : Eq a b) (h₂ : p a) : p b :=
  Eq.rec (motive := fun x _ => p x) h₂ h₁

theorem subst₁ {α : Type u} {a b : α} {p : α → Prop}
    (h₁ : Eq a b) (h₂ : p a) : p b :=
  match h₁ with
  | Eq.refl => h₂

#print subst₁

set_option pp.all true
#print subst₁
  -- ... subst.match_1 ...
#print subst₁.match_1
  -- ... Eq.casesOn ...
#print Eq.casesOn
  -- ... Eq.rec ...

theorem symm {α : Type u} {a b : α} (h : Eq a b) : Eq b a :=
  match h with
  | Eq.refl => Eq.refl

theorem trans {α : Type u} {a b c : α} (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c :=
  match h₁, h₂ with
  | Eq.refl, Eq.refl => Eq.refl

theorem congr {α β : Type u} {a b : α} (f : α → β) (h : Eq a b) : Eq (f a) (f b) :=
  match h with
  | Eq.refl => Eq.refl

end Hidden

example {α : Type u} {f : α → Sort v} (a b : α) (h : Eq a b) (x : f a) : f b :=
  h ▸ x

-- 12/24ここまで
