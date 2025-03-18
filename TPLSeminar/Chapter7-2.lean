/-
  Constructors with Arguments
-/

namespace Hidden

inductive Prod (α : Type u) (β : Type v)
  | mk : α → β → Prod α β

inductive Sum (α : Type u) (β : Type v) where
  | inl : α → Sum α β
  | inr : β → Sum α β

def fst {α : Type u} {β : Type v} (p : Prod α β) : α :=
  match p with
  | Prod.mk a _ => a

def snd {α : Type u} {β : Type v} (p : Prod α β) : β :=
  match p with
  | Prod.mk _ b => b

end Hidden

#check Prod.casesOn

-- {α : Type u} →
-- {β : Type v} →
-- {motive : α × β → Sort u_1} →
-- (t : α × β) →
-- ((fst : α) → (snd : β) → motive (fst, snd)) →
-- motive t

def prod_example (p : Bool × Nat) : Nat :=
  Prod.casesOn (motive := fun _ => Nat) p (fun b n => cond b (2 * n) (2 * n + 1))

#eval prod_example (true, 3)
#eval prod_example (false, 3)

#check Sum.casesOn

-- {α : Type u} →
-- {β : Type v} →
-- {motive : α ⊕ β → Sort u_1} →
-- (t : α ⊕ β) →
-- ((val : α) → motive (Sum.inl val)) →
-- ((val : β) → motive (Sum.inr val)) →
-- motive t

def sum_example (s : Sum Nat Nat) : Nat :=
  Sum.casesOn (motive := fun _ => Nat) s
    (fun n => 2 * n)
    (fun n => 2 * n + 1)

#eval sum_example (Sum.inl 3)
#eval sum_example (Sum.inr 3)

def sum_example2 (s : Sum Nat Nat) : Nat :=
  match s with
  | Sum.inl a => 2 * a
  | Sum.inr b => 2 * b + 1

#eval sum_example2 (Sum.inl 3)
#eval sum_example2 (Sum.inr 3)

namespace Hidden

-- structure Prod (α : Type u) (β : Type v) where
--   mk :: (fst : α) (snd : β)

end Hidden

structure Color where
  (red : Nat) (green : Nat) (blue : Nat)
  deriving Repr

def yellow := Color.mk 255 255 0

#check Color
#eval yellow

#print Color.red  -- ``structure`` キーワードにより生成された射影関数
#eval Color.red yellow

-- structure Color where
--   red : Nat
--   green : Nat
--   blue : Nat
--   deriving Repr

structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)

inductive semigrp where
  | mk (carrier : Type u) (mul : carrier → carrier → carrier)
    (mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)) : semigrp

namespace Hidden

inductive Sigma {α : Type u} (β : α → Type v) where
  | mk : (a : α) → β a → Sigma β

end Hidden

namespace Hidden

inductive Option (α : Type u) where
  | none : Option α
  | some : α → Option α
-- X ⨿ {*}

#check Option

-- variable (α : Type u) (x : α)
-- #check some x

inductive Inhabited (α : Type u) where
  | mk : α → Inhabited α

-- 練習問題

def comp (g : β → Option γ) (f : α → Option β) : α → Option γ :=
  fun a =>
    match f a with
    | Option.none => Option.none
    | Option.some b => g b

-- theorem comp_none (f : α → Option β) (g : β → Option γ) (a : α) (h : f a = Option.none) :
--   comp g f a = Option.none := by
--   simp [comp, h]

theorem comp_assoc (f : α → Option β) (g : β → Option γ) (h : γ → Option δ) :
  comp h (comp g f) = comp (comp h g) f := by
  funext a
  rw [comp, comp, comp]
  cases f a <;> rfl

end Hidden

example : Inhabited Nat := ⟨0⟩
example : Inhabited Bool := ⟨true⟩

-- example (α β : Type u) [Inhabited α] [Inhabited β] : Inhabited (α × β) := sorry

example (α β : Type u) (hα : Inhabited α) (hβ : Inhabited β) : Inhabited (α × β) :=
  match hα with
  | Inhabited.mk a =>
    match hβ with
    | Inhabited.mk b => Inhabited.mk (Prod.mk a b)

example (α β : Type u) (hβ : Inhabited β) : Inhabited (α → β) :=
  match hβ with
  | ⟨b⟩ => Inhabited.mk (fun _ => b)
