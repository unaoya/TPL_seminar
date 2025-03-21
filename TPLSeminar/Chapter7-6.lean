/-
  Tactics for Inductive Types
-/

example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (Nat.succ n)) : ∀ n, p n := by
  intro n
  cases n
  . exact hz  -- goal is p 0
  . apply hs  -- goal is a : Nat ⊢ p (succ a)

open Nat

example (n : Nat) (h : n ≠ 0) : succ (pred n) = n := by
  cases n with
  | zero =>
    -- goal: h : 0 ≠ 0 ⊢ succ (pred 0) = 0
    apply absurd rfl h
  | succ m =>
    -- second goal: h : succ m ≠ 0 ⊢ succ (pred (succ m)) = succ m
    rfl

def f (n : Nat) : Nat := by
  cases n; exact 3; exact 7

example : f 0 = 3 := rfl
example : f 5 = 7 := rfl


-- α : Type, p : α -> Prop
-- (x : α, h : p x) たちの型 β を定義できる
-- mk : (x : α) → p x → β
def Tuple (α : Type) (n : Nat) :=
  { as : List α // as.length = n }

#check Tuple Nat 3

def xs : Tuple Nat 3 :=
  ⟨[0, 1, 2], rfl⟩

def f₁ {n : Nat} (t : Tuple α n) : Nat := by
  cases n; exact 3; exact 7

def myTuple : Tuple Nat 3 :=
  ⟨[0, 1, 2], rfl⟩

example : f₁ myTuple = 7 :=
  rfl

inductive Foo where
  | bar1 : Nat → Nat → Foo
  | bar2 : Nat → Nat → Nat → Foo

  -- Foo型の項はbar1 n mの形かbar2 n m kの形である

def silly (x : Foo) : Nat := by
  cases x with
  | bar1 a b => exact b
  | bar2 c d e => exact e

#eval silly (Foo.bar1 1 2)    -- 2
#eval silly (Foo.bar2 3 4 5)  -- 5

def silly₁ (x : Foo) : Nat := by
  cases x with
  | bar2 c d e => exact e
  | bar1 a b => exact b

def g (x : Nat) : Nat := 0
def g₁ (x : Nat) : Nat := by apply g; exact 0

def silly₂ (x : Foo) : Nat := by
  cases x
  case bar1 a b => exact b
  case bar2 c d e => exact e

def silly₃ (x : Foo) : Nat := by
  cases x
  case bar2 c d e => exact e
  case bar1 a b => exact b

example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (succ n)) (m k : Nat)
        : p (m + 3 * k) := by
  cases m + 3 * k
  . exact hz   -- goal is p 0
  . apply hs   -- goal is a : Nat ⊢ p (succ a)

example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (succ n)) (m k : Nat)
        : p (m + 3 * k) := by
  generalize m + 3 * k = n
  cases n
  . exact hz   -- goal is p 0
  . apply hs   -- goal is a : Nat ⊢ p (succ a)

example (p : Prop) (m n : Nat)
        (h₁ : m < n → p) (h₂ : m ≥ n → p) : p := by
  cases Nat.lt_or_ge m n
  case inl hlt => exact h₁ hlt
  case inr hge => exact h₂ hge

#check Or
#print Or

example (p : Prop) (m n : Nat)
        (h₁ : m < n → p) (h₂ : m ≥ n → p) : p := by
  have h : m < n ∨ m ≥ n := Nat.lt_or_ge m n
  cases h -- Or p q
  case inl hlt => exact h₁ hlt
  case inr hge => exact h₂ hge

#check Nat.sub_self

theorem t1 (m n : Nat) : m - n = 0 ∨ m ≠ n := by
  cases Decidable.em (m = n) with
  | inl heq => rw [heq]; apply Or.inl; exact Nat.sub_self n
  | inr hne => apply Or.inr; exact hne

/- ``Decidable.em`` は排中律 ``Classical.em`` を必要としない -/
#print axioms t1  -- 't1' does not depend on any axioms


namespace Hidden

theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.add_succ, ih]

theorem zero_add₂ (n : Nat) : 0 + n = n := by
  cases n with
  | zero => rfl
  | succ n => rw [Nat.add_succ, zero_add₂ n]

theorem zero_add₁ (n : Nat) : 0 + n = n := by
  induction n
  case zero => rfl
  case succ n ih => rw [Nat.add_succ, ih]

theorem add_zero (n : Nat) : n + 0 = n := Nat.add_zero n

open Nat

-- theorem zero_add₃ (n : Nat) : 0 + n = n := by
--   induction n <;> simp [*, Nat.add_zero, Nat.add_succ]

theorem succ_add (m n : Nat) : succ m + n = succ (m + n) := by
  induction n
  case zero => rfl
  case succ n ih => rw [add_succ, ih]; exact rfl

-- theorem add_comm (m n : Nat) : m + n = n + m := by
--   induction n <;> simp [*, add_zero, add_succ, succ_add, zero_add]

-- theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) := by
--   induction k <;> simp [*, add_zero, add_succ]

end Hidden

/-
theorem Nat.mod.inductionOn
      {motive : Nat → Nat → Sort u}
      (x y  : Nat)
      (ind  : ∀ x y, 0 < y ∧ y ≤ x → motive (x - y) y → motive x y)
      (base : ∀ x y, ¬(0 < y ∧ y ≤ x) → motive x y)
      : motive x y :=
-/

example (x : Nat) {y : Nat} (h : y > 0) : x % y < y := by
  induction x, y using Nat.mod.inductionOn with
  | ind x y h₁ ih =>
    rw [Nat.mod_eq_sub_mod h₁.2]
    exact ih h
  | base x y h₁ =>
    have : ¬ 0 < y ∨ ¬ y ≤ x := Iff.mp (Decidable.not_and_iff_or_not ..) h₁
    match this with
    | Or.inl h₁ => exact absurd h h₁
    | Or.inr h₁ =>
      have hgt : y > x := Nat.gt_of_not_le h₁
      rw [← Nat.mod_eq_of_lt hgt] at hgt
      assumption

example : p ∨ q → q ∨ p := by
  intro h
  match h with
  | Or.inl _  => apply Or.inr; assumption
  | Or.inr h2 => apply Or.inl; exact h2

example : s ∧ q ∧ r → p ∧ r → q ∧ p := by
  intro ⟨_, ⟨hq, _⟩⟩ ⟨hp, _⟩
  exact ⟨hq, hp⟩

example : s ∧ q ∧ r → p ∧ r → q ∧ p := by
  intro h₀ h₁
  have hq : q := h₀.2.1
  have hp : p := h₁.1
  exact ⟨hq, hp⟩

example :
    (fun (x : Nat × Nat) (y : Nat × Nat) => x.1 + y.2)
    =
    (fun (x : Nat × Nat) (z : Nat × Nat) => z.2 + x.1) := by
  funext (a, b) (_, d) -- b消せるけど注意でない？
  show a + d = d + a
  rw [Nat.add_comm]

open Nat

example (m n k : Nat) (h : succ (succ m) = succ (succ n))
        : n + k = m + k := by
  injection h with h'
  injection h' with h''
  rw [h'']

open Nat

example (m n : Nat) (h : succ m = 0) : n = n + 7 := by
  injection h

example (m n : Nat) (h : succ m = 0) : n = n + 7 := by
  contradiction

example (h : 7 = 4) : False := by
  contradiction
