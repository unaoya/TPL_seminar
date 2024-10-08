/-
  Propositions as Types
-/

def Implies (p q : Prop) : Prop := p → q
#check And     -- Prop → Prop → Prop
#check Or      -- Prop → Prop → Prop
#check Not     -- Prop → Prop
#check Implies -- Prop → Prop → Prop

variable (p q r : Prop)
#check And p q                      -- Prop
#check Or (And p q) r               -- Prop
#check Implies (And p q) (And q p)  -- Prop

def Implies (p q : Prop) : Prop := p → q
structure Proof (p : Prop) : Type where
  proof : p
#check Proof   -- Proof (p : Prop) : Type

axiom and_comm (p q : Prop) : Proof (Implies (And p q) (And q p))

variable (p q : Prop)
#check and_comm p q     -- and_comm p q : Proof (Implies (p ∧ q) (q ∧ p))
#check and_comm q p     -- and_comm q p : Proof (Implies (q ∧ p) (p ∧ q))

def Implies (p q : Prop) : Prop := p → q
structure Proof (p : Prop) : Type where
  proof : p
axiom modus_ponens : (p q : Prop) → Proof (Implies p q) → Proof p → Proof q

def Implies (p q : Prop) : Prop := p → q
structure Proof (p : Prop) : Type where
  proof : p
axiom implies_intro : (p q : Prop) → (Proof p → Proof q) → Proof (Implies p q)

/-
  Working with Propositions as Types
-/

variable {p : Prop}
variable {q : Prop}

theorem t1 : p → q → p := fun hp : p => fun hq : q => hp

variable {p : Prop}
variable {q : Prop}
theorem t1 : p → q → p := fun hp : p => fun hq : q => hp

#print t1    -- ∀ {p q : Prop}, p → q → p := fun {p q} hp hq => hp

variable {p : Prop}
variable {q : Prop}
theorem t1 : p → q → p :=
  fun hp : p =>
  fun hq : q =>
  show p from hp      -- show <型> from <項>

variable {p : Prop}
variable {q : Prop}
theorem t1 (hp : p) (hq : q) : p := hp

#print t1    -- p → q → p

variable {p : Prop}
variable {q : Prop}
theorem t1 (hp : p) (hq : q) : p := hp

axiom hp : p

theorem t2 : q → p := t1 hp

axiom unsound : False
-- `False`(偽)からは任意の命題を示すことができる
theorem ex : 1 = 0 :=    -- 本来は偽の命題
  False.elim unsound


theorem t1 {p q : Prop} (hp : p) (hq : q) : p := hp

#print t1    -- ∀ {p q : Prop}, p → q → p := fun {p q} hp hq => hp

theorem t1 : ∀ {p q : Prop}, p → q → p :=
  fun {p q : Prop} (hp : p) (hq : q) => hp

variable {p q : Prop}

theorem t1 : p → q → p := fun (hp : p) (hq : q) => hp

#print t1    -- ∀ {p q : Prop}, p → q → p := fun {p q} hp hq => hp

variable {p q : Prop}
variable (hp : p)

theorem t1 : q → p := fun (hq : q) => hp

#print t1    -- ∀ {p q : Prop}, p → q → p := fun {p q} hp hq => hp

theorem t1 (p q : Prop) (hp : p) (hq : q) : p := hp

variable (p q r s : Prop)

#check t1 p q                -- p → q → p
#check t1 r s                -- r → s → r
#check t1 (r → s) (s → r)    -- (r → s) → (s → r) → r → s

variable (h : r → s)
#check t1 (r → s) (s → r) h  -- (s → r) → r → s

variable (p q r s : Prop)

theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun h₃ : p =>
  show r from h₁ (h₂ h₃)

/-
  Propositional Logic
-/

variable (p q : Prop)

#check p → q → p ∧ q
#check ¬p → p ↔ False
#check p ∨ q → q ∨ p

variable (p q : Prop)

example (hp : p) (hq : q) : p ∧ q := And.intro hp hq

#check fun (hp : p) (hq : q) => And.intro hp hq

variable (p q : Prop)

example (h : p ∧ q) : p := And.left h
example (h : p ∧ q) : q := And.right h

variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  And.intro (And.right h) (And.left h)

variable (p q : Prop)
variable (hp : p) (hq : q)

#check (⟨hp, hq⟩ : p ∧ q)

variable (xs : List Nat)

#check List.length xs
#check xs.length

variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  ⟨h.right, h.left⟩

variable (p q : Prop)

example (h : p ∧ q) : q ∧ p ∧ q :=
  ⟨h.right, ⟨h.left, h.right⟩⟩

example (h : p ∧ q) : q ∧ p ∧ q :=
  ⟨h.right, h.left, h.right⟩

variable (p q : Prop)
example (hp : p) : p ∨ q := Or.intro_left q hp
example (hq : q) : p ∨ q := Or.intro_right p hq

variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p :=
  Or.elim h
    (fun hp : p =>
      show q ∨ p from Or.intro_right q hp)
    (fun hq : q =>
      show q ∨ p from Or.intro_left p hq)

variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p :=
  Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq)

variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p :=
  h.elim (fun hp => Or.inr hp) (fun hq => Or.inl hq)

variable (p q : Prop)

example (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun hp : p =>
  show False from hnq (hpq hp)

variable (p q : Prop)

example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)


variable (p q : Prop)

example (hp : p) (hnp : ¬p) : q := absurd hp hnp

variable (p q r : Prop)

example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
  absurd (hqp hq) hnp

variable (p q : Prop)

theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
     show q ∧ p from And.intro (And.right h) (And.left h))
    (fun h : q ∧ p =>
     show p ∧ q from And.intro (And.right h) (And.left h))

#check and_swap p q    -- p ∧ q ↔ q ∧ p

variable (h : p ∧ q)
example : q ∧ p := Iff.mp (and_swap p q) h

variable (p q : Prop)

theorem and_swap : p ∧ q ↔ q ∧ p :=
  ⟨ fun h => ⟨h.right, h.left⟩, fun h => ⟨h.right, h.left⟩ ⟩

example (h : p ∧ q) : q ∧ p := (and_swap p q).mp h

/-
  Introducing Auxiliary Subgoals
-/

variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from And.intro hq hp

variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from And.intro hq hp
  show q from And.right h

/-
  Classical Logic
-/

open Classical

variable (p : Prop)
#check em p      -- p ∨ ¬p

open Classical

theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)

open Classical
variable (p : Prop)

example (h : ¬¬p) : p :=
  byCases
    (fun h1 : p => h1)
    (fun h1 : ¬p => absurd h1 h)
open Classical
variable (p : Prop)

example (h : ¬¬p) : p :=
  byContradiction
    (fun h1 : ¬p =>
     show False from h h1)

open Classical
variable (p q : Prop)
example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
  Or.elim (em p)
    (fun hp : p =>
      Or.inr
        (show ¬q from
          fun hq : q =>
          h ⟨hp, hq⟩))
    (fun hp : ¬p =>
      Or.inl hp)

/-
  Examples of Propositional Validities
-/

open Classical

-- 分配性
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      have hp : p := h.left
      Or.elim (h.right)
        (fun hq : q =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨hp, hq⟩)
        (fun hr : r =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨hp, hr⟩))
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
        (fun hpq : p ∧ q =>
          have hp : p := hpq.left
          have hq : q := hpq.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inl hq⟩)
        (fun hpr : p ∧ r =>
          have hp : p := hpr.left
          have hr : r := hpr.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inr hr⟩))

-- 古典論理を必要とする例
example (p q : Prop) : ¬(p ∧ ¬q) → (p → q) :=
  fun h : ¬(p ∧ ¬q) =>
  fun hp : p =>
  show q from
    Or.elim (em q)
      (fun hq : q => hq)
      (fun hnq : ¬q => absurd (And.intro hp hnq) h)


/-
  Exercises
-/

variable (p q r : Prop)

-- ∧ と ∨ の可換性
example : p ∧ q ↔ q ∧ p := sorry
example : p ∨ q ↔ q ∨ p := sorry

-- ∧ と ∨ の結合性
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := sorry
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

-- 分配性
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- 他の性質
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry

open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := sorry
example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
example : ¬(p → q) → p ∧ ¬q := sorry
example : (p → q) → (¬p ∨ q) := sorry
example : (¬q → ¬p) → (p → q) := sorry
example : p ∨ ¬p := sorry
example : (((p → q) → p) → p) := sorry
