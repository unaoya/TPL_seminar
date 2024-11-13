/-
  Exercises
-/

variable (p q r : Prop)

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h : p ∨ q =>
      Or.elim h (fun hp : p => Or.inr hp) (fun hq : q => Or.inl hq))
    (fun h : q ∨ p =>
      Or.elim h (fun hq : q => Or.inr hq) (fun hp : p => Or.inl hp))

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h => h.elim (fun hp => Or.inr hp) (fun hq => Or.inl hq))
    (fun h : q ∨ p =>
      Or.elim h (fun hq : q => Or.inr hq) (fun hp : p => Or.inl hp))

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      Or.elim h.right
        (fun hq : q => Or.inl ⟨h.left, hq⟩)
        (fun hr : r => Or.inr ⟨h.left, hr⟩))
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
        (fun hpq : p ∧ q => And.intro hpq.left (Or.inl hpq.right))
        (fun hpr : p ∧ r => And.intro hpr.left (Or.inr hpr.right)))


example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun h : p → q → r =>
      fun hpq : p ∧ q =>
        h hpq.left hpq.right)
    (fun h : p ∧ q → r =>
      fun hp : p =>
        fun hq : q =>
          h ⟨hp, hq⟩)


example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun h : ¬(p ∨ q) =>
      And.intro
        (fun hp : p => h (Or.inl hp))
        (fun hq : q => h (Or.inr hq)))
    (fun h : ¬p ∧ ¬q =>
      fun hpq : p ∨ q =>
        Or.elim hpq
          (fun hp : p => h.left hp)
          (fun hq : q => h.right hq))

-- ∧ と ∨ の可換性
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q => And.intro h.right h.left)
    (fun h : q ∧ p => And.intro h.right h.left)


-- ∧ と ∨ の結合性
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := sorry
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

-- 分配性

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- 他の性質

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry



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

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  fun h : p → q ∨ r =>
    byCases
      (fun hpq : p → q =>
        Or.inl hpq)
      (fun hnp : ¬(p → q) =>
        Or.inr -- : (p → r) -> (p → q) ∨ (p → r)
          (fun hp : p =>
            Or.elim  -- : (q ∨ r) (q → r) (r → r) → r
              (h hp) -- : q ∨ r
              (fun hq : q =>
                (False.elim -- : False → r
                  (hnp (fun _ => hq))))
              id -- : r → r
          )
      )


example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
example : ¬(p → q) → p ∧ ¬q := sorry
example : (p → q) → (¬p ∨ q) := sorry
example : (¬q → ¬p) → (p → q) := sorry
example : p ∨ ¬p := sorry
example : (((p → q) → p) → p) := sorry


-- α : Type, P : α → Prop, (a : α => P a : Prop)
-- ∀ a : α, P a を証明、(h a : P a)_{a : α}
