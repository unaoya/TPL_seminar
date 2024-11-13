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

structure Proof (p : Prop) : Type where
  proof : p

#check Proof   -- Proof (p : Prop) : Type
#check Proof p

axiom and_comm' (p q : Prop) : Proof (Implies (And p q) (And q p))

#check and_comm' p q     -- and_comm p q : Proof (Implies (p ∧ q) (q ∧ p))
#check and_comm' q p     -- and_comm q p : Proof (Implies (q ∧ p) (p ∧ q))

axiom modus_ponens : (p q : Prop) → Proof (Implies p q) → Proof p → Proof q

axiom implies_intro : (p q : Prop) → (Proof p → Proof q) → Proof (Implies p q)

variable (h : p) (f : p → q)
example : q := (f h)

variable (h : Proof p) (f : Proof (Implies p q))
noncomputable
example : Proof q := modus_ponens p q f h

variable (h h' : p)
example : h = h' := rfl

#check Nat

-- α : Sort u, β : α →  β : Sort (u-1)
-- Nat : Sort 1, 1 : Nat, 1 : Sort0?

-- p : Type u, a : p

variable (p : Type u) (a : p)
#check a
