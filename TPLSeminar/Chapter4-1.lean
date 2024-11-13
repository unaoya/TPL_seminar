/-
  The Universal Quantifier
-/

#check And
#check Exists

example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun y : α => (h y).left
  -- show p y from (h y).left

theorem h (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun y : α => (h y).left
  -- show p y from (h y).left

example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ x : α, p x := h α p q
  -- fun h : ∀ x : α, p x ∧ q x =>
  -- fun z : α =>
  -- show p z from And.left (h z)

variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ x y z, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r                -- ∀ (x y z : α), r x y → r y z → r x z
/- (r : α → α → Prop) と 「r x y → r y z → r x z」により x,y,z の型が推論されている -/
#check trans_r a b c          -- r a b → r b c → r a c
#check trans_r a b c hab      -- r b c → r a c
#check trans_r a b c hab hbc  -- r a c

variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r          -- r ?m.1 ?m.2 → r ?m.2 ?m.3 → r ?m.1 ?m.3
#check trans_r hab      -- r b ?m.42 → r a ?m.42
#check trans_r hab hbc  -- r a c

variable (α : Type) (r : α → α → Prop)

variable (refl_r : ∀ x, r x x)
variable (symm_r : ∀ {x y}, r x y → r y x)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  trans_r (trans_r hab (symm_r hcb)) hcd

universe i j
#check fun α : Sort i => fun β : Sort j => (x : α) → β
#check fun α : Sort 1 => fun β : Sort 2 => (x : α) → β
#check fun α : Sort 2 => fun β : Sort 1 => (x : α) → β
#check fun α : Sort 0 => fun β : Sort 1 => (x : α) → β
#check fun α : Sort 1 => fun β : Sort 0 => (x : α) → β

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun h : (∀ x, p x) ∨ (∀ x, q x) =>
    fun x : α =>
      Or.elim h
        (fun h₁ : ∀ x, p x => Or.inl (h₁ x))
        (fun h₂ : ∀ x, q x => Or.inr (h₂ x))
