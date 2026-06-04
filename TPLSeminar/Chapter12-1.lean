/-
	Propositional Extensionality
-/

#check propext

namespace Hidden

axiom propext {a b : Prop} : (a ↔ b) → a = b
#check propext

end Hidden

theorem thm₀ (a b c d e : Prop) (h : a ↔ b) : (c ∧ a ∧ d → e) ↔ (c ∧ b ∧ d → e) :=
  propext h ▸ Iff.refl _

theorem thm₁ (a b c d e : Prop) (h : a ↔ b) : (c ∧ a ∧ d → e) ↔ (c ∧ b ∧ d → e) :=
  propext h ▸ Iff.refl _

theorem thm₃ (a b : Prop) (p : Prop → Prop) (h : a = b) (h₁ : p a) : p b :=
  h ▸ h₁

theorem thm₂ (a b : Prop) (p : Prop → Prop) (h : a ↔ b) (h₁ : p a) : p b :=
  (propext h) ▸ h₁

#print axioms thm₁  -- 'thm₁' depends on axioms: [propext]
#print axioms thm₂  -- 'thm₂' depends on axioms: [propext]
#print axioms thm₃  -- 'thm₃' does not depend on any axioms

/-
	Function Extensionality
-/
universe u v
#check (@funext :
           {α : Type u}
         → {β : α → Type u}
         → {f g : (x : α) → β x}
         → (∀ (x : α), f x = g x)
         → f = g)

#print funext

def Set (α : Type u) := α → Prop

namespace Set

def mem (x : α) (a : Set α) : Prop := a x

infix:50 (priority := high) "∈" => mem

theorem setext {a b : Set α} (h : ∀ (x : α), x ∈ a ↔ x ∈ b) : a = b :=
  funext (fun x => propext (h x))

theorem setext' {a b : Set α} (h : ∀ (x : α), a x ↔ b x) : a = b :=
  funext (fun x => propext (h x))

def empty : Set α := fun x => False

notation (priority := high) "∅" => empty

example (x : α) : ¬(x ∈ ∅) := by
  intro h
  exact h

example (x : α) : ¬(x ∈ ∅) := fun h => h

example (x : α) : ¬(x ∈ ∅) := id

def inter (a b : Set α) : Set α :=
  fun x => x ∈ a ∧ x ∈ b

infix:70 " ∩ " => inter

theorem inter_self (a : Set α) : a ∩ a = a :=
  setext fun (x : α) => Iff.intro
    (fun ⟨h, _⟩ => h)
    (fun h => ⟨h, h⟩)

theorem inter_empty (a : Set α) : a ∩ ∅ = ∅ :=
  setext fun x => Iff.intro
    (fun ⟨_, h⟩ => h)
    (fun h => False.elim h)

theorem empty_inter (a : Set α) : ∅ ∩ a = ∅ :=
  setext fun x => Iff.intro
    (fun ⟨h, _⟩ => h)
    (fun h => False.elim h)

theorem inter.comm (a b : Set α) : a ∩ b = b ∩ a :=
  setext fun x => Iff.intro
    (fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩)
    (fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩)
end Set

def f (x : Nat) := x
def g (x : Nat) := 0 + x

theorem f_eq_g : f = g :=
  funext fun x => (Nat.zero_add x).symm

def val : Nat :=
  Eq.recOn (motive := fun _ _ => Nat) (t := f_eq_g) 0

-- Eq.recOn.{u, u_1} {α : Sort u_1} :
-- {a : α} → {motive : (a_1 : α) → a = a_1 → Sort u} →
-- {a_1 : α} → (t : a = a_1) → motive a ⋯ → motive a_1 t

-- (t := f_eq_g : f = g) (a := f) (a_1 := g) (α := Nat → Nat)
-- (motive : (x : Nat → Nat) → (f = x) → Type := fun _ _ => Nat)
-- 0 : (motive f := (f = f) → Type := fun _ => Nat)
-- (motive g f_eq_g := Nat)

-- does not reduce to 0
#reduce val

-- evaluates to 0
#eval val

theorem tteq : (True ∧ True) = True :=
  propext (Iff.intro (fun ⟨h, _⟩ => h) (fun h => ⟨h, h⟩))

def val₁ : Nat :=
  Eq.recOn (motive := fun _ _ => Nat) tteq 0

-- does not reduce to 0
#reduce val₁

-- evaluates to 0
#eval val₁

-- Quotients

#check Quot

namespace Hidden

axiom Quot : {α : Sort u} → (α → α → Prop) → Sort u

axiom Quot.mk : {α : Sort u} → (r : α → α → Prop) → α → Quot r

axiom Quot.ind :
    ∀ {α : Sort u} {r : α → α → Prop} {β : Quot r → Prop},
      (∀ a, β (Quot.mk r a)) → (q : Quot r) → β q

axiom Quot.lift :
    {α : Sort u} → {r : α → α → Prop} → {β : Sort u} → (f : α → β)
    → (∀ a b, r a b → f a = f b) → Quot r → β

end Hidden

def mod7Rel (x y : Nat) : Prop :=
  x % 7 = y % 7

-- 商型 `Quot mod7Rel`
#check (Quot mod7Rel : Type)

-- `4` を含む `mod7Rel`-(同値)類
#check (Quot.mk mod7Rel 4 : Quot mod7Rel)

def f₀ (x : Nat) : Bool :=
  x % 7 = 0

theorem f_respects (a b : Nat) (h : mod7Rel a b) : f₀ a = f₀ b := by
  simp [mod7Rel, f₀] at *
  rw [h]

def f' (x : Quot mod7Rel) : Bool :=
  Quot.lift f₀ f_respects x

#check (f' : Quot mod7Rel → Bool)

-- 計算原理
example (a : Nat) : f' (Quot.mk mod7Rel a) = f₀ a :=
  rfl

variable (α β : Type)
variable (r : α → α → Prop)
variable (a : α)
variable (f : α → β)
variable (h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂)

theorem thm : Quot.lift f h (Quot.mk r a) = f a := rfl

#print axioms thm   -- 'thm' does not depend on any axioms

namespace Hidden

axiom Quot.sound :
      ∀ {α : Type u} {r : α → α → Prop} {a b : α},
        r a b → Quot.mk r a = Quot.mk r b
end Hidden

theorem thm' (x y : α) (h : r x y) : Quot.mk r x = Quot.mk r y :=
  Quot.sound h

#print axioms thm' -- 'thm'' depends on axioms: [Quot.sound]


namespace Hidden

class Setoid (α : Sort u) where
  r : α → α → Prop
  iseqv : Equivalence r

instance {α : Sort u} [Setoid α] : HasEquiv α :=
  ⟨Setoid.r⟩

namespace Setoid

variable {α : Sort u} [Setoid α]

theorem refl (a : α) : a ≈ a :=
  iseqv.refl a

theorem symm {a b : α} (hab : a ≈ b) : b ≈ a :=
  iseqv.symm hab

theorem trans {a b c : α} (hab : a ≈ b) (hbc : b ≈ c) : a ≈ c :=
  iseqv.trans hab hbc

end Setoid
end Hidden

namespace Hidden
def Quotient {α : Sort u} (s : Setoid α) :=
  @Quot α Setoid.r
end Hidden

#check Quotient
#check Quotient.exact

#print axioms Quotient.exact -- 'Quotient.exact' depends on axioms: [propext]

#check (@Quotient.exact :
         ∀ {α : Sort u} {s : Setoid α} {a b : α},
           Quotient.mk s a = Quotient.mk s b → a ≈ b)

#check Quotient.sound
