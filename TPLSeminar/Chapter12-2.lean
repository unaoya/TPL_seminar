private def eqv (p₁ p₂ : α × α) : Prop :=
  (p₁.1 = p₂.1 ∧ p₁.2 = p₂.2) ∨ (p₁.1 = p₂.2 ∧ p₁.2 = p₂.1)

infix:50 " ~ " => eqv

private theorem eqv.refl (p : α × α) : p ~ p :=
  Or.inl ⟨rfl, rfl⟩

private theorem eqv.symm : ∀ {p₁ p₂ : α × α}, p₁ ~ p₂ → p₂ ~ p₁
  | (a₁, a₂), (b₁, b₂), (Or.inl ⟨a₁b₁, a₂b₂⟩) =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (Or.inr ⟨a₁b₂, a₂b₁⟩) =>
    Or.inr (by simp_all)

private theorem eqv.trans : ∀ {p₁ p₂ p₃ : α × α}, p₁ ~ p₂ → p₂ ~ p₃ → p₁ ~ p₃
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inl (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inl ⟨a₁b₁, a₂b₂⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inl ⟨b₁c₁, b₂c₂⟩ =>
    Or.inr (by simp_all)
  | (a₁, a₂), (b₁, b₂), (c₁, c₂), Or.inr ⟨a₁b₂, a₂b₁⟩, Or.inr ⟨b₁c₂, b₂c₁⟩ =>
    Or.inl (by simp_all)

private theorem is_equivalence : Equivalence (@eqv α) :=
  { refl := eqv.refl, symm := eqv.symm, trans := eqv.trans }

instance uprodSetoid (α : Type u) : Setoid (α × α) where
  r := eqv
  iseqv := is_equivalence

def UProd (α : Type u) : Type u :=
  Quotient (uprodSetoid α)

namespace UProd

def mk {α : Type} (a₁ a₂ : α) : UProd α :=
  Quotient.mk' (a₁, a₂)

notation "{ " a₁ ", " a₂ " }" => mk a₁ a₂

theorem mk_eq_mk (a₁ a₂ : α) : {a₁, a₂} = {a₂, a₁} :=
  Quot.sound (Or.inr ⟨rfl, rfl⟩)

private def mem_fn (a : α) : α × α → Prop
  | (a₁, a₂) => a = a₁ ∨ a = a₂

-- auxiliary lemma for proving mem_respects
private theorem mem_swap {a : α} :
      ∀ {p : α × α}, mem_fn a p = mem_fn a (⟨p.2, p.1⟩)
  | (a₁, a₂) => by
    apply propext
    apply Iff.intro
    . intro
      | Or.inl h => exact Or.inr h
      | Or.inr h => exact Or.inl h
    . intro
      | Or.inl h => exact Or.inr h
      | Or.inr h => exact Or.inl h

private theorem mem_respects
      : {p₁ p₂ : α × α} → (a : α) → p₁ ~ p₂ → mem_fn a p₁ = mem_fn a p₂
  | (a₁, a₂), (b₁, b₂), a, Or.inl ⟨a₁b₁, a₂b₂⟩ => by simp_all
  | (a₁, a₂), (b₁, b₂), a, Or.inr ⟨a₁b₂, a₂b₁⟩ => by
    rw [mem_swap]
    rw [a₁b₂, a₂b₁]

def mem (a : α) (u : UProd α) : Prop :=
  Quot.liftOn u (fun p => mem_fn a p) (fun p₁ p₂ e => mem_respects a e)

infix:50 (priority := high) " ∈ " => mem

theorem mem_mk_left (a b : α) : a ∈ {a, b} :=
  Or.inl rfl

theorem mem_mk_right (a b : α) : b ∈ {a, b} :=
  Or.inr rfl

theorem mem_or_mem_of_mem_mk {a b c : α} : c ∈ {a, b} → c = a ∨ c = b :=
  fun h => h
end UProd

section

-- variable (α : Type u) (β : α → Type v)

-- def equiv (f g : (x : α) → β x) : Prop :=
--   ∀ (x : α), f x = g x

-- theorem is_equivalence' : Equivalence (equiv α β) := sorry

-- instance extfun' : Setoid ((x : α) → β x) where
--   r := equiv α β
--   iseqv := is_equivalence' α β

-- @[simp]
-- theorem hoge {f g : ((x : α) → β x) × α} (h : f ≈ g) (x : α) : f.1 x = g.1 x := by
--   sorry

-- def extfun_app : Quotient (extfun' α β) → (x : α) → β x :=
--   Quotient.lift (fun f x => f.1 x)
--     (by intro a b h; simp; sorry)

-- #check funext

#check Quot.liftOn
-- Quot.liftOn.{u, v} {α : Sort u} {β : Sort v} {r : α → α → Prop} (q : Quot r) (f : α → β)
--   (c : ∀ (a b : α), r a b → f a = f b) : β

#check Quot.sound
-- Quot.sound.{u} {α : Sort u} {r : α → α → Prop} {a b : α} : r a b → Quot.mk r a = Quot.mk r b

#check congrArg
-- congrArg.{u, v} {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β) (h : a₁ = a₂) : f a₁ = f a₂

theorem funext' {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}
    (h : ∀ x, f x = g x) : f = g := by
  let eqv (f g : (x : α) → β x) := ∀ x, f x = g x
  let extfunApp (f : Quot eqv) (x : α) : β x :=
    Quot.liftOn (r := eqv) (q := f) -- α := (x : α) → β x, β := β x
      (fun (f : ∀ (x : α), β x) => f x)
      (fun a b (h : eqv a b) => (h x : a x = b x))
  have : extfunApp (Quot.mk eqv f) = f := rfl
  show extfunApp (Quot.mk eqv f) = extfunApp (Quot.mk eqv g)
  exact congrArg (f := extfunApp) (Quot.sound h)

#print axioms funext'

/-
	Choice
-/

namespace Hidden
class inductive Nonempty (α : Sort u) : Prop where
  | intro (val : α) : Nonempty α
end Hidden

example (α : Type u) : Nonempty α ↔ ∃ x : α, True :=
  Iff.intro (fun ⟨a⟩ => ⟨a, trivial⟩) (fun ⟨a, _⟩ => Nonempty.intro a)

namespace Hidden

universe u
axiom choice {α : Sort u} : Nonempty α → α

noncomputable def indefiniteDescription
    {α : Sort u} (p : α → Prop)
    (h : ∃ x, p x) : {x // p x} :=
  choice <| let ⟨x, px⟩ := h; ⟨⟨x, px⟩⟩
  -- hはNonempty {x // p x}と思える
  -- choiceによって{x // p x}の型を持つ項を作れる

open Classical

noncomputable def choose {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : α :=
  (indefiniteDescription p h).val

theorem choose_spec {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : p (choose h) :=
  (indefiniteDescription p h).property

noncomputable def inhabited_of_nonempty : Nonempty α → Inhabited α :=
  fun h => choice (let ⟨a⟩ := h; ⟨⟨a⟩⟩)

#check strongIndefiniteDescription
#print strongIndefiniteDescription
-- Classical.strongIndefiniteDescription.{u}
--   {α : Sort u} (p : α → Prop) (h : Nonempty α) :
--   { x // (∃ y, p y) → p x }

#check epsilon
-- Classical.epsilon.{u} {α : Sort u} [h : _root_.Nonempty α] (p : α → Prop) : α

#check (@epsilon_spec :
         ∀ {α : Sort u} {p : α → Prop} (hex : ∃ (y : α), p y),
           p (@epsilon _ (nonempty_of_exists hex) p))

/-
	The Law of Excluded Middle
-/
open Classical

#check (@em : ∀ (p : Prop), p ∨ ¬p)

#print axioms em

namespace Hidden
open Classical

theorem em (p : Prop) : p ∨ ¬p :=

  let U (x : Prop) : Prop := x = True ∨ p
  let V (x : Prop) : Prop := x = False ∨ p

  have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
  have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩

  -- Hidden.choose.{u} {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : α
  let u : Prop := choose (α := Prop) (p := U) (exU : ∃ x, U x)
  let v : Prop := choose (α := Prop) (p := V) (exV : ∃ x, V x)

  have u_def : U u := choose_spec exU
  have v_def : V v := choose_spec exV

  have not_uv_or_p : u ≠ v ∨ p :=
    match u_def, v_def with
    | Or.inr h, _ => Or.inr h
    | _, Or.inr h => Or.inr h
    | Or.inl hut, Or.inl hvf =>
      have hne : u ≠ v := by
        rw [hvf, hut]
        exact true_ne_false
      Or.inl hne

  have p_implies_uv : p → u = v :=
    fun (hp : p) =>
    have hpred : U = V :=
      funext fun (x : Prop) =>
        have hl : (x = True ∨ p) → (x = False ∨ p) :=
          fun _ => Or.inr hp
        have hr : (x = False ∨ p) → (x = True ∨ p) :=
          fun _ => Or.inr hp
        show (x = True ∨ p) = (x = False ∨ p) from
          propext (Iff.intro hl hr)
    have h₀ : ∀ exU exV, @choose _ U exU = @choose _ V exV := by
      rw [hpred];
      intros;
      exact rfl
    h₀ _ _

  match not_uv_or_p with
  | Or.inl hne => Or.inr (mt p_implies_uv hne)
  | Or.inr h   => Or.inl h

end Hidden

namespace Hidden
open Classical

theorem propComplete (a : Prop) : a = True ∨ a = False :=
  match em a with
  | Or.inl ha => Or.inl (propext (Iff.intro (fun _ => ⟨⟩) (fun _ => ha)))
  | Or.inr hn => Or.inr (propext (Iff.intro (fun h => hn h) (fun h => False.elim h)))

end Hidden

namespace Hidden

class inductive Decidable (p : Prop) where
  | isFalse (h : ¬p) : Decidable p
  | isTrue  (h : p)  : Decidable p

end Hidden

open Classical

noncomputable def linv [Inhabited α] (f : α → β) : β → α :=
  fun b : β => if ex : (∃ a : α, f a = b) then choose ex else default

theorem linv_comp_self {f : α → β} [Inhabited α]
    (inj : ∀ {a b}, f a = f b → a = b) : linv f ∘ f = id :=
  funext fun a =>
    have ex  : ∃ a₁ : α, f a₁ = f a := ⟨a, rfl⟩
    have feq : f (choose ex) = f a  := choose_spec ex
    calc linv f (f a)
      _ = choose ex := by dsimp [linv]
      _ = a         := inj feq
