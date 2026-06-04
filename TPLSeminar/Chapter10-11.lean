/-
	Coercions using Type Classes
-/

instance : Coe Bool Prop where
  coe b := b = true

-- namespace Hidden
-- def ite {α : Sort u} (c : Prop) [h : Decidable c] (t e : α) : α :=
--   Decidable.casesOn (motive := fun _ => α) h (fun _ => e) (fun _ => t)

-- -- attribute [-instance] : Coe Bool Prop
-- #check (inferInstance : Coe Bool Prop)

-- #eval ite true 5 3

-- end Hidden
#eval if true then 5 else 3
#eval if false then 5 else 3

-- def f (b : Bool) : Nat := if b then 0 else 1

def Set (α : Type u) := α → Prop

def Set.empty {α : Type u} : Set α := fun _ => False

def Set.mem (a : α) (s : Set α) : Prop := s a

def Set.singleton (a : α) : Set α := fun x => x = a

def Set.union (a b : Set α) : Set α := fun x => a x ∨ b x

notation "{ " a " }" => Set.singleton a

infix:55 " ∪ " => Set.union

def List.toSet : List α → Set α
  | []    => Set.empty
  | a::as => {a} ∪ as.toSet

instance : Coe (List α) (Set α) where
  coe a := a.toSet

def s : Set Nat := {1}
#check s ∪ [2, 3]
-- s ∪ List.toSet [2, 3] : Set Nat

#check let x := ↑[2, 3]; s ∪ x
-- let x := List.toSet [2, 3]; s ∪ x : Set Nat

#check let x := [2, 3]; s ∪ x
-- let x := [2, 3]; s ∪ List.toSet x : Set Nat

instance (p : Prop) [Decidable p] : CoeDep Prop p Bool where
  coe := decide p


-- c : (x1 : A1) → ... → (xn : An) → F x1 ... xn → Type u

structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)

#check Semigroup

def NatSemigrp : Semigroup := {
  carrier := Nat,
  mul := Nat.mul,
  mul_assoc := Nat.mul_assoc
}

#check NatSemigrp

instance (S : Semigroup) : Mul S.carrier where
  mul a b := S.mul a b

#check Semigroup.carrier


-- #check Semigroup.carrier NatSemigrp

instance : CoeSort Semigroup (Type u) where
  coe s := s.carrier

example (S : Semigroup) (a b c : S) : (a * b) * c = a * (b * c) :=
  Semigroup.mul_assoc _ a b c

example (a b c : NatSemigrp) : a * b * c = a * (b * c) :=
  Semigroup.mul_assoc _ a b c

structure Morphism (S1 S2 : Semigroup) where
  mor : S1 → S2
  resp_mul : ∀ a b : S1, mor (a * b) = (mor a) * (mor b)

#check Morphism

instance (S1 S2 : Semigroup) : CoeFun (Morphism S1 S2) (fun _ => S1 → S2) where
  coe m := m.mor

theorem resp_mul {S1 S2 : Semigroup} (f : Morphism S1 S2) (a b : S1)
        : f (a * b) = f a * f b :=
  f.resp_mul a b

#check @Morphism.mor

example (S1 S2 : Semigroup) (f : Morphism S1 S2) (a : S1) :
      f (a * a * a) = f a * f a * f a :=
  calc f (a * a * a)
    _ = f (a * a) * f a := by rw [resp_mul f]
    _ = f a * f a * f a := by rw [resp_mul f]
