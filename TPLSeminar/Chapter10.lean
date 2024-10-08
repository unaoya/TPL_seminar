namespace Ex
structure Add (a : Type) where
  add : a → a → a

#check @Add.add
-- Add.add : {a : Type} → Add a → a → a → a
-- `Add.add` はstructure宣言によって自動生成される射影関数
end Ex

namespace Ex
structure Add (a : Type) where
 add : a → a → a
def double (s : Add a) (x : a) : a :=
  s.add x x

#eval double { add := Nat.add } 10
-- 20

#eval double { add := Nat.mul } 10
-- 100

#eval double { add := Int.add } 10
-- 20
end Ex

namespace Ex
structure Add (a : Type) where
 add : a → a → a
def double (s : Add a) (x : a) : a :=
  s.add x x

#eval double { add := Nat.add } 10
-- 20

#eval double { add := Nat.mul } 10
-- 100

#eval double { add := Int.add } 10
-- 20
end Ex

namespace Ex
class Add (a : Type) where
 add : a → a → a
instance : Add Nat where
  add := Nat.add

instance : Add Int where
  add := Int.add

instance : Add Float where
  add := Float.add
end Ex

namespace Ex
class Add (a : Type) where
  add : a → a → a
instance : Add Nat where
 add := Nat.add
instance : Add Int where
 add := Int.add
instance : Add Float where
 add := Float.add
def double [Add a] (x : a) : a :=
  Add.add x x

#check @double
-- @double : {a : Type} → [inst : Add a] → a → a

#eval double 10
-- 20

#eval double (10 : Int)
-- 20

#eval double (7 : Float)
-- 14.000000

#eval double (239.0 + 2)
-- 482.000000

end Ex

instance [Add a] : Add (Array a) where
  add x y := Array.zipWith x y (· + ·)

#eval Add.add #[1, 2] #[3, 4]
-- #[4, 6]

#eval #[1, 2] + #[3, 4]
-- #[4, 6]

namespace Ex
class Inhabited (a : Type u) where
  default : a

#check @Inhabited.default
-- Inhabited.default : {a : Type u} → [self : Inhabited a] → a
end Ex

namespace Ex
class Inhabited (a : Type _) where
 default : a
instance : Inhabited Bool where
  default := true

instance : Inhabited Nat where
  default := 0

instance : Inhabited Unit where
  default := ()

instance : Inhabited Prop where
  default := True

#eval (Inhabited.default : Nat)
-- 0

#eval (Inhabited.default : Bool)
-- true
end Ex

namespace Ex
class Inhabited (a : Type _) where
 default : a
instance : Inhabited Bool where
 default := true
instance : Inhabited Nat where
 default := 0
instance : Inhabited Unit where
 default := ()
instance : Inhabited Prop where
 default := True
export Inhabited (default)

#eval (default : Nat)
-- 0

#eval (default : Bool)
-- true
end Ex

/-
	Chaining Instances
-/
instance [Inhabited a] [Inhabited b] : Inhabited (a × b) where
  default := (default, default)

namespace Ex
class Inhabited (a : Type u) where
 default : a
instance : Inhabited Bool where
 default := true
instance : Inhabited Nat where
 default := 0
opaque default [Inhabited a] : a :=
 Inhabited.default
instance [Inhabited a] [Inhabited b] : Inhabited (a × b) where
  default := (default, default)

#eval (default : Nat × Bool)
-- (0, true)
end Ex

instance [Inhabited b] : Inhabited (a → b) where
  default := fun _ => default

#check (inferInstance : Inhabited Nat) -- Inhabited Nat

def foo : Inhabited (Nat × Nat) :=
  inferInstance

#eval foo.default  -- (0, 0)

theorem ex : foo.default = (default, default) :=
  rfl

#print inferInstance

/-
	ToString
-/
structure Person where
  name : String
  age  : Nat

instance : ToString Person where
  toString p := p.name ++ "@" ++ toString p.age

#eval toString { name := "Leo", age := 542 : Person }
#eval toString ({ name := "Daniel", age := 18 : Person }, "hello")  -- `instToStringProd` と `instToStringPerson` の連鎖


/-
	Numerals
-/
structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0

instance instOfNatRational (n : Nat) : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"

#eval (2 : Rational) -- 2/1

#check (2 : Rational) -- Rational
#check (2 : Nat)      -- Nat

#check @OfNat.ofNat Nat 2 (instOfNatNat 2)  -- Nat
#check @OfNat.ofNat Rational 2 (instOfNatRational 2)  -- Rational

#check nat_lit 2  -- Nat

class Monoid (α : Type u) where
  unit : α
  op   : α → α → α

instance [s : Monoid α] : OfNat α (nat_lit 1) where
  ofNat := s.unit

def getUnit [Monoid α] : α :=
  1

/-
	Output Parameters
-/
#check_failure (inferInstance : Inhabited (Nat × _))

namespace Ex
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Nat Nat Nat where
  hMul := Nat.mul

instance : HMul Nat (Array Nat) (Array Nat) where
  hMul a bs := bs.map (fun b => hMul a b)

#eval hMul 4 3           -- 12
#eval hMul 4 #[2, 3, 4]  -- #[8, 12, 16]
end Ex

namespace Ex
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Nat Nat Nat where
  hMul := Nat.mul

instance : HMul Int Int Int where
  hMul := Int.mul

instance [HMul α β γ] : HMul α (Array β) (Array γ) where
  hMul a bs := bs.map (fun b => hMul a b)

#eval hMul 4 3                    -- 12
#eval hMul 4 #[2, 3, 4]           -- #[8, 12, 16]
#eval hMul (-2) #[3, -1, 4]       -- #[-6, 2, -8]
#eval hMul 2 #[#[2, 3], #[0, 4]]  -- #[#[4, 6], #[0, 8]]
end Ex

/-
	Default Instances
-/
namespace Ex
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

instance : HMul Int Int Int where
  hMul := Int.mul

def xs : List Int := [1, 2, 3]

-- Error "typeclass instance problem is stuck, it is often due to metavariables HMul ?m.89 ?m.90 ?m.91"
-- `y` の型を明示的に与えればエラーは消える
#check_failure fun y => xs.map (fun x => hMul x y)
end Ex

namespace Ex
class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

@[default_instance]
instance : HMul Int Int Int where
  hMul := Int.mul

def xs : List Int := [1, 2, 3]

#check fun y => xs.map (fun x => hMul x y)    -- Int → List Int
#eval (fun y => xs.map (fun x => hMul x y)) 3 -- [3, 6, 9]
end Ex

structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0

@[default_instance 200]
instance : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"

#check 2 -- Rational

namespace Ex
class OfNat (α : Type u) (n : Nat) where
  ofNat : α

@[default_instance]
instance (n : Nat) : OfNat Nat n where
  ofNat := n

class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

class Mul (α : Type u) where
  mul : α → α → α

@[default_instance 10]
instance [Mul α] : HMul α α α where
  hMul a b := Mul.mul a b

infixl:70 " * " => HMul.hMul
end Ex

/-
	Local Instances
-/
structure Point where
  x : Nat
  y : Nat

section

local instance : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double (p : Point) :=
  p + p

end -- もうインスタンス `Add Point` は使えない

-- def triple (p : Point) :=
--  p + p + p  -- Error: failed to synthesize instance

structure Point where
  x : Nat
  y : Nat

instance addPoint : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double (p : Point) :=
  p + p

attribute [-instance] addPoint

-- def triple (p : Point) :=
--  p + p + p  -- Error: failed to synthesize instance

/-
	Scoped Instances
-/
structure Point where
  x : Nat
  y : Nat

namespace Point

scoped instance : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double (p : Point) :=
  p + p

end Point
-- インスタンス `Add Point` はもう使えない

-- #check fun (p : Point) => p + p + p  -- Error

namespace Point
-- インスタンス `Add Point` は再び利用可能になった
#check fun (p : Point) => p + p + p

end Point

open Point -- 名前空間を開き、インスタンス `Add Point` を利用可能にする
#check fun (p : Point) => p + p + p

structure Point where
  x : Nat
  y : Nat

namespace Point

scoped instance : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double (p : Point) :=
  p + p

end Point

open scoped Point -- インスタンス `Add Point` を利用可能にする
#check fun (p : Point) => p + p + p

-- #check fun (p : Point) => double p -- Error: unknown identifier 'double'

/-
	Decidable Propositions
-/
variable (p : Nat → Prop)

-- error : failed to synthesize instance
--   Decidable (p n)
/-
def bad_foo : Nat → Bool :=
  fun (n : Nat) =>
  if p n then true
  else false
-/

open Classical

noncomputable def foo : Nat → Bool :=
  fun (n : Nat) =>
  if p n then true
  else false

#print axioms foo
-- 'foo' depends on axioms: [Classical.choice, Quot.sound, propext]

namespace Hidden
class inductive Decidable (p : Prop) where
  | isFalse (h : ¬p) : Decidable p
  | isTrue  (h : p)  : Decidable p
end Hidden

namespace Hidden
def ite {α : Sort u} (c : Prop) [h : Decidable c] (t e : α) : α :=
  Decidable.casesOn (motive := fun _ => α) h (fun _ => e) (fun _ => t)
end Hidden

namespace Hidden
def dite {α : Sort u} (c : Prop) [h : Decidable c] (t : c → α) (e : Not c → α) : α :=
  Decidable.casesOn (motive := fun _ => α) h e t
end Hidden

#check @instDecidableAnd
  -- {p q : Prop} → [Decidable p] → [Decidable q] → Decidable (And p q)

#check @instDecidableOr
#check @instDecidableNot

def step (a b x : Nat) : Nat :=
  if x < a ∨ x > b then 0 else 1

set_option pp.explicit true  -- 暗黙の引数を表示する
#print step

open Classical

namespace Hidden
open Classical
noncomputable scoped
instance (priority := low) propDecidable (a : Prop) : Decidable a :=
  choice <| match em a with
    | Or.inl h => ⟨isTrue h⟩
    | Or.inr h => ⟨isFalse h⟩
end Hidden

example : 10 < 5 ∨ 1 > 0 := by
  decide

example : ¬ (True ∧ False) := by
  decide

example : 10 * 20 = 200 := by
  decide

theorem ex : True ∧ 2 = 1+1 := by
  decide

#print ex
-- theorem ex : True ∧ 2 = 1 + 1 :=
-- of_decide_eq_true (Eq.refl true)

#check @of_decide_eq_true
-- ∀ {p : Prop} [Decidable p], decide p = true → p

#check @decide
-- (p : Prop) → [Decidable p] → Bool

/-
	Managing Type Class Instances
-/
def foo : Add Nat := inferInstance
def bar : Inhabited (Nat → Nat) := inferInstance

#check @inferInstance
-- {α : Sort u} → [α] → α

#check (inferInstance : Add Nat)

#check inferInstanceAs (Add Nat)

#check @inferInstanceAs
-- (α : Sort u) → [α] → α

def Set (α : Type u) := α → Prop

-- fails
-- example : Inhabited (Set α) :=
--  inferInstance

instance : Inhabited (Set α) :=
  inferInstanceAs (Inhabited (α → Prop))

-- 別解
example : Inhabited (Set α) :=
  @inferInstance (Inhabited (α → Prop)) _

set_option trace.Meta.synthInstance true

set_option synthInstance.maxHeartbeats 10000
set_option synthInstance.maxSize 400

class Foo where
  a : Nat
  b : Nat

instance (priority := default+1) i1 : Foo where
  a := 1
  b := 1

instance i2 : Foo where
  a := 2
  b := 2

example : Foo.a = 1 :=
  rfl

instance (priority := default+2) i3 : Foo where
  a := 3
  b := 3

example : Foo.a = 3 :=
  rfl

/-
	Coercions using Type Classes
-/
instance : Coe Bool Prop where
  coe b := b = true

#eval if true then 5 else 3
#eval if false then 5 else 3

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

#check let x := ↑[2, 3]; s ∪ x
-- let x := List.toSet [2, 3]; s ∪ x : Set Nat
#check let x := [2, 3]; s ∪ x
-- let x := [2, 3]; s ∪ List.toSet x : Set Nat

instance (p : Prop) [Decidable p] : CoeDep Prop p Bool where
  coe := decide p

    c : (x1 : A1) → ... → (xn : An) → F x1 ... xn → Type u

structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)

instance (S : Semigroup) : Mul S.carrier where
  mul a b := S.mul a b

structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)
instance (S : Semigroup) : Mul S.carrier where
  mul a b := S.mul a b
#check Semigroup.carrier

structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)
instance (S : Semigroup) : Mul S.carrier where
  mul a b := S.mul a b
instance : CoeSort Semigroup (Type u) where
  coe s := s.carrier

example (S : Semigroup) (a b c : S) : (a * b) * c = a * (b * c) :=
  Semigroup.mul_assoc _ a b c


    c : (x1 : A1) → ... → (xn : An) → (y : F x1 ... xn) → (z : B) → C

structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)
instance (S : Semigroup) : Mul S.carrier where
  mul a b := S.mul a b
instance : CoeSort Semigroup (Type u) where
  coe s := s.carrier
structure Morphism (S1 S2 : Semigroup) where
  mor : S1 → S2
  resp_mul : ∀ a b : S1, mor (a * b) = (mor a) * (mor b)

#check @Morphism.mor

structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc (a b c : carrier) : mul (mul a b) c = mul a (mul b c)
instance (S : Semigroup) : Mul S.carrier where
  mul a b := S.mul a b
instance : CoeSort Semigroup (Type u) where
  coe s := s.carrier
structure Morphism (S1 S2 : Semigroup) where
  mor : S1 → S2
  resp_mul : ∀ a b : S1, mor (a * b) = (mor a) * (mor b)
instance (S1 S2 : Semigroup) : CoeFun (Morphism S1 S2) (fun _ => S1 → S2) where
  coe m := m.mor

theorem resp_mul {S1 S2 : Semigroup} (f : Morphism S1 S2) (a b : S1)
        : f (a * b) = f a * f b :=
  f.resp_mul a b

example (S1 S2 : Semigroup) (f : Morphism S1 S2) (a : S1) :
      f (a * a * a) = f a * f a * f a :=
  calc f (a * a * a)
    _ = f (a * a) * f a := by rw [resp_mul f]
    _ = f a * f a * f a := by rw [resp_mul f]
