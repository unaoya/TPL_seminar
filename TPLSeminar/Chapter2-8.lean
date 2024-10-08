/-
  What makes dependent type theory dependent?
-/

#check List

-- #check Vector a n

def cons (α : Type) (a : α) (as : List α) : List α :=
  List.cons a as

#check cons Nat        -- Nat → List Nat → List Nat
#check cons Bool       -- Bool → List Bool → List Bool

-- α : Type, β : α → Type
-- (a : α) → β a
-- α → β = β ^ α = ∏_α β

#check cons
-- (a : Type) → (a → List a → List a)
-- (a : α) → β a = ∏_(a : α) β_a

def cons' : (a : Type) → a → List a → List a :=
  fun a x xs => List.cons x xs

def f (n : Nat) : Nat := n + 1
def f' : Nat → Nat := fun n => n + 1

#check List.cons    -- {α : Type u_1} → α → List α → List α
#check @List.cons    -- {α : Type u_1} → α → List α → List α
#check @List.nil     -- {α : Type u_1} → List α
#check @List.length  -- {α : Type u_1} → List α → Nat
#check @List.append  -- {α : Type u_1} → List α → List α → List α

universe u v

-- α × β = ⨿(a : α) β
-- (a : α) × β = ⨿(a : α) β_a

def f'' (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a :=
  ⟨a, b⟩

def g (α : Type u) (β : α → Type v) (a : α) (b : β a) : Σ a : α, β a :=
  Sigma.mk a b

#print f''
#print g

#check (a : Type) × List a
#check Σ a : Type, List a

def h1 (x : Nat) : Nat :=
  (f'' _ (fun α => α) _ x).2

#eval h1 5 -- 5

def h2 (x : Nat) : Nat :=
  (g Type (fun α => α) Nat x).2

#eval h2 5 -- 5

def i : Type :=                 -- iは ``Nat`` 型のこと
  (f'' _ (fun α => α) _ 1).1

def test : i := 5 + 5

#eval test -- 10


-- BoolじゃなくてPropにできる？
def β : Bool → Type
  | true  => Nat
  | false => Bool

def fn : (a : Bool) → β a := fun a => match a with
  | true  => Nat.zero
  | false => false
