/-
  Types as objects
-/

#check Nat               -- Type
#check Bool              -- Type
#check Nat → Bool        -- Type
#check Nat × Bool        -- Type
#check Nat → Nat         -- ...
#check Nat × Nat → Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check Nat → Nat → Bool
#check (Nat → Nat) → Nat

def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check α        -- Type
#check F α      -- Type
#check F Nat    -- Type
#check G α      -- Type → Type
#check G α β    -- Type
#check G α Nat  -- Type

#check Prod α β       -- Type
#check α × β          -- Type

#check Prod Nat Nat   -- Type
#check Nat × Nat      -- Type

#check List α    -- Type
#check List Nat  -- Type

#check Type      -- Type 1

#check Type 1
#check Type 2
#check Type 3
#check Type 4

#check Type
#check Type 0

#check Prop
#check Sort
#check Sort 0

#check Sort 1
#check Sort 2
#check Sort 3
#check Sort 4


#check List    -- List.{u} (α : Type u) : Type u

#check Prod    -- Prod.{u, v} (α : Type u) (β : Type v) : Type (max u v)

universe u
def F' (α : Type u) : Type u := Prod α α       -- `Type u` に属する型 `α` を受け取ると、`α` と `α` の直積型を返す関数
#check F'                                      -- Type u → Type u

def F''.{v} (α : Type v) : Type v := Prod α α

#check F''    -- Type u → Type u

-- universe の指定について

#check Nat

def H₀ (α : Type) : Type := α
def H₁ (α : Type 1) : Type 1 := α
def H₂.{v} (α : Type v) : Type v := α

#check H₀ Nat
-- #check H₁ Nat
#check H₁ Type
#check H₂ Nat
#check H₂ Type
#check H₂ (Type 1)
