/-
  Implicit Arguments
-/


universe u

def Lst (α : Type u) : Type u := List α
def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil (α : Type u) : Lst α := List.nil
def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs

#check Lst          -- Lst.{u} (α : Type u) : Type u
#check Lst.cons     -- Lst.cons.{u} (α : Type u) (a : α) (as : Lst α) : Lst α
#check Lst.nil      -- Lst.nil.{u} (α : Type u) : Lst α
#check Lst.append   -- Lst.append.{u} (α : Type u) (as bs : Lst α) : Lst α

#check Lst.cons Nat 0 (Lst.nil Nat)      -- Lst Nat
#eval Lst.cons Nat 0 (Lst.nil Nat)       -- [0]

def as : Lst Nat := Lst.nil Nat
def bs : Lst Nat := Lst.cons Nat 5 (Lst.nil Nat)

#check Lst.append Nat as bs              -- Lst Nat
#eval Lst.append Nat as bs               -- [5]

#check Lst.cons _ 0 (Lst.nil _)      -- Lst Nat

def as' : Lst Nat := Lst.nil _
def bs' : Lst Nat := Lst.cons _ 5 (Lst.nil _)

#check Lst.append _ as bs            -- Lst Nat


def Lst.cons' {α : Type u} (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil' {α : Type u} : Lst α := List.nil
def Lst.append' {α : Type u} (as bs : Lst α) : Lst α := List.append as bs

#check Lst.cons' 0 Lst.nil'      -- Lst Nat

def as'' : Lst Nat := Lst.nil'
def bs'' : Lst Nat := Lst.cons' 5 Lst.nil'

#check Lst.append' as bs        -- Lst Nat

def ident {α : Type u} (x : α) := x

#check ident         -- ?m → ?m
#check ident 1       -- Nat
#check ident "hello" -- String
#check @ident        -- {α : Type u_1} → α → α

#check @ident Nat 1
-- #check @ident 1


section
  variable {α : Type u}
  variable (x : α)
  def ident' := x
end

#check ident           -- {α : Type u_1} → α → α
#check ident 4         -- Nat
#check ident "hello"   -- String

#check List.nil               -- List ?m
#check id                     -- ?m → ?m

#check (List.nil : List Nat)  -- List Nat
#check (id : Nat → Nat)       -- Nat → Nat

#check 2            -- Nat
#check (2 : Nat)    -- Nat
#check (2 : Int)    -- Int


#check @id        -- {α : Sort u_1} → α → α
#check @id Nat    -- Nat → Nat
#check @id Bool   -- Bool → Bool

#check @id Nat 1     -- Nat
#check @id Bool true -- Bool
