/-
	Declaring Structures
-/
structure Point (α : Type u) where
  mk :: (x : α) (y : α)

structure Point (α : Type u) where
 mk :: (x : α) (y : α)
#check Point       -- a Type
#check @Point.rec  -- the eliminator
#check @Point.mk   -- the constructor
#check @Point.x    -- a projection
#check @Point.y    -- a projection

structure Point (α : Type u) where
  x : α
  y : α

structure Point (α : Type u) where
 x : α
 y : α
#eval Point.x (Point.mk 10 20)
#eval Point.y (Point.mk 10 20)

open Point

example (a b : α) : x (mk a b) = a :=
  rfl

example (a b : α) : y (mk a b) = b :=
  rfl

structure Point (α : Type u) where
 x : α
 y : α
def p := Point.mk 10 20

#check p.x  -- Nat
#eval p.x   -- 10
#eval p.y   -- 20

structure Point (α : Type u) where
  x : α
  y : α
  deriving Repr

def Point.add (p q : Point Nat) :=
  mk (p.x + q.x) (p.y + q.y)

def p : Point Nat := Point.mk 1 2
def q : Point Nat := Point.mk 3 4

#eval p.add q  -- {x := 4, y := 6}

structure Point (α : Type u) where
 x : α
 y : α
 deriving Repr
def Point.smul (n : Nat) (p : Point Nat) :=
  Point.mk (n * p.x) (n * p.y)

def p : Point Nat := Point.mk 1 2

#eval p.smul 3  -- {x := 3, y := 6}

#check @List.map

def xs : List Nat := [1, 2, 3]
def f : Nat → Nat := fun x => x * x

#eval xs.map f  -- [1, 4, 9]

/-
	Objects
-/
structure Point (α : Type u) where
  x : α
  y : α

#check { x := 10, y := 20 : Point Nat }    -- { (<field-name> := <expr>)* : structure-type }
#check { y := 20, x := 10 : Point _ }      -- フィールドを指定する順番は任意
#check ({ x := 10, y := 20 } : Point Nat)  -- { (<field-name> := <expr>)* } 構造体の型が明らか

example : Point Nat :=
  { y := 20, x := 10 }                     -- { (<field-name> := <expr>)* } 構造体の型が明らか

structure MyStruct where
    {α : Type u}
    {β : Type v}
    a : α
    b : β

#check { a := 10, b := true : MyStruct }

structure Point (α : Type u) where
  x : α
  y : α
  deriving Repr

def p : Point Nat :=
  { x := 1, y := 2 }

#eval { p with y := 3 }  -- { x := 1, y := 3 }
#eval { p with x := 4 }  -- { x := 4, y := 2 }

structure Point3 (α : Type u) where
  x : α
  y : α
  z : α

def q : Point3 Nat :=
  { x := 5, y := 5, z := 5 }

def r : Point3 Nat :=
  { p, q with x := 6 }

example : r.x = 6 := rfl
example : r.y = 2 := rfl
example : r.z = 5 := rfl

/-
	Inheritance
-/
structure Point (α : Type u) where
  x : α
  y : α

inductive Color where
  | red | green | blue

structure ColorPoint (α : Type u) extends Point α where
  c : Color

structure Point (α : Type u) where
  x : α
  y : α
  z : α

structure RGBValue where
  red : Nat
  green : Nat
  blue : Nat

structure RedGreenPoint (α : Type u) extends Point α, RGBValue where
  no_blue : blue = 0

def p : Point Nat :=
  { x := 10, y := 10, z := 20 }

def rgp : RedGreenPoint Nat :=
  { p with red := 200, green := 40, blue := 0, no_blue := rfl }

example : rgp.x   = 10 := rfl
example : rgp.red = 200 := rfl
