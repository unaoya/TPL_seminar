/-
	Inheritance
-/
structure Point (α : Type u) where
  x : α
  y : α

#check Point

inductive Color where
  | red | green | blue

structure ColorPoint (α : Type u) extends Point α where
  c : Color

#check ColorPoint.c

structure Point3 (α : Type u) where
  x : α
  y : α
  z : α

structure RGBValue where
  red : Nat
  green : Nat
  blue : Nat

structure RedGreenPoint (α : Type u) extends Point3 α, RGBValue where
  no_blue : blue = 0

def p : Point3 Nat :=
  { x := 10, y := 10, z := 20 }

def rgp : RedGreenPoint Nat :=
  { p with red := 200, green := 40, blue := 0, no_blue := rfl }

example : rgp.x   = 10 := rfl
example : rgp.red = 200 := rfl
example : rgp.blue = 0 := rgp.no_blue
