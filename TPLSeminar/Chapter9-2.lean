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

structure Point' (α : Type u) where
  x : α
  y : α
  deriving Repr

def p : Point Nat :=
  { x := 1, y := 2 }

#eval { p with y := 3 }  -- { x := 1, y := 3 }
#eval { p with x := 4 }  -- { x := 4, y := 2 }

def p' : Point' Nat :=
  { x := 1, y := 2 }

#eval { p' with y := 3 }  -- { x := 1, y := 3 }
#eval { p' with x := 4 }  -- { x := 4, y := 2 }

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
