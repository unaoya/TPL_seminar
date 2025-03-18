namespace Ex

structure Add (a : Type) where
  add : a → a → a

#check @Add.add
-- Add.add : {a : Type} → Add a → a → a → a
-- `Add.add` はstructure宣言によって自動生成される射影関数

def double (s : Add a) (x : a) : a :=
  s.add x x

#eval double { add := Nat.add } 10
-- 20

#eval double { add := Nat.mul } 10
-- 100

#eval double { add := Int.add } 10
-- 20

#check @double

end Ex

namespace Ex2

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

#eval double 10
-- 20

#eval double (10 : Int)
-- 20

#eval double (7 : Float)
-- 14.000000

#eval double (239.0 + 2)
-- 482.000000

#check @double
-- @double : {a : Type} → [inst : Add a] → a → a

instance [Add a] : Add (Array a) where
  add x y := Array.zipWith x y Add.add

#eval Add.add #[1, 2] #[3, 4]
-- #[4, 6]

-- #eval #[1, 2] + #[3, 4]
-- -- #[4, 6]

class Inhabited (a : Type u) where
  default : a

#check @Inhabited.default
-- Inhabited.default : {a : Type u} → [self : Inhabited a] → a

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

export Inhabited (default)

#eval (default : Nat)
-- 0

#eval (default : Bool)
-- true
