/-
	Default Instances
-/

def xs : List Int := [1, 2, 3]

-- Error "typeclass instance problem is stuck, it is often due to metavariables HMul ?m.89 ?m.90 ?m.91"
-- `y` の型を明示的に与えればエラーは消える
#check_failure fun y => xs.map (fun x => hMul x y)

@[default_instance]
instance : HMul Int Int Int where
  hMul := Int.mul

#check fun y => xs.map (fun x => hMul x y)    -- Int → List Int
#eval (fun y => xs.map (fun x => hMul x y)) 3 -- [3, 6, 9]

@[default_instance 200]
instance : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"

#check 2 -- Rational

class OfNat (α : Type u) (n : Nat) where
  ofNat : α

@[default_instance]
instance (n : Nat) : OfNat Nat n where
  ofNat := n

class Mul (α : Type u) where
  mul : α → α → α

@[default_instance 10]
instance [Mul α] : HMul α α α where
  hMul a b := Mul.mul a b

infixl:70 " * " => HMul.hMul
