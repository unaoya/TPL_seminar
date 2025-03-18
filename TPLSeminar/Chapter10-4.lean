/-
	Numerals
-/

structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0

#check OfNat

instance instOfNatRational (n : Nat) : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }

instance : ToString Rational where
  toString r := s!"{r.num}/{r.den}"

#eval (2 : Rational) -- 2/1

#check 2
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

def getUnit [Monoid α] : α := 1
