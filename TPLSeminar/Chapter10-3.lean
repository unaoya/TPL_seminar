/-
	ToString
-/

structure Person where
  name : String
  age  : Nat

#check (inferInstance : ToString Nat)  -- ToString Nat

instance : ToString Person where
  toString p := p.name ++ "@" ++ toString p.age

#check instToStringProd

#eval toString { name := "Leo", age := 542 : Person }
#eval toString ({ name := "Daniel", age := 18 : Person }, "hello")  -- `instToStringProd` と `instToStringPerson` の連鎖
