/-
  Coercions
-/

variable (m n : Nat)
variable (i j : Int)

#check i + m      -- i + Int.ofNat m : Int
#check i + m + j  -- i + Int.ofNat m + j : Int
#check i + m + n  -- i + Int.ofNat m + Int.ofNat n : Int

#check (m + n) + i  -- i + Int.ofNat m + Int.ofNat n : Int

#check ((m + n)) + i
