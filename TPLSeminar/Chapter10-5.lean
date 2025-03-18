/-
	Output Parameters
-/

#check_failure (inferInstance : Inhabited (Nat × _))

-- class HMul (α : Type u) (β : Type v) (γ : Type w) where
--   hMul : α → β → γ

namespace Ex

class HMul (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  hMul : α → β → γ

export HMul (hMul)

variable (α β : Type u) (f : Nat → α) (g : Nat → β)

instance : HMul Nat Nat Nat where
  hMul := Nat.mul

instance : HMul Nat Nat Int where
  hMul := (fun n m ↦ (Nat.mul n m))

instance : HMul Nat (Array Nat) (Array Nat) where
  hMul a bs := bs.map (fun b => hMul a b)

#check hMul 4 3
#eval hMul 4 3          -- 12
#eval hMul 4 #[2, 3, 4]  -- #[8, 12, 16]

instance : HMul Int Int Int where
  hMul := Int.mul

instance [HMul α β γ] : HMul α (Array β) (Array γ) where
  hMul a bs := bs.map (fun b => hMul a b)

#eval hMul 4 3                    -- 12
#eval hMul 4 #[2, 3, 4]           -- #[8, 12, 16]
#eval hMul (-2) #[3, -1, 4]       -- #[-6, 2, -8]
#eval hMul 2 #[#[2, 3], #[0, 4]]  -- #[#[4, 6], #[0, 8]]
