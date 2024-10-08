
/-
  Function Abstraction and Evaluation
-/


-- 括弧は省略可能
-- fun (<入力引数の名前> : <入力引数の型名>) => <関数の出力を定義する式>
-- λ (<入力引数の名前> : <入力引数の型名>) => <関数の出力を定義する式>
#check fun (x : Nat) => x + 5   -- Nat → Nat
#check λ (x : Nat) => x + 5     -- `λ` と `fun` は同じ意味
#check fun x => x + 5           -- `x` は `Nat` 型だと推論される
#check λ x => x + 5             -- `x` は `Nat` 型だと推論される

#eval (λ x : Nat => x + 5) 10    -- 15

#check ite
#check ite true
#check ite true 1
#check ite true Nat
#check ite true 1 1

#check fun x : Nat => (fun y : Bool => (if not y then x + 1 else x + 2))

def f₀ (x : Nat) (y : Bool) : Nat := if not y then x + 1 else x + 2
#eval f₀ 10 true
#eval f₀ 10 false

#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2   -- Nat → Bool → Nat

def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#check fun x : Nat => x        -- Nat → Nat
#check fun x : Nat => true     -- Nat → Bool
#check fun x : Nat => g (f x)  -- Nat → Bool
#check fun x => g (f x)        -- Nat → Bool
#check fun x => x

#check fun (g : String → Bool) (f : Nat → String) (x : Nat) => g (f x)
-- (String → Bool) → (Nat → String) → Nat → Bool

#check fun (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => g (f x)
def f₁.{u} (α β γ : Type u) (g : β → γ) (f : α → β) (x : α) : γ := g (f x)
#check f₁ Nat String Bool

-- α同値について
-- rflで証明できる？

def b : Nat := 0
#check fun (α β : Type) (b : β) (x : α) => b
#check (fun (α β : Type) (b : β) (x : α) => b) _ _ b
#check (fun (α β : Type) (b : β) (x : α) => b) _ _ b true

example (α : Type) : (fun (x : α) => x) = (fun (y : α) => y) := rfl

-- t : α → β, s : α, t s : β
#check (fun x : Nat => x) 1     -- Nat
#check (fun x : Nat => true) 1  -- Bool

#check
  (fun (α β γ : Type) (u : β → γ) (v : α → β) (x : α) => u (v x)) Nat String Bool g f 0
  -- Bool

#eval (fun x : Nat => x) 1     -- 1
#eval (fun x : Nat => true) 1  -- true
#eval (fun (α β γ : Type) (u : β → γ) (v : α → β) (x : α) => u (v x)) Nat String Bool g f 0  -- true
