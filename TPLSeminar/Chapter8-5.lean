/-
	Well-Founded Recursion and Induction
-/
variable (α : Sort u)
variable (r : α → α → Prop)

#check (Acc r : α → Prop)
#check (WellFounded r : Prop)

noncomputable def f {α : Sort u}
      (r : α → α → Prop)
      (h : WellFounded r)
      (C : α → Sort v)
      (F : (x : α) → ((y : α) → r y x → C y) → C x)
      : (x : α) → C x := WellFounded.fix h F

open Nat

theorem div_lemma {x y : Nat} : 0 < y ∧ y ≤ x → x - y < x :=
  fun h => sub_lt (Nat.lt_of_lt_of_le h.left h.right) h.left

def div.F (x : Nat) (f : (x₁ : Nat) → x₁ < x → Nat → Nat) (y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    (f (x - y) (div_lemma h) y) + 1
  else
    zero

noncomputable def div := WellFounded.fix (measure id).wf div.F

#reduce div 8 2 -- 4

namespace Hidden₁

def div₁ (x y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    -- have : x - y < x := Nat.sub_lt (Nat.lt_of_lt_of_le h.1 h.2) h.1
    (div₁ (x - y) y) + 1
  else
    0

end Hidden₁

def div₂ (x y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
  --  have : x - y < x := Nat.sub_lt (Nat.lt_of_lt_of_le h.1 h.2) h.1
    div₂ (x - y) y + 1
  else
    0

example (x y : Nat) : div x y = if 0 < y ∧ y ≤ x then div (x - y) y + 1 else 0 := by
  conv => lhs; unfold div -- 等式の左辺の `div` を展開する
  sorry
  -- exact?

-- example (x y : Nat) (h : 0 < y ∧ y ≤ x) : div x y = div (x - y) y + 1 := by
--   conv => lhs; unfold div
--   simp [h]


-- 1/14ここまで

def natToBin : Nat → List Nat
  | 0     => [0]
  | 1     => [1]
  | n + 2 =>
    have : (n + 2) / 2 < n + 2 := sorry
    natToBin ((n + 2) / 2) ++ [n % 2]

#eval natToBin 1234567

def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)
termination_by x y => (x, y)

#check (inferInstance : WellFoundedRelation Nat)

#eval ack 3 5
-- アッカーマン関数は入力値の増加に伴い出力値が急速に増加する関数であり、
-- 例えば `#eval ack 4 1` などはバッファオーバーフロー等のエラーを引き起こす可能性が高いため、
-- 実行しないことをお勧めする。

instance (priority := low) [SizeOf α] : WellFoundedRelation α :=
  sizeOfWFRel

variable {α : Type}

-- Array `as` を先頭から見て、
-- `as` の要素 `a` が `p a` を満たす限りArray `r` に `a` を追加し、`r` を返す関数
def takeWhile (p : α → Bool) (as : Array α) : Array α :=
  go 0 #[]
where
  go (i : Nat) (r : Array α) : Array α :=
    if h : i < as.size then
      let a := as.get ⟨i, h⟩
      if p a then
        go (i+1) (r.push a)
      else
        r
    else
      r
termination_by as.size - i

#eval takeWhile (fun n : Nat => if n % 2 = 1 then true else false) #[1, 3, 5, 6, 7]

theorem div_lemma' {x y : Nat} : 0 < y ∧ y ≤ x → x - y < x :=
  fun ⟨ypos, ylex⟩ => Nat.sub_lt (Nat.lt_of_lt_of_le ypos ylex) ypos

def div₀ (x y : Nat) : Nat :=
  if h : 0 < y ∧ y ≤ x then
    div₀ (x - y) y + 1
  else
    0
decreasing_by apply div_lemma'; assumption

def ack' : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack' x 1
  | x+1, y+1 => ack' x (ack' (x+1) y)
termination_by x y => (x, y)
decreasing_by
  all_goals simp_wf -- unfolds well-founded recursion auxiliary definitions
  · apply Prod.Lex.left; simp_arith
  · apply Prod.Lex.right; simp_arith
  · apply Prod.Lex.left; simp_arith

def natToBin' : Nat → List Nat
  | 0     => [0]
  | 1     => [1]
  | n + 2 => natToBin' ((n + 2) / 2) ++ [n % 2]
decreasing_by simp_wf; simp_arith; exact div_le_self n 2

#eval natToBin 1234567

def unsound (x : Nat) : False :=
  unsound (x + 1)
decreasing_by sorry

#check unsound 0
-- `unsound 0` is a proof of `False`

#print axioms unsound
-- 'unsound' depends on axioms: [sorryAx]
