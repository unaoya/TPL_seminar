/-
  Simple Type Theory
-/

-- def <項の名前(識別子)> : <項の型> := <項の定義式>
def m : Nat := 1           -- `m` は自然数型を持つ
def b1 : Bool := true      -- `b1` はブール型を持つ
def b2 : Bool := false

-- #check <項>
#check m                   -- output: Nat
#check b1                  -- output: Bool
#check and
#check and b1 b2
#check b1 && b2            -- `&&` は「かつ」 output: Bool
#check or
#check b1 || b2            -- `||` は「または」 output: Bool

-- #eval <項>
#eval 5 * 4                -- 20
#eval m + 2                -- 3
#eval b1 && b2             -- false

#check Nat
#check Nat → Nat                   -- `→` は "\to" あるいは "\r" と打つと入力できる
#check Nat -> Nat                  -- `->` は `→` のASCII表記

#check Nat × Nat                   -- `×` は "\times" と打つと入力できる
#check Prod Nat Nat                -- `Prod Nat Nat` は `Nat × Nat` のASCII表記

#check Nat → Nat → Nat
#check Nat → (Nat → Nat)           -- これは1つ上と同じである。つまり、`→` は右結合的である
#check Nat × Nat → Nat
#check Nat × (Nat → Nat)
#check (Nat × Nat) → Nat
#check (Nat → Nat) → Nat           -- 関数を受け取る関数の型

#check Nat.succ                    -- Nat → Nat
#check (0, 1)                      -- Nat × Nat
#check Prod.mk
#check Prod.mk 0
#check Prod.mk 0 1                 -- Nat × Nat
#check Nat.add                     -- Nat → Nat → Nat

#check Nat.succ 2                  -- Nat
#check Nat.add 3                   -- Nat → Nat
#check Nat.add 3 2                 -- Nat
#check (5, 9).1                    -- Nat
#check (5, 9).2                    -- Nat

#eval Nat.succ 2                   -- 3
#eval Nat.add 5 2                  -- 7
#eval (5, 9).1                     -- 5
#eval (5, 9).2                     -- 9
#eval Nat.add (10, 7).1 (10, 7).2  -- 17
