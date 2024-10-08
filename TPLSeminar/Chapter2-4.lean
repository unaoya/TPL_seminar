/-
  Definitions
-/

-- def <関数の名前> (<入力引数の名前> : <入力引数の型>) : <出力の型> := <出力を定義する式>

def double (x : Nat) : Nat :=
  x + x

#eval double 3    -- 6

def double' : Nat → Nat :=
  fun x => x + x

#eval double' 3    -- 6

def double'' :=
  fun (x : Nat) => x + x

#eval double'' 3    -- 6

example : double = double' := rfl

-- def foo : α := bar

def pi := 3.141592654

def add (x y : Nat) :=
  x + y

#eval add 3 2               -- 5

def add' (x : Nat) (y : Nat) :=
  x + y

#eval add (double 3) (7 + 9)  -- 22

def greater (x y : Nat) :=
  if x > y then x
  else y

#check ite

#check 7 > 6

#eval greater 7 6             -- 7
#eval greater 99 100          -- 100
#eval greater 5 5             -- 5

def square :=
  fun (x : Nat) => x * x

def doTwice (f : Nat → Nat) (x : Nat) : Nat :=
  f (f x)

#eval doTwice double 2        -- 8
#eval doTwice square 3        -- 81

def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

#eval compose _ _ _ double square 3        -- 18
#eval compose Nat Nat Nat square double 3        -- 36


-- iteだと同じ型でしかできない、真偽で違う型の項を返したい時にどうするか？
