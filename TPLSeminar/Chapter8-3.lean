/-
	Structual Recursion and Induction
-/
open Nat
def add : Nat → Nat → Nat
  | m, zero   => m
  | m, succ n => succ (add m n)

theorem add_zero (m : Nat)   : add m zero = m := rfl
theorem add_succ (m n : Nat) : add m (succ n) = succ (add m n) := rfl

theorem zero_add : ∀ n, add zero n = n
  | zero   => rfl
  | succ n => congrArg succ (zero_add n)

def mul : Nat → Nat → Nat
  | n, zero   => zero
  | n, succ m => add (mul n m) n

theorem mul_zero (m : Nat)   : mul m zero = zero := rfl
theorem mul_succ (m n : Nat) : mul m (succ n) = add (mul m n) m := rfl

theorem zero_add₁ : ∀ n, add zero n = n
  | zero   => by simp [add]
  | succ n => by simp [add, zero_add]

def add₁ (m : Nat) : Nat → Nat
  | zero   => m
  | succ n => succ (add m n)


/- `match` を使う場合はもちろん `:=` が必要になる -/

def add₂ (m n : Nat) : Nat :=
  match n with
  | zero   => m
  | succ n => succ (add m n)

def fib : Nat → Nat
  | 0   => 1
  | 1   => 1
  | n+2 => fib (n+1) + fib n

example : fib 0 = 1 := rfl
example : fib 1 = 1 := rfl
example : fib (n + 2) = fib (n + 1) + fib n := rfl

example : fib 7 = 21 := rfl

def fibFast (n : Nat) : Nat :=
  (loop n).2
where
  loop : Nat → Nat × Nat
    | 0   => (0, 1)
    | n+1 => let p := loop n; (p.2, p.1 + p.2)

#eval fibFast 100

def fibFast₂ (n : Nat) : Nat :=
  let rec loop : Nat → Nat × Nat
    | 0   => (0, 1)
    | n+1 => let p := loop n; (p.2, p.1 + p.2)
  (loop n).2

variable (C : Nat → Type u)

#check (@Nat.below C : Nat → Type u)

#reduce @Nat.below C (3 : Nat)

#check (@Nat.brecOn C : (n : Nat) → ((n : Nat) → @Nat.below C n → C n) → C n)


-- #eval fib 50 -- slow
#reduce fib 50  -- fast

#print fib

def append : List α → List α → List α
  | [],    bs => bs
  | a::as, bs => a :: append as bs

example : append [1, 2, 3] [4, 5] = [1, 2, 3, 4, 5] := rfl

def listAdd [Add α] : List α → List α → List α
  | [],      _       => []
  | _,       []      => []
  | a :: as, b :: bs => (a + b) :: listAdd as bs

#eval listAdd [1, 2, 3] [4, 5, 6, 6, 9, 10]
-- [5, 7, 9]
