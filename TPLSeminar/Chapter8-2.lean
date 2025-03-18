/-
	Wildcards and Overlapping Patterns
-/

def foo : Nat → Nat → Nat
  | 0,   _   => 0
  | _+1, 0   => 1
  | _+1, _+1 => 2

def foo₁ : Nat → Nat → Nat
  | 0, _ => 0
  | _, 0 => 1
  | _, _ => 2

example : foo 0     0     = 0 := rfl
example : foo 0     (n+1) = 0 := rfl
example : foo (m+1) 0     = 1 := rfl
example : foo (m+1) (n+1) = 2 := rfl

def foo₂ : Nat → Nat → Nat
  | 0, _ => 0
  | _, 0 => 1
  | _, _ => 2

def f1 : Nat → Nat → Nat
  | 0, _  => 1
  | _, 0  => 2
  | _, _  => default  -- the "incomplete" case
#eval f1 1 1

#check Inhabited
#check Inhabited.default
#check (inferInstance : Inhabited Nat).default
#eval (inferInstance : Inhabited Nat).default

-- instance : Inhabited Nat := ⟨1⟩

-- #eval (inferInstance : Inhabited Nat).default

-- def f2 : Nat → Nat → Nat
--   | 0, _  => 1
--   | _, 0  => 2
--   | _, _  => default  -- the "incomplete" case

-- #eval f2 1 1

example : f1 0     0     = 1       := rfl
example : f1 0     (a+1) = 1       := rfl
example : f1 (a+1) 0     = 2       := rfl
example : f1 (a+1) (b+1) = default := rfl

def f2 : Nat → Nat → Option Nat
  | 0, _  => some 1
  | _, 0  => some 2
  | _, _  => none     -- the "incomplete" case

example : f2 0     0     = some 1 := rfl
example : f2 0     (a+1) = some 1 := rfl
example : f2 (a+1) 0     = some 2 := rfl
example : f2 (a+1) (b+1) = none   := rfl

def bar : Nat → List Nat → Bool → Nat
  | 0,   _,      false => 0
  | 0,   b :: _, _     => b
  | 0,   [],     true  => 7
  | a+1, [],     false => a
  | a+1, [],     true  => a + 1
  | a+1, b :: _, _     => a + b

def foo₃ : Char → Nat
  | 'A' => 1
  | 'B' => 2
  | _   => 3

#print foo.match_1
