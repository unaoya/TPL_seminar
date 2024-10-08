
/-
  Local Definitions
-/

#check let y := 2 + 2; y * y   -- Nat
#eval  let y := 2 + 2; y * y   -- 16

def double_square (x : Nat) : Nat :=
  let y := x + x;y * y

#eval double_square 2   -- 16

#check let y := 2 + 2; let z := y + y; z * z   -- Nat
#eval  let y := 2 + 2; let z := y + y; z * z   -- 64

def double_square' (x : Nat) : Nat :=
  let y := x + x
  y * y

def foo := let a := Nat; fun x : a => x + 2

def bar := (fun a => fun x : a => x + 2) Nat

def baz := fun a => fun x : a => 1 + 2

#check HAdd
