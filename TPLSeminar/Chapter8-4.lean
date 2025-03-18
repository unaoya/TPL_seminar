/-
	Local Recursive Declarations
-/

def f (n : Nat) : Nat :=
  let m := n + 1
  m + 1

def replicate (n : Nat) (a : α) : List α :=
  let rec loop : Nat → List α → List α
    | 0,   as => as
    | n+1, as => loop n (a::as)
  loop n []

example : replicate 3 true = [true, true, true] := rfl

#check @replicate.loop
-- {α : Type} → α → Nat → List α → List α

theorem length_replicate (n : Nat) (a : α) : (replicate n a).length = n := by
  let rec aux (n : Nat) (as : List α)
              : (replicate.loop a n as).length = n + as.length := by
    match n with
    | 0   => simp [replicate.loop]
    | n+1 =>
      simp [replicate.loop, aux n]
      rw [Nat.add_assoc, Nat.add_comm _ 1]
  exact aux n []


def f₁ (n : Nat) : Nat :=
  m + 1
  where m := n + 1

def replicate₁ (n : Nat) (a : α) : List α :=
  loop n []
where
  loop : Nat → List α → List α
    | 0,   as => as
    | n+1, as => loop n (a::as)

theorem length_replicate₁ (n : Nat) (a : α) : (replicate n a).length = n := by
  exact aux n []
where
  aux (n : Nat) (as : List α)
      : (replicate.loop a n as).length = n + as.length := by
    match n with
    | 0   => simp [replicate.loop]
    | n+1 =>
      simp [replicate.loop, aux n]
      rw [Nat.add_assoc, Nat.add_comm _ 1]
