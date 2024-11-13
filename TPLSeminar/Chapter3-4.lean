/-
  Introducing Auxiliary Subgoals
-/

variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from And.intro hq hp
-- have h : p := s; t

-- (fun (h : p) => t) s
example (h : p ∧ q) : q ∧ p :=
  (fun (hp : p) (hq : q) => And.intro hq hp) h.left h.right

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from And.intro hq hp
  show q from And.right h
