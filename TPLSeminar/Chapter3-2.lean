/-
  Working with Propositions as Types
-/

section
variable {p q : Prop}

theorem t1 : p → (q → p) :=
  fun hp : p =>
  fun _ : q => hp

#print t1    -- ∀ {p q : Prop}, p → q → p := fun {p q} hp hq => hp

theorem t1' : p → q → p :=
  fun hp : p =>
  fun hq : q =>
  show p from hp      -- show <型> from <項>

theorem t1'' (hp : p) (hq : q) : p := hp

#print t1'    -- p → q → p
#print t1''    -- p → q → p

axiom hp : p

theorem t2 : q → p := t1 hp

axiom unsound : False
-- `False`(偽)からは任意の命題を示すことができる
theorem ex : 1 = 0 :=    -- 本来は偽の命題
  False.elim unsound

theorem t1 {p q : Prop} (hp : p) (hq : q) : p := hp

#print t1    -- ∀ {p q : Prop}, p → q → p := fun {p q} hp hq => hp

theorem t1 : ∀ {p q : Prop}, p → q → p :=
  fun {p q : Prop} (hp : p) (hq : q) => hp

theorem t1 : p → q → p := fun (hp : p) (hq : q) => hp

#print t1    -- ∀ {p q : Prop}, p → q → p := fun {p q} hp hq => hp

variable (hp : p)

theorem t1''' : q → p := fun (hq : q) => hp

#print t1'''    -- ∀ {p q : Prop}, p → q → p := fun {p q} hp hq => hp

end

section
theorem t3 (p q : Prop) (hp : p) (hq : q) : p := hp

variable (p q r s : Prop)

#check t3 p q                -- p → q → p
#check t3 r s                -- r → s → r
#check t3 (r → s) (s → r)    -- (r → s) → (s → r) → r → s

variable (h : r → s)
#check t3 _ (s → r) h  -- (s → r) → r → s

theorem t4 (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun h₃ : p =>
  show r from h₁ (h₂ h₃)
