/-
  More on Namespaces
-/

section
variable (x y : Nat)

def double := x + x

#check double y
#check double (2 * x)

attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

theorem t1 : double (x + y) = double x + double y := by
  simp [double]

#check t1 y
#check t1 (2 * x)

theorem t2 : double (x * y) = double x * y := by
  simp [double, Nat.add_mul]

end

def Foo.bar : Nat := 1

namespace Foo
def bar : Nat := 1
end Foo

def String.add (a b : String) : String :=
  a ++ b

def Bool.add (a b : Bool) : Bool :=
  a != b

def add (α β : Type) : Type := Sum α β

open Bool
open String
-- #check add -- これは曖昧である
#check String.add           -- String → String → String
#check Bool.add             -- Bool → Bool → Bool
#check _root_.add           -- Type → Type → Type

#check add "hello" "world"  -- String
#check add true false       -- Bool
#check add Nat Nat          -- Type

protected def Foo.bar : Nat := 1

open Foo

-- #check bar -- error
#check Foo.bar

open Nat (succ zero gcd)
#check zero     -- Nat
#eval gcd 15 6  -- 3

open Nat hiding succ gcd
#check zero     -- Nat
-- #eval gcd 15 6  -- error
#eval Nat.gcd 15 6  -- 3

open Nat renaming mul → times, add → plus
#eval plus (times 2 2) 3  -- 7
-- #eval mul 1 2          -- error
#eval Nat.mul 1 2         -- 2

namespace Foo
export And (intro left right)

#check And.intro  -- And.intro {a b : Prop} (left : a) (right : b) : a ∧ b
#check Foo.intro  -- And.intro {a b : Prop} (left : a) (right : b) : a ∧ b
#check intro      -- And.intro {a b : Prop} (left : a) (right : b) : a ∧ b
#check left       -- And.left {a b : Prop} (self : a ∧ b) : a
end Foo

-- #check intro   -- error

export And (intro left right)
#check intro      -- And.intro {a b : Prop} (left : a) (right : b) : a ∧ b
-- #check _root_.intro  -- error
