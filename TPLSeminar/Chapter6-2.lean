/-
  More on Namespaces
-/

def bar : Nat := 1

def Foo.b : Nat := 3

namespace Foo

def bar : Nat := 2

#eval bar
#eval Foo.bar

#eval b

end Foo

#eval bar
#eval Foo.bar

#eval Foo.b


def String.add (a b : String) : String :=
  a ++ b

def Bool.add (a b : Bool) : Bool :=
  a != b

def add (α β : Type) : Type := Sum α β

#check add -- これは曖昧である

open String
#check add -- これは曖昧である

open Bool
#check add -- これは曖昧である

#check add -- これは曖昧である
#check String.add           -- String → String → String
#check Bool.add             -- Bool → Bool → Bool
#check _root_.add           -- Type → Type → Type

#check add "hello" "world"  -- String
#check add true false       -- Bool
#check add Nat Nat          -- Type

protected def Foo.a : Nat := 1

open Foo

-- #check bar -- error
#check Foo.a
-- #check a

-- #check zero
#check Nat.zero
#check Nat.add

open Nat (succ zero gcd)
#check zero     -- Nat
#eval gcd 15 6  -- 3

#check Nat.add
#check add

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
