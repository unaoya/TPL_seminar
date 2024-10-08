
/-
  Namespaces
-/

def a : Nat := 3

namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
  def ffa : Nat := f (f a)

  #check a
  #eval a
  #check f
  #check fa
  #check ffa
  #check Foo.fa
end Foo

#check a  -- error
#eval a
#check f  -- error
#check Foo.a
#eval Foo.a
#check Foo.f
#check Foo.fa
#check Foo.ffa

open Foo

#check a
-- #eval a
#check f
-- #eval f a
#check fa
#check Foo.fa

#check List.nil
#check List.cons
#check List.map

open List

#check nil
#check cons
#check map


namespace Foo

  namespace Bar
    def fffa : Nat := f (f a)

    #check fa
    #check ffa
    #check fffa
  end Bar

  #check fa
  #check Bar.fffa
end Foo

#check Foo.fa
#check Foo.Bar.fffa

open Foo

#check fa
#check Bar.fffa

#check Foo.a
#check Foo.f

namespace Foo
  def ffa : Nat := f (f a)
end Foo

#check Foo.ffa

namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
end Foo

#check Foo.a
#check Foo.f

namespace Foo
  def ffa : Nat := f (f a)
end Foo
