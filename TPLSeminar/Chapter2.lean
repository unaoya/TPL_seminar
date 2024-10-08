/-
  Simple Type Theory
-/

-- def <項の名前(識別子)> : <項の型> := <項の定義式>
def m : Nat := 1           -- `m` は自然数型を持つ
def b1 : Bool := true      -- `b1` はブール型を持つ
def b2 : Bool := false

-- #check <項>
#check m                   -- output: Nat
#check b1 && b2            -- `&&` は「かつ」 output: Bool
#check b1 || b2            -- `||` は「または」 output: Bool

-- #eval <項>
#eval 5 * 4                -- 20
#eval m + 2                -- 3
#eval b1 && b2             -- false

#check Nat → Nat                   -- `→` は "\to" あるいは "\r" と打つと入力できる
#check Nat -> Nat                  -- `->` は `→` のASCII表記

#check Nat × Nat                   -- `×` は "\times" と打つと入力できる
#check Prod Nat Nat                -- `Prod Nat Nat` は `Nat × Nat` のASCII表記

#check Nat → Nat → Nat
#check Nat → (Nat → Nat)           -- これは1つ上と同じである。つまり、`→` は右結合的である
#check Nat × Nat → Nat
#check (Nat → Nat) → Nat           -- 関数を受け取る関数の型

#check Nat.succ                    -- Nat → Nat
#check (0, 1)                      -- Nat × Nat
#check Nat.add                     -- Nat → Nat → Nat

#check Nat.succ 2                  -- Nat
#check Nat.add 3                   -- Nat → Nat
#check Nat.add 5 2                 -- Nat
#check (5, 9).1                    -- Nat
#check (5, 9).2                    -- Nat

#eval Nat.succ 2                   -- 3
#eval Nat.add 5 2                  -- 7
#eval (5, 9).1                     -- 5
#eval (5, 9).2                     -- 9
#eval Nat.add (10, 7).1 (10, 7).2  -- 17


/-
  Types as objects
-/

#check Nat               -- Type
#check Bool              -- Type
#check Nat → Bool        -- Type
#check Nat × Bool        -- Type
#check Nat → Nat         -- ...
#check Nat × Nat → Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check Nat → Nat → Bool
#check (Nat → Nat) → Nat

def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List
def G : Type → Type → Type := Prod

#check α        -- Type
#check F α      -- Type
#check F Nat    -- Type
#check G α      -- Type → Type
#check G α β    -- Type
#check G α Nat  -- Type

#check Prod α β       -- Type
#check α × β          -- Type

#check Prod Nat Nat   -- Type
#check Nat × Nat      -- Type

#check List α    -- Type
#check List Nat  -- Type

#check Type      -- Type 1

#check Type 1
#check Type 2
#check Type 3
#check Type 4

#check Type
#check Type 0

#check Prop
#check Sort
#check Sort 0

#check Sort 1
#check Sort 2
#check Sort 3
#check Sort 4


#check List    -- List.{u} (α : Type u) : Type u

#check Prod    -- Prod.{u, v} (α : Type u) (β : Type v) : Type (max u v)

universe u
def F' (α : Type u) : Type u := Prod α α       -- `Type u` に属する型 `α` を受け取ると、`α` と `α` の直積型を返す関数
#check F'                                      -- Type u → Type u

def F''.{v} (α : Type v) : Type v := Prod α α

#check F''    -- Type u → Type u

-- universe の指定について

#check Nat

def H₀ (α : Type) : Type := α
def H₁ (α : Type 1) : Type 1 := α
def H₂.{v} (α : Type v) : Type v := α

#check H₀ Nat
-- #check H₁ Nat
#check H₁ Type
#check H₂ Nat
#check H₂ Type
#check H₂ (Type 1)

/-
  Function Abstraction and Evaluation
-/


-- 括弧は省略可能
-- fun (<入力引数の名前> : <入力引数の型名>) => <関数の出力を定義する式>
-- λ (<入力引数の名前> : <入力引数の型名>) => <関数の出力を定義する式>
#check fun (x : Nat) => x + 5   -- Nat → Nat
#check λ (x : Nat) => x + 5     -- `λ` と `fun` は同じ意味
#check fun x => x + 5           -- `x` は `Nat` 型だと推論される
#check λ x => x + 5             -- `x` は `Nat` 型だと推論される


#eval (λ x : Nat => x + 5) 10    -- 15

#check fun x : Nat => fun y : Bool => if not y then x + 1 else x + 2
#check fun (x : Nat) (y : Bool) => if not y then x + 1 else x + 2
#check fun x y => if not y then x + 1 else x + 2   -- Nat → Bool → Nat

def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#check fun x : Nat => x        -- Nat → Nat
#check fun x : Nat => true     -- Nat → Bool
#check fun x : Nat => g (f x)  -- Nat → Bool
#check fun x => g (f x)        -- Nat → Bool


#check fun (g : String → Bool) (f : Nat → String) (x : Nat) => g (f x)
-- (String → Bool) → (Nat → String) → Nat → Bool

#check fun (α β γ : Type) (g : β → γ) (f : α → β) (x : α) => g (f x)

-- α同値について

example (α : Type) : (fun (x : α) => x) = fun (y : α) => y := rfl

#check (fun x : Nat => x) 1     -- Nat
#check (fun x : Nat => true) 1  -- Bool

def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#check
  (fun (α β γ : Type) (u : β → γ) (v : α → β) (x : α) => u (v x)) Nat String Bool g f 0
  -- Bool

def f (n : Nat) : String := toString n
def g (s : String) : Bool := s.length > 0

#eval (fun x : Nat => x) 1     -- 1
#eval (fun x : Nat => true) 1  -- true
#eval (fun (α β γ : Type) (u : β → γ) (v : α → β) (x : α) => u (v x)) Nat String Bool g f 0  -- true

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

#eval compose Nat Nat Nat double square 3        -- 18
#eval compose Nat Nat Nat square double 3        -- 36

/-
  Local Definitions
-/

#check let y := 2 + 2; y * y   -- Nat
#eval  let y := 2 + 2; y * y   -- 16

def double_square (x : Nat) : Nat :=
  let y := x + x; y * y

#eval double_square 2   -- 16

#check let y := 2 + 2; let z := y + y; z * z   -- Nat
#eval  let y := 2 + 2; let z := y + y; z * z   -- 64

def double_square' (x : Nat) : Nat :=
  let y := x + x
  y * y

def foo := let a := Nat; fun x : a => x + 2

-- def bar := (fun a => fun x : a => x + 2) Nat

/-
  Varibles and Sections
-/

def doThrice (α : Type) (h : α → α) (x : α) : α :=
  h (h (h x))

#print compose
#print doTwice
#print doThrice

variable (α β γ : Type)

def compose' (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice' (h : α → α) (x : α) : α :=
  h (h x)

def doThrice' (h : α → α) (x : α) : α :=
  h (h (h x))

#print compose'
#print doTwice'
#print doThrice'

variable (α β γ : Type)
variable (g : β → γ) (f : α → β) (h : α → α)
variable (x : α)

def compose'' := g (f x)
def doTwice'' := h (h x)
def doThrice'' := h (h (h x))

#print compose''
#print doTwice''
#print doThrice''

section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  #check α              -- セクション内で変数 `α` は参照可能。

  def compose''' := g (f x)
  def doTwice''' := h (h x)
  def doThrice''' := h (h (h x))
end useful

#check compose          -- セクション内で定義された関数はセクション外でも参照可能。
-- #check α             -- エラー。セクション外で変数 `α` は参照不可能。

/-
  Namespaces
-/

namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
  def ffa : Nat := f (f a)

  #check a
  #check f
  #check fa
  #check ffa
  #check Foo.fa
end Foo

-- #check a  -- error
-- #check f  -- error
#check Foo.a
#check Foo.f
#check Foo.fa
#check Foo.ffa

open Foo

#check a
#check f
#check fa
#check Foo.fa

end Foo

#check List.nil
#check List.cons
#check List.map

open List

#check nil
#check cons
#check map

end List

namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a

  namespace Bar
    def ffa : Nat := f (f a)

    #check fa
    #check ffa
  end Bar

  #check fa
  #check Bar.ffa
end Foo

#check Foo.fa
#check Foo.Bar.ffa

open Foo

#check fa
#check Bar.ffa

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

/-
  What makes dependent type theory dependent?
-/

def cons (α : Type) (a : α) (as : List α) : List α :=
  List.cons a as

#check cons Nat        -- Nat → List Nat → List Nat
#check cons Bool       -- Bool → List Bool → List Bool
#check cons            -- (α : Type) → α → List α → List α

#check @List.cons    -- {α : Type u_1} → α → List α → List α
#check @List.nil     -- {α : Type u_1} → List α
#check @List.length  -- {α : Type u_1} → List α → Nat
#check @List.append  -- {α : Type u_1} → List α → List α → List α

universe u v

def f (α : Type u) (β : α → Type v) (a : α) (b : β a) : (a : α) × β a :=
  ⟨a, b⟩

def g (α : Type u) (β : α → Type v) (a : α) (b : β a) : Σ a : α, β a :=
  Sigma.mk a b

#print f
#print g

def h1 (x : Nat) : Nat :=
  (f Type (fun α => α) Nat x).2

#eval h1 5 -- 5

def h2 (x : Nat) : Nat :=
  (g Type (fun α => α) Nat x).2

#eval h2 5 -- 5

def i : Type :=                 -- iは ``Nat`` 型のこと
  (f Type (fun α => α) Nat 5).1

def test : i := 5 + 5

#eval test -- 10

/-
  Implicit Arguments
-/

universe u
def Lst (α : Type u) : Type u := List α
def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil (α : Type u) : Lst α := List.nil
def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs
#check Lst          -- Lst.{u} (α : Type u) : Type u
#check Lst.cons     -- Lst.cons.{u} (α : Type u) (a : α) (as : Lst α) : Lst α
#check Lst.nil      -- Lst.nil.{u} (α : Type u) : Lst α
#check Lst.append   -- Lst.append.{u} (α : Type u) (as bs : Lst α) : Lst α

#check Lst.cons Nat 0 (Lst.nil Nat)      -- Lst Nat
#eval Lst.cons Nat 0 (Lst.nil Nat)       -- [0]

def as : Lst Nat := Lst.nil Nat
def bs : Lst Nat := Lst.cons Nat 5 (Lst.nil Nat)

#check Lst.append Nat as bs              -- Lst Nat
#eval Lst.append Nat as bs               -- [5]

universe u
def Lst (α : Type u) : Type u := List α
def Lst.cons (α : Type u) (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil (α : Type u) : Lst α := List.nil
def Lst.append (α : Type u) (as bs : Lst α) : Lst α := List.append as bs
#check Lst          -- Type u_1 → Type u_1
#check Lst.cons     -- (α : Type u_1) → α → Lst α → Lst α
#check Lst.nil      -- (α : Type u_1) → Lst α
#check Lst.append   -- (α : Type u_1) → Lst α → Lst α → Lst α
#check Lst.cons _ 0 (Lst.nil _)      -- Lst Nat

def as : Lst Nat := Lst.nil _
def bs : Lst Nat := Lst.cons _ 5 (Lst.nil _)

#check Lst.append _ as bs            -- Lst Nat

universe u
def Lst (α : Type u) : Type u := List α

def Lst.cons {α : Type u} (a : α) (as : Lst α) : Lst α := List.cons a as
def Lst.nil {α : Type u} : Lst α := List.nil
def Lst.append {α : Type u} (as bs : Lst α) : Lst α := List.append as bs

#check Lst.cons 0 Lst.nil      -- Lst Nat

def as : Lst Nat := Lst.nil
def bs : Lst Nat := Lst.cons 5 Lst.nil

#check Lst.append as bs        -- Lst Nat

universe u
def ident {α : Type u} (x : α) := x

#check ident         -- ?m → ?m
#check ident 1       -- Nat
#check ident "hello" -- String
#check @ident        -- {α : Type u_1} → α → α

universe u

section
  variable {α : Type u}
  variable (x : α)
  def ident := x
end

#check ident           -- {α : Type u_1} → α → α
#check ident 4         -- Nat
#check ident "hello"   -- String

#check List.nil               -- List ?m
#check id                     -- ?m → ?m

#check (List.nil : List Nat)  -- List Nat
#check (id : Nat → Nat)       -- Nat → Nat

#check 2            -- Nat
#check (2 : Nat)    -- Nat
#check (2 : Int)    -- Int


#check @id        -- {α : Sort u_1} → α → α
#check @id Nat    -- Nat → Nat
#check @id Bool   -- Bool → Bool

#check @id Nat 1     -- Nat
#check @id Bool true -- Bool
