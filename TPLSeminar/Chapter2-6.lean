/-
  Varibles and Sections
-/

def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def doTwice (α : Type) (h : α → α) (x : α) : α :=
  h (h x)

def doThrice (α : Type) (h : α → α) (x : α) : α :=
  h (h (h x))

#print compose
#print doTwice
#print doThrice

def f (x : α) : α := x

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
  variable (α₀ β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  #check α₀              -- セクション内で変数 `α` は参照可能。

  def compose''' := g (f x)
  def doTwice''' := h (h x)
  def doThrice''' := h (h (h x))
end useful

#check compose'''          -- セクション内で定義された関数はセクション外でも参照可能。
#check α₀             -- エラー。セクション外で変数 `α` は参照不可能。
