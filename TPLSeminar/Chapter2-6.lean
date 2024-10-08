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
