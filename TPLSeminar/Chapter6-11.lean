/-
  Implicit Lambdas
-/

-- variable (ρ : Type) (m : Type → Type) [Monad m]

-- instance : Monad (ReaderT ρ m) where
--   pure := ReaderT.pure
--   bind := ReaderT.bind

namespace ex2

def id1 : {α : Type} → α → α :=
  fun x => x

def listId : List ({α : Type} → α → α) :=
  (fun x => x) :: []

-- 次の例において、``fun`` の前に ``@`` があるときは
-- 暗黙ラムダ式導入機能は無効になっている
def id2 : {α : Type} → α → α :=
  @fun α (x : α) => id1 x

#check id2

def id2' : {α : Type} → α → α :=
  fun x => id1 x

#check id2'

def id3 : {α : Type} → α → α :=
  @fun _ x => id1 x

def id4 : {α : Type} → α → α :=
  fun x => id1 x

-- 次の例では、束縛記法 ``{...}`` を使っているため、
-- 暗黙ラムダ式導入機能は無効になっている
def id5 : {α : Type} → α → α :=
  fun {α} (x : α) => id1 x

end ex2
