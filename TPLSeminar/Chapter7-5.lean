/-
  Other Recursive Data Types
-/

namespace Hidden
inductive List (α : Type u) where
  | nil  : List α
  | cons : α → List α → List α

namespace List

def append (as bs : List α) : List α :=
  match as with
  | nil       => bs
  | cons a as => cons a (append as bs)

theorem nil_append (as : List α) : append nil as = as :=
  rfl

theorem cons_append (a : α) (as bs : List α)
                    : append (cons a as) bs = cons a (append as bs) :=
  rfl

theorem append_nil (as : List α) : append as nil = as :=
  -- List.recOn as rfl
  --   (fun a as ih =>
  --     show append (cons a as) nil = cons a as from
  --     by rw [cons_append, ih])
  match as with
  | nil       => rfl
  | cons a as => by rw [cons_append, append_nil]

theorem append_assoc (as bs cs : List α)
        : append (append as bs) cs = append as (append bs cs) :=
  match as with
  | nil       => rfl
  | cons a as => by rw [cons_append]; rw [cons_append]; rw[cons_append]; rw [append_assoc]

end List
end Hidden

/- 1. ただ1つの頂点からなる有向グラフは全二分木である。
   2. 次数0の頂点vと2つの全二分木A,Bを用意し、
   ラベル付き有向辺(左,v,Aの根)と(右,v,Bの根)を追加し、vを根としたものは全二分木である。
   3. 以上の手続きで全二分木だとわかるものだけが全二分木である。 -/
inductive BinaryTree where
  | leaf : BinaryTree
  | root (left : BinaryTree) (right : BinaryTree) : BinaryTree


/- 1. ただ1つの頂点からなる有向グラフは全可算無限分木である。
   2. 次数0の頂点vと2つの全可算無限分木T_0,T_1,...を用意し、
   ラベル付き有向辺(0,v,T_0の根),(1,v,T_1の根),...を追加し、vを根としたものは全可算無限分木である。
   3. 以上の手続きで全可算無限分木だとわかるものだけが全可算無限分木である。 -/
inductive CBTree where
  | leaf : CBTree
  | sup : (Nat → CBTree) → CBTree

namespace CBTree

def succ (t : CBTree) : CBTree :=
  sup (fun _ => t)

def toCBTree : Nat → CBTree
  | 0 => leaf
  | n+1 => succ (toCBTree n)

def omega : CBTree :=
  sup toCBTree

end CBTree
