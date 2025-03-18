/-
  Defining the Natural Numbers
-/

namespace Hidden
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
  deriving Repr

#check @Nat.rec

--   {motive : Nat → Sort u}
--   → motive Nat.zero
--   → ((n : Nat) → motive n → motive (Nat.succ n))
--   → (t : Nat) → motive t

--   α
--   → (Nat → α → α)
--   → (t : Nat) → α

-- motiveは定義したい関数の行き先の型を指定する
-- 依存型関数も定義できるように、motiveはNatで添字づけられた型の族である。
-- これが定数 α なら Nat → α を定義することになる。
-- 一番最後の (t : Nat) → motive t が実際に定義された依存型関数
-- Natのinductive typeとしての定義から、
-- zeroの行き先をmotive Nat.zero型の項として定義し
-- nの行き先がmotive n型の項と指定されているならばmotive n.succ型の項が指定され、それがn.succの行き先。

-- @Nat.recOn :
--   {motive : Nat → Sort u}
--   → (t : Nat)
--   → motive Nat.zero
--   → ((n : Nat) → motive n → motive (Nat.succ n))
--   → motive t

-- inductive Nat where
--   | zero : Nat
--   | succ : Nat → Nat
--   deriving Repr

inductive Test where
  | a : Test
  | b : Test

#check @Test.rec

-- {motive : Test → Sort u_1} →
--   motive Test.a →
--     motive Test.b →
--       (t : Test) → motive t

-- Testを定義域とする関数を定義したいとする。
-- まず行き先の型を決める。
-- これは依存型もありなので、Test → Sort u という型の族を指定することになる。
-- この項を motive とする。
-- このうえで、a の行き先と b の行き先を motive a 型の項と motive b 型の項として指定する。
-- これで、(x : Test) → motive x という型を持つ関数が定義される。

inductive Sum (α β : Type) where
  | inl : α → Sum α β
  | inr : β → Sum α β

#check @Sum.rec
-- {α β : Type} →
--   {motive : Sum α β → Sort u_1} →
--     ((a : α) → motive (Sum.inl a)) →
--       ((a : β) → motive (Sum.inr a)) →
--         (t : Sum α β) → motive t

-- motiveが定数な場合（つまり依存型でない普通の関数）の場合を考えるとわかりやすいかも


namespace Nat

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)

#eval add (succ (succ zero)) (succ zero)

instance : Add Nat where
  add := add

theorem add_zero (m : Nat) : m + zero = m := rfl
-- theorem zero_add (m : Nat) : zero + m = m := rfl

end Nat
end Hidden

open Nat

@[simp]
theorem add_succ (m n : Nat) : m + succ n = succ (m + n) := rfl


-- @Nat.recOn :
--   {motive : Nat → Sort u}
--   → (t : Nat)
--   → motive Nat.zero
--   → ((n : Nat) → motive n → motive (Nat.succ n))
--   → motive t

theorem zero_add (n : Nat) : 0 + n = n :=
  Nat.recOn
    (motive := fun x => 0 + x = x)
    n
    (show 0 + 0 = 0 from rfl)
    (fun (n : Nat) (ih : 0 + n = n) =>
      show 0 + succ n = succ n from
      calc 0 + succ n
        _ = succ (0 + n) := rfl
        _ = succ n       := by rw [ih])

example (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := fun x => 0 + x = x) n
    rfl
    (fun n ih => by simp [_root_.add_succ, ih])

example (n : Nat) : 0 + n = n :=
  Nat.recOn (motive := fun x => 0 + x = x) n
    rfl
    (fun n ih => by simp [Nat.add_succ, ih])

theorem add_assoc (m n k : Nat) : m + n + k = m + (n + k) :=
  Nat.recOn (motive := fun k => m + n + k = m + (n + k)) k
    (show m + n + 0 = m + (n + 0) from rfl)
    (fun k (ih : m + n + k = m + (n + k)) =>
      show m + n + succ k = m + (n + succ k) from
      calc m + n + succ k
        _ = succ (m + n + k)   := rfl
        _ = succ (m + (n + k)) := by rw [ih]
        _ = m + succ (n + k)   := rfl
        _ = m + (n + succ k)   := rfl)

theorem add_comm (m n : Nat) : m + n = n + m :=
  Nat.recOn (motive := fun x => m + x = x + m) n
   (show m + 0 = 0 + m by rw [Nat.zero_add, Nat.add_zero])
   (fun (n : Nat) (ih : m + n = n + m) =>
    show m + succ n = succ n + m from
    calc m + succ n
      _ = succ (m + n) := rfl
      _ = succ (n + m) := by rw [ih]
      _ = succ n + m   := sorry)

theorem succ_add (n m : Nat) : succ n + m = succ (n + m) :=
  Nat.recOn (motive := fun x => succ n + x = succ (n + x)) m
    (show succ n + 0 = succ (n + 0) from rfl)
    (fun (m : Nat) (ih : succ n + m = succ (n + m)) =>
     show succ n + succ m = succ (n + succ m) from
     calc succ n + succ m
       _ = succ (succ n + m)   := rfl
       _ = succ (succ (n + m)) := by rw [ih]
       _ = succ (n + succ m)   := rfl)

-- theorem succ_add (n m : Nat) : succ n + m = succ (n + m) :=
--   Nat.recOn (motive := fun x => succ n + x = succ (n + x)) m
--     rfl
--     (fun m ih => by simp only [add_succ, ih])

-- theorem add_comm (m n : Nat) : m + n = n + m :=
--   Nat.recOn (motive := fun x => m + x = x + m) n
--     (by simp)
--     (fun m ih => by simp [add_succ, succ_add, ih])

namespace Hidden

inductive Eq : α → α → Prop where
  /-- `Eq.refl a : a = a` is reflexivity, the unique constructor of the
  equality type. See also `rfl`, which is usually used instead. -/
  | refl (a : α) : Eq a a

set_option pp.all true
#check @Eq.rec
-- {α : Sort u_2} →
--   {a : α} →
--     {motive : (a_1 : α) → @Hidden.Eq.{u_2} α a a_1 → Sort u_1} →
--       motive a (@Hidden.Eq.refl.{u_2} α a) →
--         {a_1 : α} →
--           (t : @Hidden.Eq.{u_2} α a a_1) →
--             motive a_1 t

variable (α : Type) (a : α)
#check @Eq.rec α
#check @Eq.rec α a

example (α : Type) (a b : α) (h : Eq a b) : Eq b a :=
  match h with
  | Eq.refl a => Eq.refl a

example (α : Type) (a b : α) (h : Eq a b) : Eq b a :=
  let motive : (x : α) → Eq a x → Prop := fun x _ => Eq x a
  @Eq.rec α a motive (Eq.refl a) b h
