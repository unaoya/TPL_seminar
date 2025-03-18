/-
  Enumerated Types
-/

inductive Weekday where
  | sunday : Weekday
  | monday : Weekday
  | tuesday : Weekday
  | wednesday : Weekday
  | thursday : Weekday
  | friday : Weekday
  | saturday : Weekday
  deriving Repr

#check Weekday
#check Weekday.sunday
#check Weekday.monday


open Weekday

#check sunday
#check monday

example : sunday ≠ monday := noConfusion

#check Weekday.rec

def numberOfDay (d : Weekday) : Nat :=
  match d with
  | sunday    => 1
  | monday    => 2
  | tuesday   => 3
  | wednesday => 4
  | thursday  => 5
  | friday    => 6
  | saturday  => 7

#eval numberOfDay Weekday.sunday  -- 1
#eval numberOfDay Weekday.monday  -- 2
#eval numberOfDay tuesday         -- 3


set_option pp.all true    -- 詳細な情報を表示させるオプション
#print numberOfDay
-- 定義中に``numberOfDay.match_1``というものが現れている
#print numberOfDay.match_1
-- 定義中に``Weekday.casesOn``というものが現れている
#print Weekday.casesOn
-- 定義中に``Weekday.rec``というものが現れている
#check @Weekday.rec
/-
@Weekday.rec.{u}
 : {motive : Weekday → Sort u} →
    motive Weekday.sunday →
    motive Weekday.monday →
    motive Weekday.tuesday →
    motive Weekday.wednesday →
    motive Weekday.thursday →
    motive Weekday.friday →
    motive Weekday.saturday →
    (t : Weekday) → motive t
-/


#eval tuesday   -- Weekday.tuesday (``deriving Repr`` を外すとエラーになる)

namespace Weekday

def next (d : Weekday) : Weekday :=
  match d with
  | sunday    => monday
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday

#eval next monday

variable (x : Weekday)
#check x.next

def previous (d : Weekday) : Weekday :=
  match d with
  | sunday    => saturday
  | monday    => sunday
  | tuesday   => monday
  | wednesday => tuesday
  | thursday  => wednesday
  | friday    => thursday
  | saturday  => friday

#eval next (next tuesday)      -- Weekday.thursday
#eval next (previous tuesday)  -- Weekday.tuesday

example : next (previous tuesday) = tuesday :=
  rfl

theorem next_previous (d : Weekday) : next (previous d) = d :=
  match d with
  | sunday    => rfl
  | monday    => rfl
  | tuesday   => rfl
  | wednesday => rfl
  | thursday  => rfl
  | friday    => rfl
  | saturday  => rfl

def next_previous_ (d : Weekday) : next (previous d) = d := by
  cases d <;> rfl

end Weekday

#print Bool

namespace Hidden

inductive Bool where
  | t : Bool
  | f : Bool

def and (a b : Bool) : Bool :=
  match a with
  | Bool.t => b
  | Bool.f => Bool.f

def or (a b : Bool) : Bool :=
  match a with
  | Bool.t => Bool.t
  | Bool.f => b

def not (a : Bool) : Bool :=
  match a with
  | Bool.t => Bool.f
  | Bool.f => Bool.t

theorem deMorgan (a b : Bool) : not (and a b) = or (not a) (not b) := by
  cases a <;> cases b <;> rfl

end Hidden
