/-
	Local Instances
-/

namespace Ex3

structure Point where
  x : Nat
  y : Nat

section

local instance addPoint : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double (p : Point) :=
  Add.add p p

end -- もうインスタンス `Add Point` は使えない

-- def double' (p : Point) :=
--   Add.add p p  -- Error: failed to synthesize instance

-- def triple (p : Point) :=
--  p + p + p  -- Error: failed to synthesize instance

-- 2/25ここまで
