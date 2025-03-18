/-
	Scoped Instances
-/
structure Point where
  x : Nat
  y : Nat

namespace Point

scoped instance : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double (p : Point) :=
  p + p

end Point
-- インスタンス `Add Point` はもう使えない

-- #check fun (p : Point) => p + p + p  -- Error

namespace Point
-- インスタンス `Add Point` は再び利用可能になった
#check fun (p : Point) => p + p + p

end Point

open Point -- 名前空間を開き、インスタンス `Add Point` を利用可能にする
#check fun (p : Point) => p + p + p

namespace Point

scoped instance : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

end Point

open scoped Point -- インスタンス `Add Point` を利用可能にする
#check fun (p : Point) => p + p + p

-- #check fun (p : Point) => double p -- Error: unknown identifier 'double'
