/-
  Extensible Tactics
-/

-- 新しい記法を定義する
syntax "triv" : tactic

macro_rules
  | `(tactic| triv) => `(tactic| assumption)

example (h : p) : p := by
  triv

-- 現時点では、`triv` を使って次の定理を証明することはできない
-- example (x : α) : x = x := by
--  triv

-- `triv` を拡張しよう。タクティク解釈器はどれかが成功するまで
-- `triv` のための全てのマクロ展開を試す
macro_rules
  | `(tactic| triv) => `(tactic| rfl)

example (x : α) : x = x := by
  triv

example (x : α) (h : p) : x = x ∧ p := by
  apply And.intro <;> triv

-- (再帰的な)マクロ展開を追加する
macro_rules | `(tactic| triv) => `(tactic| apply And.intro <;> triv)

example (x : α) (h : p) : x = x ∧ p := by
  triv
