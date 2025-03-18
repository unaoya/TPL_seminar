/-
	Exercises
-/
inductive Expr where
  | const : Nat → Expr
  | var : Nat → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr
  deriving Repr

open Expr

def sampleExpr : Expr :=
  plus (times (var 0) (const 7)) (times (const 2) (var 1))
  -- 7x₀ + 2x₁

def eval (v : Nat → Nat) : Expr → Nat
  | const n     => n
  | var n       => v n
  | plus e₁ e₂  => eval v e₁ + eval v e₂
  | times e₁ e₂ => eval v e₁ * eval v e₂

def sampleVal : Nat → Nat
  | 0 => 5
  | 1 => 6
  | _ => 0

-- 次のコマンドを実行せよ。`47` が出力されたら正解である。
#eval eval sampleVal sampleExpr

def simpConst : Expr → Expr
  | plus (const n₁) (const n₂)  => const (n₁ + n₂)
  | times (const n₁) (const n₂) => const (n₁ * n₂)
  | e                           => e

def fuse : Expr → Expr
  | const n    => const n
  | var n      => var n
  | plus (const n) (const m) => const (n + m)
  | plus e₁ e₂ => simpConst (Expr.plus (fuse e₁) (fuse e₂))
  | times (const n) (const m) => const (n * m)
  | times e₁ e₂ => simpConst (times (fuse e₁) (fuse e₂))

def sampleExpr' : Expr :=
  plus (times (plus (const 2) (const 1)) (const 7)) (times (const 2) (const 1))
  -- ((2 + 1) * 7) + (2 * 1)

#eval sampleExpr'
#eval fuse sampleExpr' -- Expr.const 9

example : simpConst (plus (var 2) (var 3)) = plus (var 2) (var 3) := rfl

theorem simpConst_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (simpConst e) = eval v e
  | const n     => rfl
  | var n       => rfl
  | plus e₁ e₂  =>
    match e₁, e₂ with
    | const n₁, const n₂ => rfl
    | const n₁, var n₂ => rfl
    | const n₁, plus e₁₁ e₁₂ => rfl
    | const n₁, times e₁₁ e₁₂ => rfl
    | var n₁, _ => rfl
    | plus e₁₁ e₁₂, _ => rfl
    | times e₁₁ e₁₂, _ => rfl
  | times e₁ e₂ =>
    match e₁, e₂ with
    | const n₁, const n₂ => rfl
    | const n₁, var n₂ => rfl
    | const n₁, plus e₁₁ e₁₂ => rfl
    | const n₁, times e₁₁ e₁₂ => rfl
    | var n₁, _ => rfl
    | plus e₁₁ e₁₂, _ => rfl
    | times e₁₁ e₁₂, _ => rfl

theorem fuse_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (fuse e) = eval v e
  | const n     => rfl
  | var n       => rfl
  | plus (const n₁) (const n₂) => rfl
  | plus (plus e₁ e₂) (plus e₃ e₄) => by
    rw [fuse]
    have := simpConst_eq v ((fuse (e₁.plus e₂)).plus (fuse (e₃.plus e₄)))
    rw [this]
    have (e e' : Expr) : eval v ((fuse e).plus (fuse e')) = eval v (e.plus e') := sorry
    rw [this]
