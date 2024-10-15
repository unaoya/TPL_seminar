/-
  Notation
-/

infixl:65   " + " => HAdd.hAdd  -- 左結合的な中置演算子
infix:50    " = " => Eq         -- 非結合的な中置演算子
infixr:80   " ^ " => HPow.hPow  -- 右結合的な中置演算子
prefix:100  "-"   => Neg.neg    -- 前置演算子
set_option quotPrecheck false
postfix:max "⁻¹"  => Inv.inv    -- 後置演算子

notation:65 lhs:65 " + " rhs:66 => HAdd.hAdd lhs rhs
notation:50 lhs:51 " = " rhs:51 => Eq lhs rhs
notation:80 lhs:81 " ^ " rhs:80 => HPow.hPow lhs rhs
notation:100 "-" arg:100 => Neg.neg arg
set_option quotPrecheck false
notation:1024 arg:1024 "⁻¹" => Inv.inv arg  -- ``max`` は優先度1024の略記

set_option quotPrecheck false
notation:65 lhs:65 " ~ " rhs:65 => wobble lhs rhs

set_option quotPrecheck false
notation:max "(" e ")" => e
notation:10 Γ " ⊢ " e " : " τ => Typing Γ e τ

notation:65 a " + " b:66 " + " c:66 => a + b - c
#eval 1 + 2 + 3  -- 0
