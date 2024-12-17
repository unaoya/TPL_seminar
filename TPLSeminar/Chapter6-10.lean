/-
  Auto Bound Implicit Arguments
-/

-- universe u v w
-- def compose {α : Type u} {β : Type v} {γ : Type w}
--             (g : β → γ) (f : α → β) (x : α) : γ :=
--   g (f x)

-- def compose.{u, v, w}
--             {α : Type u} {β : Type v} {γ : Type w}
--             (g : β → γ) (f : α → β) (x : α) : γ :=
--   g (f x)

def compose (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

#check @compose
-- {β : Sort u_1} → {γ : Sort u_2} → {α : Sort u_3} → (β → γ) → (α → β) → α → γ

-- def compose (g : β → γ) (f : α → β) (x : α) : γ :=
--   g (f x)

-- #check @compose
-- -- {β : Sort u_1} → {γ : Sort u_2} → {α : Sort u_3} → (β → γ) → (α → β) → α → γ
