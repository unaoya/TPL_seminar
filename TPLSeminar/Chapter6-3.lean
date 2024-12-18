/-
  Attributes
-/

def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
  ∃ t, l₁ ++ t = l₂

-- @[simp] theorem List.isPrefix_self (as : List α) : isPrefix as as :=
--   ⟨[], by simp⟩

-- example : isPrefix [1, 2, 3] [1, 2, 3] := by
--   simp only [List.isPrefix_self]

-- theorem List.isPrefix_self (as : List α) : isPrefix as as :=
--   ⟨[], by simp⟩

-- attribute [simp] List.isPrefix_self

section

theorem List.isPrefix_self (as : List α) : isPrefix as as :=
  ⟨[], by simp⟩

attribute [local simp] List.isPrefix_self

example : isPrefix [1, 2, 3] [1, 2, 3] := by
  simp

end

-- example : isPrefix [1, 2, 3] [1, 2, 3] := by
--   simp


-- Error:
-- example : isPrefix [1, 2, 3] [1, 2, 3] := by
--  simp

-- instance : LE (List α) where
--   le := isPrefix

-- theorem List.isPrefix_self (as : List α) : as ≤ as :=
--   ⟨[], by simp⟩

def instLe : LE (List α) :=
  { le := isPrefix }

attribute [instance] instLe

section
attribute [local instance] instLe

example (as : List α) : as ≤ as :=
  ⟨[], by simp⟩

end

example (as : List α) : as ≤ as :=
  ⟨[], by simp⟩

-- Error:
-- example (as : List α) : as ≤ as :=
--  ⟨[], by simp⟩
