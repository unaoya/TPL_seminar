/-
  Entering Tactic Mode
-/

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  · exact hp
  . apply And.intro
    · exact hq
    · exact hp

theorem test₀ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  And.intro hp (And.intro hq hp)

theorem test₁ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  by apply And.intro
     exact hp
     apply And.intro
     exact hq
     exact hp

theorem test₂ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp

#print test
#print test₀

/-
theorem test : ∀ (p q : Prop), p → q → p ∧ q ∧ p :=
fun p q hp hq => { left := hp, right := { left := hq, right := hp } }
-/

theorem test₃ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp
  exact And.intro hq hp

theorem test₃' (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro _ (And.intro hq hp)
  exact hp

#print test₃

theorem test₄ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp; exact And.intro hq hp

theorem test₅ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case left => exact hp
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp

theorem test₆ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp
  case left => exact hp

theorem test₇ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  . exact hp
  . apply And.intro
    . exact hq
    . exact hp
