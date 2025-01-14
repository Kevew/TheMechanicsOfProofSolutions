import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

example : (11 : ℕ) ∣ 88 := by
  dsimp [(· ∣ ·)]
  use 8
