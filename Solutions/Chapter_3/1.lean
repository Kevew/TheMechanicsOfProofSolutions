import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

-- 3.1.2 Example
example : Odd (-3 : ℤ) := by {
  dsimp [Odd]
  use -2
  norm_num
}
