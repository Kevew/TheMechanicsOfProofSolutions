import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

-- 3.2.2 Example
example : (-2 : ℤ) ∣ 6 := by {
  dsimp [(· ∣ ·)]
  use -3
  norm_num
}
