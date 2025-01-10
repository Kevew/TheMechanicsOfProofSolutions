import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

-- 2.2.2 Example
example {y : ℝ} : y ^ 2 + 1 ≠ 0 := by {
    apply ne_of_gt
    have h1 : y^2 ≥ 0 := by exact sq_nonneg y
    calc 0
    _ ≤ y ^2 := by rel [h1]
    _ < y ^ 2 + 1 := by linarith
}


-- 2.2.3 Example
example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a ^ 2 = 0 := by{
  apply le_antisymm
  have h2: b^2 ≥ 0 := by exact sq_nonneg b
  calc
    a ^ 2 ≤ a ^ 2 + b ^ 2 := by linarith
    _ = 0 := by rel [h1]
  exact sq_nonneg a
}

-- 2.2.4.1 Example
example {m : ℤ} (hm : m + 1 = 5) : 3 * m ≠ 6 := by{
    apply ne_of_gt
    have h1: m = 4 := by linarith
    rw [h1]
    norm_num
}

-- 2.2.4.2 Example
example {s : ℚ} (h1 : 3 * s ≤ -6) (h2 : 2 * s ≥ -4) : s = -2 := by {
    apply le_antisymm
    · linarith -- It just rewrites h1 to apply it to the goal
    · linarith
}
