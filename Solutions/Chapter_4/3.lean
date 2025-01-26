import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Int.ModEq

-- 4.3.2 Example
example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by {
  use 2
  dsimp
  constructor
  · intro a ha ha2
    have h1: -1 ≤ a - 2 := by linarith
    have h2: a - 2 ≤ 1 := by linarith
    have h3: a - 2 ≤ 1 ∧ -1 ≤ a - 2 := by exact ⟨h2, h1⟩
    have h4: (a - 2) ^ 2 ≤ 1 ^ 2 := by exact sq_le_sq' h1 h2
    exact h4
  intro y h
  have h1 := h 1 (by norm_num) (by norm_num)
  have h2 := h 3 (by norm_num) (by norm_num)
  have h3: (y - 2) ^ 2 ≤ 0 := by {
    calc (y - 2) ^ 2
    _ = ((1 - y)^2 + (3 - y) ^ 2 - 2)/2 := by ring
    _ ≤ (1 + 1 - 2)/2 := by rel [h1, h2]
    _ = 0 := by norm_num
  }
  have h4: (y - 2) ^ 2 ≥ 0 := by exact sq_nonneg (y - 2)
  have h5: (y - 2) ^ 2 = 0 := by linarith
  linarith
}

-- 4.3.5.1 Example
example : ∃! x : ℚ, 4 * x - 3 = 9 := by {
  use 3
  constructor
  dsimp
  norm_num
  intro y hy
  linarith
}

-- 4.3.5.2 Example
example : ∃! n : ℕ, ∀ a, n ≤ a := by {
  use 0
  constructor
  · intro a
    linarith
  intro y hy
  exact Nat.eq_zero_of_le_zero (hy 0)
}

-- 4.3.5.3 Example
example : ∃! r : ℤ, 0 ≤ r ∧ r < 3 ∧ 11 ≡ r [ZMOD 3] := by {
  use 2
  dsimp
  constructor
  constructor
  norm_num
  constructor
  norm_num
  dsimp [Int.ModEq]
  intro y hy
  have h1 : 11 % 3 = 2 := by norm_num
  have h2 : y % 3 = 2 := by
    rw [Int.ModEq] at hy
    omega
  omega
}
