import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

-- 2.4.2 Example
example {p : ℚ} (hp : p ^ 2 ≤ 8) : p ≥ -5 := by{
  have hp2 : p ^ 2 ≤ 3 ^ 2 := by linarith
  have hp3 : (0:ℚ) ≤ 3:= by norm_num
  have hp' : -3 ≤ p ∧ p ≤ 3 := by apply abs_le_of_sq_le_sq' hp2 hp3
  calc p
  _ ≥ -3 := by rel [hp'.left]
  _ ≥ -5 := by norm_num
}

-- 2.4.4 Example
example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a = 0 ∧ b = 0 := by{
  have h2 : a ^ 2 = 0 := by {
    apply le_antisymm
    have h2 : b ^ 2 ≥ 0 := by exact sq_nonneg b
    calc
      a ^ 2 ≤ a ^ 2 + b ^ 2 := by linarith
      _ = 0 := by rw [h1]
    exact sq_nonneg a
  }
  have h3 : b ^ 2 = 0 := by{
    calc  b ^ 2
    _ = 0 + b ^ 2:= by ring
    _ = a ^ 2 + b ^ 2 := by rw [h2]
    _ = 0 := by rw [h1]
  }
  have h4 : a = 0 := by exact pow_eq_zero h2
  have h5 : b = 0 := by exact pow_eq_zero h3
  constructor
  exact h4
  exact h5
}

-- 2.4.5.1 Example
example {a b : ℚ} (H : a ≤ 1 ∧ a + b ≤ 3) : 2 * a + b ≤ 4 := by {
  calc 2 * a + b
  = a + (a + b) := by ring
  _ ≤ 1 + 3 := by rel [H.left, H.right]
  _ = 4 := by norm_num
}

-- 2.4.5.2 Example
example {r s : ℝ} (H : r + s ≤ 1 ∧ r - s ≤ 5) : 2 * r ≤ 6 := by {
  calc 2 * r
  _ = r + s + (r - s) := by ring
  _ ≤ 1 + 5 := by rel [H.left, H.right]
  _ = 6 := by ring
}

-- 2.4.5.3 Example
example {m n : ℤ} (H : n ≤ 8 ∧ m + 5 ≤ n) : m ≤ 3 := by {
  calc m
  _ = m + 5 - 5 := by ring
  _ ≤ n - 5 := by rel [H.right]
  _ ≤ 8 - 5 := by rel[H.left]
  _ = 3 := by norm_num
}

-- 2.4.5.4 Example
example {p : ℤ} (hp : p + 2 ≥ 9) : p ^ 2 ≥ 49 ∧ 7 ≤ p := by {
  have h1 : p ≥ 7 := by linarith [hp]
  have h2 : p ^ 2 ≥ 49 := by {
    calc p ^ 2
      ≥ 7 ^ 2 := by rel [h1]
      _ = 49 := by norm_num
  }
  exact ⟨h2, h1⟩
}

-- 2.4.5.5 Example
example {a : ℚ} (h : a - 1 ≥ 5) : a ≥ 6 ∧ 3 * a ≥ 10 := by {
  have h1 : a ≥ 6 := by linarith
  have h2 : 3 * a ≥ 10 := by {
    calc 3 * a
    _ ≥ 3 * 6 := by rel [h1]
    _ ≥ 10 := by norm_num
  }
  exact ⟨h1, h2⟩
  -- Following works as well for exact
  -- constructor
  -- exact h1
  -- exact h2
}

-- 2.4.5.6 Example
example {x y : ℚ} (h : x + y = 5 ∧ x + 2 * y = 7) : x = 3 ∧ y = 2 := by {
  have h1 : y = 5 - x := by linarith [h.left]
  have h2 : x = 3 := by {
    -- linarith works fine here but ill show some insight
    have h3 : x + 2 * y = - x + 10 := by linarith [h1]
    rcases h with ⟨h4, h5⟩
    rw [h3] at h5
    linarith [h5]
  }
  have h3 : y = 2 := by linarith [h1, h2]
  exact ⟨h2, h3⟩
}

-- 2.4.5.7 Example
example {a b : ℝ} (h1 : a * b = a) (h2 : a * b = b) :
    a = 0 ∧ b = 0 ∨ a = 1 ∧ b = 1 := by {
  have h3 : a = b := by {
      calc a
        = a * b := h1.symm
        _ = b := h2
  }
  have h4 : a * a = a := by{
    calc a * a
    _ = a * b := by rw [h3]
    _ = a := by rw [h1]
  }
  have h5 : a * (a - 1) = 0 := by linarith [h4]
  have h6 : a = 0 ∨ a - 1 = 0 := by
    apply eq_zero_or_eq_zero_of_mul_eq_zero h5
  cases h6 with
  | inl h7 =>
    have h8 : b = 0 := by linarith
    exact Or.inl ⟨h7, h8⟩
  | inr h7 =>
    have h8 : b = 1 := by linarith
    have h9 : a = 1 := by linarith
    exact Or.inr ⟨h9, h8⟩
}
