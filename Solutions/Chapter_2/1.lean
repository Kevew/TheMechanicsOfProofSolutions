import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

-- 2.1.3 Example
example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 := by{
  -- It says use one tactic but I think this looks better
  -- You can see how I manipulated h1 to become it
  have h3 : r ≤ s + 3 := by {
    rw [ge_iff_le] at h1
    exact h1
  }
  -- If you're curious, the textbook way would be `addarith [h2]`
  -- I'm gonna stick to linarith since it's part of Mathlib
  have h4 : r ≤ 3 - s := by linarith
  calc r
    _ = (r + r) / 2 := by ring
    _ ≤ (3 - s + (s + 3)) / 2 := by rel [h3, h4]
    _ = 3 := by ring
}

-- 2.1.6 Example
example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by {
  have h1: x ≤ -1 := by{
    calc x
    _ = x + 3 - 3 := by ring
    _ ≤ 2 - 3 := by rel [hx]
    _ = -1 := by ring
    -- Or just use linarith
  }

  have h2 : 3 - 2 * x ≥ 5 := by{
    calc 3 - 2 * x
      _ ≥ 3 - 2 * (-1) := by rel [h1]
      _ = 3 + 2 := by ring
      _ = 5 := by ring
  }

  calc y
  _ = y + 2 * x - 2 * x := by ring
  _ ≥ 3 - 2 * x := by rel [hy]
  _ ≥ 5 := by rel [h2]
  _ > 3 := by norm_num
}

-- 2.1.7 Example
example (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by {
  have h2: 0 ≤ a + b := by linarith
  have h3: 0 ≤ b - a := by linarith
  have h4: 0 ≤ (a + b) * (b - a) := by{
    exact Left.mul_nonneg h2 h3
  }
  calc a ^ 2
  _ = a ^ 2 + 0 := by ring
  _ ≤ a ^ 2 + (a + b) * (b - a) := by rel [h4]
  _ = b ^ 2 := by ring
}

-- 2.1.8 Example
example (a b : ℝ) (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := by {
  have h2: 0 ≤ b - a := by linarith
  have h2_2: 0 ≤ (b - a) ^ 2 := by exact sq_nonneg (b - a)
  have h3: 0 ≤ (b + a) ^ 2 := by exact sq_nonneg (b + a)
  have h4: 0 ≤ 3 * (b + a) ^ 2 := by linarith
  have h5: 0 ≤ (b - a) ^ 2 + 3 * (b + a) ^ 2 := by {
    linarith
  }

  have h6: 0 ≤ (b - a) * ((b - a)^2 + 3 * (b + a) ^ 2) := by{
    exact Left.mul_nonneg h2 h5
  }
  have h7: 0 ≤ ((b - a) * ((b - a)^2 + 3 * (b + a) ^ 2))/4 := by{
    linarith
  }

  calc a ^ 3
  _ = a ^ 3 + 0 := by ring
  _ ≤ a ^ 3 + ((b - a) * ((b - a)^2 + 3 * (b + a) ^ 2))/4 := by rel [h7]
  _ = b ^ 3 := by ring
}

-- 2.1.9.1 Example
example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by {
  have h3 : x = 2 ∨ x = -2 := by {
    exact sq_eq_sq_iff_eq_or_eq_neg.mp h1
  }
  cases h3 with
  | inl h4 => exact h4
  | inr h5 => linarith -- Not possible due to contradiction so it ignores, pretty cool
}

-- 2.1.9.2 Example
example {n : ℤ} (hn : n ^ 2 + 4 = 4 * n) : n = 2 := by {
  have h1: (n - 2)^ 2 = 0 := by {
    linarith -- It manipulates hn
  }
  have h2: n - 2 = 0 := by {
    exact pow_eq_zero h1
  }
  linarith
}

-- 2.1.9.3 Example
example (x y : ℚ) (h : x * y = 1) (h2 : x ≥ 1) : y ≤ 1 := by {
  have h3 : y = 1 / x := by {
    rw [← eq_one_div_of_mul_eq_one_right h]
  }
  rw [h3]

  exact div_le_self rfl h2
}
