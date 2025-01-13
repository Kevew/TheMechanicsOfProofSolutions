import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

-- My proofs on this page might differ more than yours. I used contradiction more often here.

-- 2.5.2 Example
-- I just decided to do a proof by contradiction here
-- It seems more natural
example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by {
  rcases h with ⟨x, hxt⟩
  have H := le_or_gt x 0
  intro ht
  rw [ht, mul_zero] at hxt
  simp at hxt
}

-- 2.5.3 Example
example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  norm_num

-- 2.5.4 Example
example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  linarith

-- 2.5.5 Example
example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6
  use 5
  norm_num

-- 2.5.6 Example
example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by {
  use (a + 1)
  use a
  linarith
}

-- 2.5.7 Example
example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by {
  use (p + q)/2
  constructor
  · calc p
    _ = (p + p)/2 := by ring
    _ < (p + q)/2 := by rel [h]
  · calc q
    _ = (q + q)/2 := by ring
    _ > (p + q)/2 := by rel [h]
}

-- 2.5.9.1 Example
example : ∃ t : ℚ, t ^ 2 = 1.69 := by{
  use 1.3
  norm_num
}

-- 2.5.9.2 Example
example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by {
  use 9
  use 2
  norm_num
}

-- 2.5.9.3 Example
example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by {
  use -0.5
  norm_num
}

-- 2.5.9.4 Example
example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by {
  use 4
  use 3
  norm_num
}


-- 2.5.9.5 Example
example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  use abs x + 1
  have h1: (abs x + 1)^2 = abs x ^ 2 + 2 * abs x + 1 := by ring
  rw [h1]

  have h : x ^ 2 + 1 > x := by{
    suffices x ^ 2 - x + 1 > 0 by linarith
    have : x ^ 2 - x + 1 = (x - 1/2)^2 + 3/4 := by ring
    rw [this]
    apply add_pos_of_nonneg_of_pos
    · apply sq_nonneg
    · norm_num
  }

  calc abs x^2 + 2 * abs x + 1
  _ ≥ abs x ^ 2 + 0 + 1 := by linarith [abs_nonneg x]
  _ = abs x ^ 2 + 1 := by ring
  _ ≥ x ^ 2 + 1 := by rw [sq_abs]
  _ > x := by rel [h]


-- 2.5.9.6 Example
-- Contradiction is still easier here
example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by {
  intro tt
  rcases h with ⟨a, ha⟩
  rw [tt] at ha
  simp at ha
}

-- 2.5.9.7 Example
example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by {
  intro t
  rcases h with ⟨a, ha⟩
  rw [t] at ha
  have h1: (2 : ℤ) ∣ 5 := by exact Dvd.intro a ha
  have h2 : ((5: ℤ) % 2) = 0 := by{
    exact Int.emod_eq_zero_of_dvd h1
  }
  simp at h2
}

-- 2.5.9.8 Example
-- I spent way too long thinking n was a real number...
-- I think 'use |x| + 2' works as well and might be easier than what I did.
-- Also a easy way of solving this could be a single inequality like the following:
-- a = n^2 + 7 => n * a + 7 < n * a + n < n(a + 1) < n*n^2 < 2n^3
-- It really shows there a so many ways of solving a mathematical statemet.
example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by {
  use n^2 + 2
  have h1 (a): 2 * a ^ 3 - n * a - 7 ≥ 0 → 2 * a ^ 3 ≥ n * a + 7 := by{
    intro a
    linarith
  }
  apply h1
  calc 2 * (n^2 + 2)^3 - n * (n^2 + 2) - 7
    _ = 2 * (n^6 + 6 * n^4 + 12 * n^2 + 8) - (n^3 + 2 * n) - 7 := by ring
    _ = 2 * n^6 + 12 * n^4 + 24 * n^2 + 16 - n^3 - 2 * n - 7 := by ring
    _ = 2 * n^6 + 12 * n^4 - n^3 + 24 * n^2 - 2 * n + 9 := by ring
    _ ≥ 0 := by{
      by_cases h : |n| ≤ 1
      · -- Case 1: |n| ≤ 1
        cases' Int.abs_le_one_iff.mp h with hn hn
        · -- n = 0
          rw [hn]
          linarith
        · -- n = 1 or n = 2
          rcases hn with h2 | h3
          rw [h2]
          linarith
          rw [h3]
          linarith
      · -- Case 2: |n| ≥ 2
        push_neg at h
        have h5 : |n| ≥ 2 := h
        have h2 : 2 * n ^ 6 - n ^ 3 ≥ 0 := by {
          have rewrite: (n^2) * (2 * n ^ 4 - n) ≥ 0 → 2 * n ^ 6 - n ^ 3 ≥ 0 := by{
            intro a
            linarith
          }
          have h2a : 2 * n ^ 4 - n ≥ 0 := by{
            have : n ≤ n^2 := by exact Int.le_self_sq n
            have : n^2 ≤ (n^2)^2 := by exact Int.le_self_sq (n ^ 2)
            have : (n^2)^2 ≥ 0 := by exact sq_nonneg (n ^ 2)
            linarith
          }
          apply rewrite
          calc n ^ 2 * (2 * n ^ 4 - n)
          _ ≥ n ^ 2 * (0) := by rel [h2a]
          _ ≥ 0 := by linarith
        }
        have h3 : 12 * n^4 - 2 * n ≥ 0 := by  {
          have : n ≤ n^2 := by exact Int.le_self_sq n
          have : n^2 ≤ (n^2)^2 := by exact Int.le_self_sq (n ^ 2)
          have : (n^2)^2 ≥ 0 := by exact sq_nonneg (n ^ 2)
          linarith
        }
        have h4 : 24 * n^2 ≥ 0 := by {
          have : n^2 ≥ 0 := by exact sq_nonneg n
          linarith
        }
        have h5 : 9 ≥ 0 := by linarith
        linarith
    }
}

-- 2.5.9.9 Example
example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by {
  use (b + c - a) / 2, (a + c - b) / 2, (a + b - c) / 2
  constructor
  · apply div_nonneg
    linarith
    norm_num
  constructor
  · apply div_nonneg
    linarith
    norm_num
  constructor
  · apply div_nonneg
    linarith
    norm_num
  constructor
  · linarith
  constructor
  · linarith
  linarith
}
