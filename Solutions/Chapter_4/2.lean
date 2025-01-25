import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Int.ModEq

-- 4.2.3 Example
-- Different from how the book would want. This is as I use Mathlib's definition and
-- not the book's redefinition of congruence.
theorem odd_iff_modEq (n : ℤ) : Odd n ↔ n ≡ 1 [ZMOD 2] := by {
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Int.ModEq]
    rw [hk]
    rw [Int.add_emod, Int.mul_emod_right]
    simp
  · intro h
    exact Int.odd_iff.mpr h
}

-- 4.2.4 Example
theorem even_iff_modEq (n : ℤ) : Even n ↔ n ≡ 0 [ZMOD 2] := by {
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    dsimp [Int.ModEq]
    rw [hk]
    have h1: k * 2 % 2 = 0 := by exact Int.mul_emod_left k 2
    ring_nf
    exact h1
  · intro h
    exact Int.even_iff.mpr h
}

-- 4.2.5 Example
example {x : ℝ} : x ^ 2 + x - 6 = 0 ↔ x = -3 ∨ x = 2 := by {
  constructor
  · intro h
    have h1 : (x + 3) * (x - 2) = 0 := by linarith
    simp [mul_eq_zero] at h1
    rcases h1 with h2 | h3
    · left
      linarith
    · right
      linarith
  · intro h
    rcases h with h1 | h2
    rw [h1]
    norm_num
    rw [h2]
    norm_num
}

-- 4.2.6 Example
example {a : ℤ} : a ^ 2 - 5 * a + 5 ≤ -1 ↔ a = 2 ∨ a = 3 := by {
  constructor
  · intro h
    have h1: (2 * a - 5) ^ 2 ≤ 1 ^ 2 := by{
      calc (2 * a - 5) ^ 2
      _ = 4 * (a ^ 2 - 5 * a + 5) + 5 := by ring
      _ ≤ 4 * (-1) + 5 := by rel [h]
      _ = 1 ^ 2 := by ring
    }
    have h2: -1 ≤ 2 * a - 5 ∧ 2 * a - 5 ≤ 1 := by{
      refine abs_le.mp ?_
      exact (sq_le_one_iff_abs_le_one (2 * a - 5)).mp h1
    }
    rcases h2 with ⟨h3, h4⟩
    have h5: 2 ≤ a := by linarith
    have h6: a ≤ 3 := by linarith
    have h7: a = 2 ∨ a = 3 := by omega
    rcases h7 with h7 | h8
    · left
      exact h7
    · right
      exact h8
  intro h
  rcases h with h1 | h2
  rw [h1]
  simp
  rw [h2]
  simp
}

-- 4.2.7 Example
example {n : ℤ} (hn : n ^ 2 - 10 * n + 24 = 0) : Even n := by {
  have hn1 :=
    calc (n - 4) * (n - 6) = n ^ 2 - 10 * n + 24 := by ring
      _ = 0 := hn
  have hn2 := eq_zero_or_eq_zero_of_mul_eq_zero hn1
  cases hn2 with
  | inl h1 => {
    use 2
    calc n
    _ = n - 4 + 4 := by ring
    _ = 0 + 4 := by rw [h1]
    _ = 2 + 2 := by norm_num
  }| inr h1 => {
    use 3
    calc n
    _ = n - 6 + 6 := by ring
    _ = 0 + 6 := by rw [h1]
    _ = 3 + 3 := by norm_num
  }
}

-- 4.2.9 Example
example (n : ℤ) : Even n ∨ Odd n := by {
  have h : n % 2 = 0 ∨ n % 2 = 1 := by exact Int.emod_two_eq n
  cases h with
  | inl h1 => {
    left
    exact (even_iff_modEq n).mpr h1
  } | inr h1 => {
    right
    exact (odd_iff_modEq n).mpr h1
  }
}

-- 4.2.10.1 Example
example {x : ℝ} : 2 * x - 1 = 11 ↔ x = 6 := by {
  constructor
  · intro h
    linarith
  · intro h
    linarith
}

-- 4.2.10.2 Example
example {n : ℤ} : 63 ∣ n ↔ 7 ∣ n ∧ 9 ∣ n := by {
  constructor
  · intro h
    rcases h with ⟨c, hc⟩
    constructor
    · use 9 * c
      linarith
    · use 7 * c
      linarith
  · intro h
    omega -- this is just the proof from 3.5.4.3
}

-- 4.2.10.3 Example
theorem dvd_iff_modEq {a n : ℤ} : n ∣ a ↔ a ≡ 0 [ZMOD n] := by {
  constructor
  · intro h
    rcases h with ⟨c, hc⟩
    rw [hc]
    dsimp [Int.ModEq]
    simp
  intro h
  dsimp [Int.ModEq] at *
  exact Int.dvd_of_emod_eq_zero h
}

-- 4.2.10.4 Example
example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by {
  rcases hab with ⟨c, hc⟩
  rw [hc]
  use (2 * a ^ 2 * c ^ 3 - a * c ^ 2 + 3 * c)
  ring
}

-- 4.2.10.5 Example
example {k : ℕ} : k ^ 2 ≤ 6 ↔ k = 0 ∨ k = 1 ∨ k = 2 := by {
  constructor
  · intro h
    have h1 : k ≤ 2 := by nlinarith
    have h2: k = 0 ∨ k = 1 ∨ k = 2 := by omega
    exact h2
  · intro h
    rcases h with h1 | h2 | h3
    rw [h1]
    norm_num
    rw [h2]
    norm_num
    rw [h3]
    norm_num
}
