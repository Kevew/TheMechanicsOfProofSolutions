import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith


def Prime (p : ℕ) : Prop :=
  2 ≤ p ∧ ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p

def Superpowered (k : ℕ) : Prop := ∀ n : ℕ, Prime (k ^ k ^ n + 1)

theorem not_superpowered_zero : ¬ Superpowered 0 := by
  intro h
  have one_prime : Prime (0 ^ 0 ^ 0 + 1) := h 0
  conv at one_prime => norm_num
  have : ¬ Prime 1 := sorry
  contradiction

theorem superpowered_one : Superpowered 1 := by
  intro n
  conv => ring -- simplifies goal from `Prime (1 ^ 1 ^ n + 1)` to `Prime 2`
  sorry -- The prime_two is from chapter 4.1

-- 5.2.7.1 Example
def Tribalanced (x : ℝ) : Prop := ∀ n : ℕ, (1 + x / n) ^ n < 3

example : ∃ x : ℝ, Tribalanced x ∧ ¬ Tribalanced (x + 1) := by {
  by_cases h1: Tribalanced (0.5 : ℝ)
  · use (0.5 : ℝ)
    constructor
    · exact h1
    · intro h2
      specialize h2 3
      have h3:(1 + (0.5 + 1) / ↑3)^3 > (3 : ℝ) := by {
        calc ((1 : ℝ) + (0.5 + 1) / ↑3)^3
        _ = 3.375 := by norm_num
        _ > 3 := by norm_num
      }
      linarith
  · use (-0.5 : ℝ)
    constructor
    · intro n
      have h5: (1 + (-0.5 : ℝ) / ↑n) ^ n ≤ 1 ^ n := by {
        have h6: 1 + (-0.5 : ℝ) / ↑n ≤ 1 := by {
          have : (-0.5 : ℝ) / ↑n ≤ 0 := by
            apply div_nonpos_of_nonpos_of_nonneg
            · norm_num
            · exact Nat.cast_nonneg n
          linarith
        }
        have h7: 0 ≤ 1 + (-0.5 : ℝ) / n := by {
          have hn' : 0 ≤ n := by exact Nat.zero_le n
          have h₁ : (-0.5 : ℝ) / n ≥ -1 := by sorry -- not sure why linarith is not working here
          linarith
        }
        exact pow_le_pow_left₀ h7 h6 n
      }
      calc (1 + (-0.5 : ℝ) / ↑n) ^ n
      _ ≤ 1 ^ n := by rel [h5]
      _ < 3 := by norm_num
    · have h5: (-0.5 + 1) = (0.5 : ℝ) := by ring
      rw [h5]
      exact h1
}

-- 5.2.7.2 Example
example (P Q : Prop) : (¬P → ¬Q) ↔ (Q → P) := by {
  by_cases h: P
  · constructor
    · intro h1 h2
      exact h
    · intro h1 h2
      contradiction
  · constructor
    · intro h1 h2
      apply h1 at h
      contradiction
    · intro h1 h2
      by_cases h3: Q
      · apply h1 at h3
        contradiction
      · exact h3
}

-- 5.2.7.3 Example
example : ∃ k : ℕ, Superpowered k ∧ ¬ Superpowered (k + 1) := by {
  use 1
  constructor
  · exact superpowered_one
  · intro h
    conv at h => ring
    specialize h 5
    dsimp [Prime] at h
    rcases h with ⟨h1, h2⟩
    specialize h2 641
    have h3: 641 ∣ 4294967297 := by omega
    apply h2 at h3
    rcases h3 with h4 | h5
    contradiction
    contradiction
}
