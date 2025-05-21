import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith

-- 6.4.1 Example
def F : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => F (n + 1) + F n

theorem F_bound (n : ℕ) : F n ≤ 2 ^ n := by
  match n with
  | 0 =>
      calc F 0 = 1 := by rw [F]
        _ ≤ 2 ^ 0 := by norm_num
  | 1 =>
      calc F 1 = 1 := by rw [F]
        _ ≤ 2 ^ 1 := by norm_num
  | k + 2 =>
      have IH1 := F_bound k -- first inductive hypothesis
      have IH2 := F_bound (k + 1) -- second inductive hypothesis
      calc F (k + 2) = F (k + 1) + F k := by rw [F]
        _ ≤ 2 ^ (k + 1) + 2 ^ k := by rel [IH1, IH2]
        _ ≤ 2 ^ (k + 1) + 2 ^ k + 2 ^ k := by norm_num
        _ = 2 ^ (k + 2) := by ring

theorem extract_pow_two (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by {
  match n with
  | 0 => {
    contradiction
  }| 1 => {
    use 0
    use 1
    constructor
    · exact Nat.odd_iff.mpr rfl
    · norm_num
  }| k + 2 => {
    by_cases h: Even (k + 2)
    · have : 2 * ((k + 2) / 2) = k + 2 := by exact Nat.two_mul_div_two_of_even h -- needed for linarith next line
      have h1: (k + 2) / 2 > 0 := by linarith
      have h2 := extract_pow_two ((k + 2)/2) (h1)
      rcases h2 with ⟨a, ⟨b, ⟨hb1, hb2⟩ ⟩⟩
      use a + 1, b
      constructor
      · exact hb1
      · calc k + 2
        _ = 2 * ((k + 2) / 2) := by rw [this]
        _ = 2 * (2 ^ a * b) := by rw [hb2]
        _ = 2 ^ (a + 1) * b := by ring
    · use 0
      use k + 2
      constructor
      · exact Nat.not_even_iff_odd.mp h
      · linarith
  }
}
