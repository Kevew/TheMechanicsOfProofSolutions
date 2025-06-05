import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Set

-- 9.1.4 Example
example : ¬ {x : ℝ | 0 ≤ x ^ 2} ⊆ {t : ℝ | 0 ≤ t} := by
  dsimp [Set.subset_def]
  push_neg
  use -1
  constructor
  · norm_num
  · norm_num


-- 9.1.10.1 Example
example : 4 ∉ {a : ℚ | a < 3} := by
  dsimp only [Set.mem_setOf_eq]
  push_neg
  norm_num


-- 9.1.10.2 Example
example : 6 ∈ {n : ℕ | n ∣ 42} := by {
    dsimp only [Set.mem_setOf_eq]
    use 7
}


-- 9.1.10.3 Example
example : 8 ∉ {k : ℤ | 5 ∣ k} := by {
    simp only [Set.mem_setOf_eq]
    omega
}


-- 9.1.10.4 Example
example : 11 ∈ {n : ℕ | Odd n} := by {
    use 5
    norm_num
}


-- 9.1.10.5 Example
example : -3 ∈ {x : ℝ | ∀ y : ℝ, x ≤ y ^ 2} := by {
    intro x
    have h1: 0 ≤ x^2 := by exact sq_nonneg x
    calc -3 ≤ 0 := by norm_num
    _ ≤ x ^ 2 := by rel [h1]
}


-- 9.1.10.6 Example
example : {a : ℕ | 20 ∣ a} ⊆ {x : ℕ | 5 ∣ x} := by {
    simp only [Set.setOf_subset_setOf]
    intro a h1
    rcases h1 with ⟨k, hk⟩
    use 4 * k
    linarith
}


-- 9.1.10.7 Example
example : ¬ {a : ℕ | 5 ∣ a} ⊆ {x : ℕ | 20 ∣ x} := by {
    simp only [Set.setOf_subset_setOf]
    push_neg
    use 10
    constructor
    · use 2
    · omega
}


-- 9.1.10.8 Example
example : ¬ {r : ℤ | 3 ∣ r} ⊆ {s : ℤ | 0 ≤ s} := by {
    simp only [Set.setOf_subset_setOf]
    push_neg
    use -6
    constructor
    · use -2
      norm_num
    · norm_num
}


-- 9.1.10.9 Example
example : {m : ℤ | m ≥ 10} ⊆ {n : ℤ | n ^ 3 - 7 * n ^ 2 ≥ 4 * n} := by {
    simp only [ge_iff_le, Set.setOf_subset_setOf]
    intro a h1
    nlinarith
}


-- 9.1.10.10 Example
example : {n : ℤ | Even n} = {a : ℤ | a ≡ 6 [ZMOD 2]} := by {
    ext x
    dsimp only [Set.mem_setOf_eq]
    constructor
    · intro h1
      rcases h1 with ⟨k, hk⟩
      rw [hk]
      dsimp [Int.ModEq]
      calc (k + k) % 2
      _ = (2 * k) % 2 := by ring_nf
      _ = 0 := by exact Int.mul_emod_right 2 k
    · intro h1
      have : 2 ∣ x := by {
        exact Int.dvd_of_emod_eq_zero h1
      }
      rcases this with ⟨k, hk⟩
      use k
      linarith
}


-- 9.1.10.11 Example
example : {t : ℝ | t ^ 2 - 5 * t + 4 = 0} ≠ {4} := by {
    intro h
    have h1 : (1 : ℝ) ∈ {t : ℝ | t ^ 2 - 5 * t + 4 = 0} := by {
        simp only [Set.mem_setOf_eq, one_pow, mul_one]
        norm_num
    }
    rw [h] at h1
    simp at h1
}


-- 9.1.10.12 Example
example : {k : ℤ | 8 ∣ 6 * k} ≠ {l : ℤ | 8 ∣ l} := by {
  intro h1
  have h2 : 4 ∈ {k : ℤ | 8 ∣ 6 * k} := by
    show 8 ∣ 6 * (4 : ℤ)
    norm_num
  have h3 : 4 ∉ {l : ℤ | 8 ∣ l} := by
    show ¬ (8 ∣ (4 : ℤ))
    omega
  rw [h1] at h2
  contradiction
}


-- 9.1.10.13 Example
example : {k : ℤ | 7 ∣ 9 * k} = {l : ℤ | 7 ∣ l} := by {
  ext x
  dsimp only [Set.mem_setOf_eq]
  constructor
  · intro h1
    rcases h1 with ⟨k, hk⟩
    have : x = (7 * k) / 9 := by omega
    use k / 9
    omega
  · intro h1
    rcases h1 with ⟨k, hk⟩
    use 9 * k
    rw [hk]
    ring
}


-- 9.1.10.15 Example
example : {x : ℝ | x ^ 2 + 3 * x + 2 = 0} = {-1, -2} := by {
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h1
    have h2: (x + 1) * (x + 2) = 0 := by linarith
    have h3: x + 1 = 0 ∨ x + 2 = 0 := by exact mul_eq_zero.mp h2
    rcases h3 with h3 | h3
    · left
      linarith
    · right
      linarith
  · intro h1
    rcases h1 with h1 | h1
    · rw [h1]
      norm_num
    · rw [h1]
      norm_num
}
