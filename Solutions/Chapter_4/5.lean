import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Int.ModEq

def Prime (p : ℕ) : Prop :=
  2 ≤ p ∧ ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p

-- 4.5.1 Example
example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by {
  intro h
  have h1: (0.5 : ℝ) ^ 2 ≥ 0.5 := by{
    exact h 0.5
  }
  linarith
}

-- 4.5.2 Example
example : ¬ 3 ∣ 13 := by {
  intro h
  rcases h with ⟨c, hc⟩
  have h: 5 ≤ c ∨ c ≤ 4 := by omega
  cases h with
  | inl h1 => {
    have h2: 13 ≥ 3 * 5 := by {
      calc 13
      _ = 3 * c := by rw [hc]
      _ ≥ 3 * 5 := by rel [h1]
    }
    linarith
  }
  | inr h1 => {
    have h2: 13 ≤ 3 * 4 := by {
      calc 13
      _ = 3 * c := by rw [hc]
      _ ≤ 3 * 4 := by rel [h1]
    }
    linarith
  }
}

-- 4.5.4 Example
example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by {
  intro h
  rcases h with ⟨n, hn⟩
  have h1: n ≤ 1 ∨ n ≥ 2 := by omega
  cases h1 with
  | inl h1 => {
    have : 2 ≤ 1 ^ 2 := by{
      calc 2
      _ = n ^ 2 := by rw [hn]
      _ ≤ 1 ^ 2 := by rel [h1]
    }
    linarith
  }
  | inr h1 => {
    have : 2 ≥ 2 ^ 2 := by{
      calc 2
      _ = n ^ 2 := by rw [hn]
      _ ≥ 2 ^ 2 := by rel [h1]
    }
    linarith
  }
}

-- 4.5.5 Example
example (n : ℤ) : Odd n ↔ ¬ Even n := by {
  exact Int.not_even_iff_odd.symm
}

-- 4.5.8 Example
example (a b : ℤ) (h : ∃ q, b * q < a ∧ a < b * (q + 1)) : ¬b ∣ a := by {
  intro H
  obtain ⟨k, hk⟩ := H
  obtain ⟨q, hq₁, hq₂⟩ := h
  have hb :=
  calc 0 = a - a := by ring
    _ < b * (q + 1) - b * q := by rel [hq₁, hq₂]
    _ = b := by ring
  have h1 :=
  calc b * k = a := by rw [hk]
    _ < b * (q + 1) := hq₂
  have h2: k < (q + 1) := by {
    apply (mul_lt_mul_left hb).mp
    exact h1
  }
  have h3: b * q < b * k := by {
    calc b * q
    _ < a := by rel [hq₁]
    _ = b * k := by rw [hk]
  }
  have h4: q < k := by {
    exact (mul_lt_mul_left hb).mp h3
  }
  linarith
}

theorem prime_test {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by {
  constructor
  · apply hp -- show that `2 ≤ p`
  intro m hmp
  have hp' : 0 < p := by linarith
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp'
  obtain hm | hm_left : 1 = m ∨ 1 < m := eq_or_lt_of_le h1m
  · -- the case `m = 1`
    left
    linarith
  -- the case `1 < m`
  right
  have h1 : m ≤ p := by exact Nat.le_of_dvd hp' hmp
  have h2 : p = m ∨ m < p := by exact LE.le.eq_or_gt h1
  rcases h2 with h3 | h4
  exact id (Eq.symm h3)
  tauto
}


-- 4.5.9 Example
theorem better_prime_test {p : ℕ} (hp : 2 ≤ p)  (T : ℕ) (hTp : p < T ^ 2)
    (H : ∀ (m : ℕ), 1 < m → m < T → ¬ (m ∣ p)) :
    Prime p := by {
  apply prime_test hp
  intro m hm1 hmp
  obtain hmT | hmT := lt_or_le m T
  · apply H m hm1 hmT
  intro h_div
  obtain ⟨l, hl⟩ := h_div
  have : l ∣ p := by {
    exact Dvd.intro_left m (id (Eq.symm hl))
  }
  have hl1 :=
    calc m * 1 = m := by ring
      _ < p := hmp
      _ = m * l := hl
  have hl3: 1 < l := by {
    exact Nat.lt_of_mul_lt_mul_left hl1
  }
  have h : T * l < T * T := by {
    calc T * l
    _ ≤ m * l := by rel [hmT]
    _ = p := by rw [hl]
    _ < T ^ 2 := by rel [hTp]
    _ = T * T := by ring
  }
  have hl2 : l < T := by {
    exact Nat.lt_of_mul_lt_mul_left h
  }
  have : ¬ l ∣ p := H l hl3 hl2
  contradiction
}

lemma Nat.not_dvd_of_exists_lt_and_lt (a b : ℕ)
  (h : ∃ q, b * q < a ∧ a < b * (q + 1)) :
  ¬b ∣ a := sorry

-- 4.5.9.2 Example
example : Prime 79 := by
  apply better_prime_test (T := 9)
  · norm_num
  · norm_num
  intro m hm1 hm2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases m
  · use 39
    constructor <;> norm_num
  · use 26
    constructor <;> norm_num
  · use 19
    constructor <;> norm_num
  · use 15
    constructor <;> norm_num
  · use 13
    constructor <;> norm_num
  · use 11
    constructor <;> norm_num
  · use 9
    constructor <;> norm_num

-- 4.5.10.1 Example
example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by {
  intro h
  rcases h with ⟨c, hc⟩
  linarith
}

-- 4.5.10.2 Example
example : ¬ (∃ a : ℝ, a ^ 2 ≤ 8 ∧ a ^ 3 ≥ 30) := by {
  intro h
  rcases h with ⟨c, hc⟩
  rcases hc with ⟨h1, h2⟩
  have h3 : c ≤ 8 ^ (1 / 2) := by {
    nlinarith
  }
  have h4 : 30 ^ (1 / 3) ≤ c := by {
    nlinarith
  }
  nlinarith
}

-- 4.5.10.3 Example
example : ¬ Even 7 := by {
  dsimp [Even]
  intro h
  rcases h with ⟨c, hc⟩
  omega
}

-- 4.5.10.4 Example
example {n : ℤ} (hn : n + 3 = 7) : ¬ (Even n ∧ n ^ 2 = 10) := by {
  intro h
  rcases h with ⟨h1, h2⟩
  rcases h1 with ⟨c, hc⟩
  rw [hc] at h2
  rw [hc] at hn
  have h1: c = 2 := by{
    linarith
  }
  rw [h1] at h2
  omega
}

-- 4.5.10.5 Example
example {x : ℝ} (hx : x ^ 2 < 9) : ¬ (x ≤ -3 ∨ x ≥ 3) := by {
  intro h
  rcases h with h1 | h2
  nlinarith
  nlinarith
}

-- 4.5.10.6 Example
example : ¬ (∃ N : ℕ, ∀ k > N, Even k) := by {
  intro h
  rcases h with ⟨c, hc⟩
  dsimp [Even] at hc
  specialize hc (2 * c + 1)
  have hc_h : 2 * c + 1 > c := by linarith
  have h1: ∃ r, 2 * c + 1 = r + r := by {
    exact hc hc_h
  }
  rcases h1 with ⟨d, hd⟩
  omega
}

-- 4.5.10.8 Example
example : ¬ Prime 1 := by {
  intro h
  dsimp [Prime] at h
  rcases h with ⟨h1, h2⟩
  contradiction
}

-- 4.5.10.9 Example
example : Prime 97 := by {
  apply better_prime_test (T:= 10)
  · norm_num
  · norm_num
  intro h h1 h2
  apply Nat.not_dvd_of_exists_lt_and_lt
  interval_cases h
  · use 48
    constructor <;> norm_num
  · use 32
    constructor <;> norm_num
  · use 24
    constructor <;> norm_num
  · use 19
    constructor <;> norm_num
  · use 16
    constructor <;> norm_num
  · use 13
    constructor <;> norm_num
  · use 12
    constructor <;> norm_num
  · use 10
    constructor <;> norm_num
}
