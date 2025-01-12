import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

-- 2.3.1 Example
-- I like rcases more than using obtain
example {x y : ℝ} (h : x = 1 ∨ y = -1) : x * y + x = y + 1 := by
  rcases h with hx | hy
  calc
    x * y + x = 1 * y + 1 := by rw [hx]
    _ = y + 1 := by ring
  calc
    x * y + x = x * -1 + x := by rw [hy]
    _ = -1 + 1 := by ring
    _ = y + 1 := by rw [hy]


lemma le_or_succ_le (a b : ℕ) : a ≤ b ∨ b + 1 ≤ a := by{
  induction a with
  | zero => {
    left
    exact Nat.zero_le b
  }
  | succ n ih => {
    rcases ih with h1 | h2

    cases Nat.eq_or_lt_of_le h1 with
    | inl h_eq => {
      right
      rw [h_eq]
    }
    | inr h_lt => {
      left
      exact h_lt
    }
    right
    exact Nat.le_add_right_of_le h2
  }
}


-- 2.3.2 Example
example {n : ℕ} : n ^ 2 ≠ 2 := by {
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  apply ne_of_lt
  calc
    n ^ 2 ≤ 1 ^ 2 := by rel [hn]
    _ < 2 := by norm_num
  apply ne_of_gt
  have h1: 2 ≤ n := by rel [hn]
  calc 2
  _ ≤  n := by rel [h1]
  _ < n ^ 2 := by {
    apply lt_self_pow₀
    linarith
    linarith
  }
}

-- 2.3.3 Example
example {x : ℝ} (hx : 2 * x + 1 = 5) : x = 1 ∨ x = 2 := by
  right
  calc
    x = (2 * x + 1 - 1) / 2 := by ring
    _ = (5 - 1) / 2 := by rw [hx]
    _ = 2 := by norm_num

-- 2.3.4 Example
example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h1 :=
    calc
    (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
    _ = 0 := by rw [hx]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  rcases h2 with h3 | h4
  left
  linarith
  right
  linarith


-- 2.3.6.1 Example
-- This proof proves the next 4 proofs lol
example {x : ℚ} (h : x = 4 ∨ x = -4) : x ^ 2 + 1 = 17 := by {
  cases h with
  | inl h1 => {
    rw [h1]
    norm_num
  }
  | inr h2 =>{
    rw [h2]
    ring
  }
}

-- 2.3.6.2 Example
example {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by {
  cases h with
  | inl h1 => {
    rw [h1]
    norm_num
  }
  | inr h2 => {
    rw [h2]
    ring
  }
}

-- 2.3.6.3 Example
example {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by {
  cases h with
  | inl h1 => {
    rw [h1]
    norm_num
  }
  | inr h2 => {
    rw [h2]
    ring
  }
}

-- 2.3.6.4 Example
example {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by {
  cases h with
  | inl h1 => {
    rw [h1]
    norm_num
  }
  | inr h2 => {
    rw [h2]
    ring
  }
}

-- 2.3.6.5 Example
example {s t : ℚ} (h : s = 3 - t) : s + t = 3 ∨ s + t = 5 := by {
  left
  rw [h]
  ring
}

-- 2.3.6.6 Example
example {a b : ℚ} (h : a + 2 * b < 0) : b < a / 2 ∨ b < - a / 2 := by {
  right
  linarith
}

-- 2.3.6.7 Example
example {x y : ℝ} (h : y = 2 * x + 1) : x < y / 2 ∨ x > y / 2 := by {
  left
  rw [h]
  ring
  norm_num -- Could also just used linarith
}

-- 2.3.6.8 Example
example {x : ℝ} (hx : x ^ 2 + 2 * x - 3 = 0) : x = -3 ∨ x = 1 := by {
  have h1 :=
    calc
    (x - 1) * (x + 3) = x ^ 2 + 2 * x - 3 := by ring
    _ = 0 := by rw [hx]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  rcases h2 with h3 | h4
  · right
    linarith
  · left
    linarith
}

-- 2.3.6.9 Example
example {a b : ℝ} (hab : a ^ 2 + 2 * b ^ 2 = 3 * a * b) : a = b ∨ a = 2 * b := by {
  have h1 :=
    calc
    a ^ 2 + 2 * b ^ 2 - 3 * a * b = 3 * a * b - 3 * a * b := by rw [hab]
    _ = 0 := by ring
  have h2 :=
    calc
    (a - 2 * b) * (a - b) = a ^ 2 + 2 * b ^ 2 - 3 * a * b := by ring
    _ = 0 := by rw [h1]
  have h3 := eq_zero_or_eq_zero_of_mul_eq_zero h2
  rcases h3 with h4 | h5
  right
  linarith
  left
  linarith
}

-- 2.3.6.10 Example
example {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by {
  have h1 : t ^ 3 - t ^ 2 = 0 := by exact sub_eq_zero_of_eq ht
  have h2 : t ^ 2 * (t - 1) = 0 := by {
      calc
      t ^ 2 * (t - 1) = t ^ 3 - t ^ 2 := by ring
      _ = 0 := by rw [h1]
  }
  have h3 := eq_zero_or_eq_zero_of_mul_eq_zero h2
  rcases h3 with h4 | h5
  right
  exact pow_eq_zero h4
  left
  linarith
}

-- 2.3.7.11 Example
example {n : ℕ} : n ^ 2 ≠ 7 := by {
  have hn := le_or_succ_le n 2
  rcases hn with h1 | h2
  · apply ne_of_lt
    calc
      n ^ 2 ≤ 2 ^ 2 := by rel [h1]
      _ < 7 := by norm_num
  · apply ne_of_gt
    calc
      7 < 3 ^ 2 := by norm_num
      _ ≤ n ^ 2 := by gcongr
}

-- 2.3.7.12 Example
example {x : ℤ} : 2 * x ≠ 3 := by {
  intro h
  rw [mul_comm] at h
  have h1: (2:ℤ) ∣ 3 := by{
    exact Dvd.intro_left x h
  }
  have : ((3: ℤ) % 2) = 0 := by{
    exact Int.emod_eq_zero_of_dvd h1
  }
  simp at this
}

-- 2.3.7.13 Example
example {t : ℤ} : 5 * t ≠ 18 := by {
  intro h
  rw [mul_comm] at h
  have h1: (5:ℤ) ∣ 18 := by{
    exact Dvd.intro_left t h
  }
  have : ((18: ℤ) % 5) = 0 := by{
    exact Int.emod_eq_zero_of_dvd h1
  }
  simp at this
}

-- 2.3.7.14 Example
example {m : ℕ} : m ^ 2 + 4 * m ≠ 46 := by {
  have h1: Even m ∨ Odd m := by{
    exact Nat.even_or_odd m
  }
  intro test
  have h4: (m ^ 2 + 4 * m) % 4 = 46 % 4 := by{
    rw [test]
  }
  simp at h4
  rcases h1 with h2 | h3
  · rcases h2 with ⟨a, ha⟩
    have evenM : m = 2 * a := by linarith
    rw [evenM] at h4
    have h6 : (2 * a) ^ 2 = 4 * a ^ 2 := by ring
    rw [h6] at h4
    simp at h4
  · rcases h3 with ⟨b, hb⟩
    rw [hb] at h4
    have h6 : (2 * b + 1) ^ 2 = 4 * (b ^ 2 + b) + 1 := by ring
    rw [h6] at h4
    simp at h4
}
