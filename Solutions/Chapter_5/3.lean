import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

-- 5.3.1 Example
example (P Q : Prop) : ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q) := by {
  constructor
  · intro h
    by_cases hP : P
    · right
      intro hQ
      have hPQ : P ∧ Q := by {
      · constructor
        · apply hP
        · apply hQ
      }
      contradiction
    · left
      apply hP
  · intro h
    by_cases hP : Q
    intro h1
    · rcases h with h2 | h3
      have h3: P := by exact h1.left
      contradiction
      contradiction
    intro h1
    · rcases h with h2 | h3
      have h3: P := by exact h1.left
      contradiction
      have h4: Q := by exact h1.right
      contradiction
}

-- 5.3.3 Example
example : ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
  ↔ ∃ n : ℤ, ∀ m : ℤ, n ^ 2 ≥ m ∨ m ≥ (n + 1) ^ 2 := by {
  calc  ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
  _ ↔ ∃n : ℤ, ¬(∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2) := by exact not_forall
  _ ↔ ∃n : ℤ, ∀ m : ℤ, ¬((n ^ 2 < m) ∧ (m < (n + 1) ^ 2)) := by simp
  _ ↔ ∃n : ℤ, ∀ m : ℤ, ¬(n ^ 2 < m) ∨ ¬(m < (n + 1) ^ 2) := by sorry -- Couldn't find not_and that works. Strangely not_or exists.
  _ ↔ ∃n : ℤ, ∀ m : ℤ, n ^ 2 ≥ m ∨ m ≥ (n + 1) ^ 2 := by simp
}

lemma le_or_succ_le (a b : ℕ) : a ≤ b ∨ b + 1 ≤ a := sorry

-- 5.3.5 Example
example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  push_neg
  intro n
  have hn := by {
    exact le_or_succ_le n 1
  }
  obtain hn | hn := hn
  · apply ne_of_lt
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by norm_num
  · apply ne_of_gt
    have h1: 2 ≤ n := by linarith
    calc 2
    _ = 1 + 1 := by ring
    _ ≤ n := by rel [hn]
    _ < n ^ 2 := by nlinarith

-- 5.3.6.1 Example
example (P : Prop) : ¬ (¬ P) ↔ P := by{
  push_neg
  trivial
}

-- 5.3.6.2 Example
example (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by {
  push_neg
  constructor
  · intro h
    rcases h with ⟨h1, h2⟩
    exact ⟨h1,h2⟩
  · intro h
    exact h
}

-- 5.3.6.3 Example
example (P : α → Prop) : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := by {
  push_neg
  constructor
  · intro h
    exact h
  · intro h
    exact h
}

-- 5.3.6.4 Example
example : (¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
    ↔ ∃ a b : ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 := by {
  calc (¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
  _ ↔ ∃ a b : ℤ, ¬(a * b = 1 → a = 1 ∨ b = 1) := by simp
  _ ↔ ∃ a b : ℤ, a * b = 1 ∧ ¬(a = 1 ∨ b = 1) := by simp
  _ ↔ ∃ a b : ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 := by simp
}

-- 5.3.6.5 Example
example : (¬ ∃ x : ℝ, ∀ y : ℝ, y ≤ x) ↔ (∀ x : ℝ, ∃ y : ℝ, y > x) := by {
  calc (¬ ∃ x : ℝ, ∀ y : ℝ, y ≤ x)
  _ ↔ (∀ x : ℝ, ∃ y : ℝ, y > x) := by simp
}

-- 5.3.6.6 Example
example : ¬ (∃ m : ℤ, ∀ n : ℤ, m = n + 5) ↔ ∀ m : ℤ, ∃ n : ℤ, m ≠ n + 5 := by {
  calc ¬ (∃ m : ℤ, ∀ n : ℤ, m = n + 5)
  _ ↔ ∀ m : ℤ, ∃ n : ℤ, m ≠ n + 5 := by simp
}

-- 5.3.6.7 Example
#push_neg ¬(∀ n : ℕ, n > 0 → ∃ k l : ℕ, k < n ∧ l < n ∧ k ≠ l)
#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
#push_neg ¬(∃ x : ℝ, ∀ y : ℝ, ∃ m : ℤ, x < y * m ∧ y * m < m)
#push_neg ¬(∃ x : ℝ, ∀ q : ℝ, q > x → ∃ m : ℕ, q ^ m > x)


-- 5.3.6.8 Example
example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by
  push_neg
  use 0.5
  linarith


-- 5.3.6.9 Example
example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  push_neg
  intro t h1
  linarith

-- 5.3.6.10 Example
example : ¬ Even 7 := by
  dsimp [Even]
  push_neg
  intro r a
  omega

def Prime (p : ℕ) : Prop :=
  2 ≤ p ∧ ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p

-- 5.3.6.11 Example
example {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬ Prime p := by
  dsimp [Prime]
  push_neg
  intro h1
  use k

-- 5.3.6.12 Example
example : ¬ ∃ a : ℤ, ∀ n : ℤ, 2 * a ^ 3 ≥ n * a + 7 := by {
  push_neg
  intro h
  use 2 * h ^ 2
  linarith
}


-- From 4.4.4
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

-- 5.3.7.13 Example
example {p : ℕ} (hp : ¬ Prime p) (hp2 : 2 ≤ p) : ∃ m, 2 ≤ m ∧ m < p ∧ m ∣ p := by
  have H : ¬ (∀ (m : ℕ), 2 ≤ m → m < p → ¬m ∣ p) := by {
  · intro H
    have h1: Prime p := by {
      exact prime_test hp2 H
    }
    contradiction
  }
  push_neg at H
  exact H
