import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Prime.Basic


-- 6.1.2 Example
example (n : ℕ) : Even n ∨ Odd n := by
  induction n with
  | zero => {
    left
    trivial
  }
  | succ k hk => {
    rcases hk with h1 | h2
    · right
      rcases h1 with ⟨a, ha⟩
      use a
      rw [ha]
      ring
    · left
      rcases h2 with ⟨a, ha⟩
      use a + 1
      rw [ha]
      ring
}

-- 6.1.3 Example
example {a b d : ℤ} (h : a ≡ b [ZMOD d]) (n : ℕ) : a ^ n ≡ b ^ n [ZMOD d] := by {
  induction n with
  | zero => {
    rfl
  }
  | succ k hk => {
    exact Int.ModEq.pow (k + 1) h
  }
}

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

-- 6.1.6 Example
example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by {
  dsimp
  use 4
  intro n hn
  induction' hn with k hk h1
  norm_num
  simp
  dsimp [Nat.le] at hk
  calc (k + 1) ^ 2
  _ = k ^ 2 + 2 * k + 1 := by ring
  _ ≤ k ^ 2 + 2 * k + 2 * 4 := by norm_num
  _ ≤ k ^ 2 + 2 * k + 2 * k := by rel [hk]
  _ = k ^ 2 + 4 * k := by ring
  _ ≤ k ^ 2 + k * k := by rel [hk]
  _ = 2 * k ^ 2 := by ring
  _ ≤ 2 * 2 ^ k := by rel [h1]
  _ = 2 ^ (k + 1) := by ring
}

-- 6.1.7.1 Example
example (n : ℕ) : 3 ^ n ≥ n ^ 2 + n + 1 := by {
  induction' n with k hk
  norm_num
  have h1: 3 * k ^ 2 ≥ k ^ 2 := by omega
  calc 3 ^ (k + 1)
  _ = 3 * 3 ^ k := by ring
  _ ≥ 3 * (k ^ 2 + k + 1) := by rel [hk]
  _ = 3 + k * 3 + k ^ 2 * 3 := by ring
  _ ≥ 3 + k * 3 + k ^ 2 := by linarith
  _ = (k + 1) ^ 2 + (k + 1) + 1 := by ring
}

-- 6.1.7.2 Example
example {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by {
  induction n with
  | zero => {
    norm_num
  }
  | succ k hk => {
    have h1: (1 + a) ≥ 0 := by exact neg_le_iff_add_nonneg'.mp ha
    have h2: a ^ 2 ≥ 0 := by exact sq_nonneg a
    calc (1 + a) ^ (k + 1)
    _ = (1 + a) ^ k * (1 + a) := by ring
    _ ≥ (1 + ↑k * a) * (1 + a) := by rel [hk]
    _ = 1 + ↑k * a + a + ↑k * a ^ 2 := by ring
    _ ≥ 1 + ↑k * a + a + ↑k * 0 := by rel [h2]
    _ = 1 + (↑k + 1) * a := by ring
    _ = 1 + ↑(k + 1) * a := by simp only [Nat.cast_add, Nat.cast_one]  }
}

-- 6.1.7.3 Example
example (n : ℕ) : 5 ^ n ≡ 1 [ZMOD 8] ∨ 5 ^ n ≡ 5 [ZMOD 8] := by {
  induction' n with k hk
  simp only [pow_zero, Int.ModEq.refl, true_or]
  rcases hk with h1 | h2
  · right
    have h2: (5:ℤ) ^ (k + 1) = 5 ^ k * 5 := by ring
    rw [h2]
    exact Int.ModEq.mul_right (5) h1
  · left
    have h1 : (5:ℤ)^(k+1) = 5^k * 5 := by ring
    have h3 : (5:ℤ)^k * 5 ≡ 5 * 5 [ZMOD 8] := by {
      exact Int.ModEq.mul h2 rfl
    }
    rw [h1]
    have h36 : (5 * 5:ℤ) ≡ 1 [ZMOD 8] := by rfl
    apply Int.ModEq.trans h3 h36
}

-- 6.1.7.4 Example
example (n : ℕ) : 6 ^ n ≡ 1 [ZMOD 7] ∨ 6 ^ n ≡ 6 [ZMOD 7] := by {
  induction' n with k hk
  simp only [pow_zero, Int.ModEq.refl, true_or]
  rcases hk with h1 | h2
  · right
    have h2: (6:ℤ) ^ (k + 1) = 6 ^ k * 6 := by ring
    rw [h2]
    exact Int.ModEq.mul_right (6) h1
  · left
    have h1 : (6:ℤ)^(k+1) = 6^k * 6 := by ring
    have h3 : (6:ℤ)^k * 6 ≡ 6 * 6 [ZMOD 7] := by {
      exact Int.ModEq.mul h2 rfl
    }
    rw [h1]
    have h36 : (6 * 6:ℤ) ≡ 1 [ZMOD 7] := by rfl
    apply Int.ModEq.trans h3 h36
}

-- Should probably have made a seperate lemma to simplify
-- 6.1.7.5 Example
example (n : ℕ) :
    4 ^ n ≡ 1 [ZMOD 7] ∨ 4 ^ n ≡ 2 [ZMOD 7] ∨ 4 ^ n ≡ 4 [ZMOD 7] := by {
  induction' n with k hk
  · simp
  · rcases hk with h1 | h1 | h1
    · right
      right
      have h2 : (4:ℤ)^(k+1) = 4^k * 4 := by ring
      have h3 : (4:ℤ)^k * 4 ≡ 1 * 4 [ZMOD 7] := by {
        exact Int.ModEq.mul h1 rfl
      }
      rw [h2]
      have h4 : (1 * 4:ℤ) ≡ 4 [ZMOD 7] := by rfl
      apply Int.ModEq.trans h3 h4
    · left
      have h2 : (4:ℤ)^(k+1) = 4^k * 4 := by ring
      have h3 : (4:ℤ)^k * 4 ≡ 2 * 4 [ZMOD 7] := by {
        exact Int.ModEq.mul h1 rfl
      }
      rw [h2]
      have h4 : (2 * 4:ℤ) ≡ 1 [ZMOD 7] := by rfl
      apply Int.ModEq.trans h3 h4
    · right
      left
      have h2 : (4:ℤ)^(k+1) = 4^k * 4 := by ring
      have h3 : (4:ℤ)^k * 4 ≡ 4 * 4 [ZMOD 7] := by {
        exact Int.ModEq.mul h1 rfl
      }
      rw [h2]
      have h4 : (4 * 4:ℤ) ≡ 2 [ZMOD 7] := by rfl
      apply Int.ModEq.trans h3 h4
}

-- 6.1.7.6 Example
-- The nat and the int is really messing with the exacts. Hmm.
example : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  use 8
  intro x h1
  induction x using Nat.strong_induction_on with
  | _ x ih => {
    have h3: x = 8 ∨ x > 8 := by exact LE.le.eq_or_gt h1
    cases h3 with
    | inl h2 => {
      rw [h2]
      norm_num
    }
    | inr h2 => {
      specialize ih (x - 1) (by omega) (by omega)
      have h4: x > 0 := by exact Nat.zero_lt_of_lt h1
      have whyisthisthecase: x = (x - 1 + 1) := by exact (Nat.sub_eq_iff_eq_add h4).mp rfl
      have h5: (3 : ℤ) ^ x = 3 ^ (x - 1 + 1) := by {
        rw [← whyisthisthecase]
      }
      have h6: (3 : ℤ) ^ (x - 1 + 1) = 3 ^ (x - 1) * 3:= by
        exact rfl
      calc
        (3 : ℤ) ^ x = 3 ^ (x - 1) * 3 := by rw [h5, h6]
        _ ≥ (2 ^ (x - 1) + 100) * 3 := by rel [ih]
        _ = 3/2 * (2 ^ x) + 300 := by
          sorry -- not sure why this is not trivial
        _ ≥ 2 ^ x + 100 := by
          omega
    }
  }


-- 6.1.7.9.1 Example
theorem Odd_pow {a : ℕ} (ha : Odd a) (n : ℕ) : Odd (a ^ n) := by {
  induction' n with x hx
  · use 0
    norm_num
  · rcases hx with ⟨k, hk⟩
    rcases ha with ⟨b, hb⟩
    use 2 * k * b + k + b
    have h1: a ^ (x + 1) = a ^ x * a := by rfl
    rw [h1, hk, hb]
    ring
}

-- 6.1.7.9.2 Example
theorem Nat.even_of_pow_even {a n : ℕ} (ha : Even (a ^ n)) : Even a := by {
  rcases ha with ⟨k, hk⟩
  have h0: k + k = 2 * k := by exact Eq.symm (Nat.two_mul k)
  rw [h0] at hk
  have h1: 2 ∣ a ^ n := by exact Dvd.intro k (id (Eq.symm hk))
  have prime_two: Prime 2 := by exact prime_two
  have h2: 2 ∣ a := by
    exact Prime.dvd_of_dvd_pow prime_two h1
  rcases h2 with ⟨b, hb⟩
  use b
  have h3: 2 * b = b + b := by exact Nat.two_mul b
  rw [← h3]
  exact hb
}
