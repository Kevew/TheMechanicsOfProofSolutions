import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith


def a : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | n + 2 => a (n + 1) + 2 * a n

-- 6.3.1 Example
example (n : ℕ) : a n = 2 ^ n + (-1) ^ n := by {
  induction n using Nat.twoStepInduction with
  | zero => {
    calc a 0
    _ = 2 := by rw [a]
  }
  | one => {
    simp only [pow_one, Int.reduceNeg, Int.reduceAdd]
    rw [a]
  }
  | more k h1 h2 => {
    calc a (k+2)
    _ = a (k+1) + 2 * (a k) := by rw [a]
    _ = (2 ^ (k+1) + (-1)^(k+1)) + 2 * (2^k + (-1)^k) := by {
      rw [h1, h2]
    }
    _ = (2 * 2 ^ (k) - (-1)^k) + (2 * 2 ^ k + 2 * (-1)^k) := by ring
    _ = 2 ^ 2 * 2 ^ k + (-1)^2 * (-1)^k := by ring
    _ = 2 ^ (k+2) + (-1)^(k+2) := by {
      ring
    }
  }
}

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

-- 6.3.6.1 Example
def b : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 5 * b (n + 1) - 6 * b n

example (n : ℕ) : b n = 3 ^ n - 2 ^ n := by {
  induction n using Nat.twoStepInduction with
  | zero => {
    ring_nf
    rw [b]
  }| one => {
    ring_nf
    rw [b]
  }| more k h1 h2 => {

    calc b (k + 2)
    _ = 5 * b (k + 1) - 6 * b k := by rw [b]
    _ = 5 * (3 ^ (k + 1) - 2 ^ (k + 1)) - 6 * (3 ^ k - 2 ^ k) := by rw [h1, h2]
    _ = 5 * (3 ^ (k + 1) - 2 ^ (k + 1)) - 2 * 3 ^ (k+1) + 3 * 2 ^ (k+1) := by ring
    _ = 3 ^ (k + 2) - 2 ^ (k + 2) := by {
      ring
    }
  }
}


-- 6.3.6.2 Example
def c : ℕ → ℤ
  | 0 => 3
  | 1 => 2
  | n + 2 => 4 * c n

example (n : ℕ) : c n = 2 * 2 ^ n + (-2) ^ n := by {
  induction n using Nat.twoStepInduction with
  | zero => {
    ring_nf
    rw [c]
  }| one => {
    ring_nf
    rw [c]
  }| more k h1 h2 => {
    calc c (k + 2)
    _ = 4 * c (k) := by rw [c]
    _ = 4 * (2 * 2 ^ k + (-2) ^ k) := by rw [h1]
    _ = 2 * 2 ^ (k + 2) + (-2) ^ (k + 2) := by ring
  }
}


-- 6.3.6.3 Example
def t : ℕ → ℤ
  | 0 => 5
  | 1 => 7
  | n + 2 => 2 * t (n + 1) - t n

example (n : ℕ) : t n = 2 * n + 5 := by {
  induction n using Nat.twoStepInduction with
  | zero => {
    ring_nf
    rw [t]
  }| one => {
    ring_nf
    rw [t]
  }| more k h1 h2 => {
    calc t (k + 2)
    _ = 2 * t (k + 1) - t k := by rw [t]
    _ = 2 * (2 * ↑(k + 1) + 5) - (2 * ↑k + 5) := by rw [h1, h2]
    _ = 2 * (2 * (↑k + ↑1) + 5) - (2 * ↑k + 5) := by norm_cast
    _ = 2 * (↑k + 2) + 5 := by ring
    _ = 2 * ↑(k + 2) + 5 := by norm_cast
  }
}


-- 6.3.6.4 Example
def q : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | n + 2 => 2 * q (n + 1) - q n + 6 * n + 6

example (n : ℕ) : q n = (n:ℤ) ^ 3 + 1 := by {
  induction n using Nat.twoStepInduction with
  | zero => {
    ring_nf
    rw [q]
  }| one => {
    ring_nf
    rw [q]
  }| more k h1 h2 => {
    calc q (k + 2)
    _ = 2 * q (k + 1) - q k + 6 * k + 6 := by rw [q]
    _ = 2 * (↑(k + 1) ^ 3 + 1) - (↑k ^ 3 + 1) + 6 * k + 6 := by rw [h1, h2]
    _ = 2 * ((↑k + 1) ^ 3 + 1) - (↑k ^ 3 + 1) + 6 * k + 6 := by norm_cast
    _ = 2 * (k^3 + 3 * k^2 + 3 * k + 1 + 1) - (↑k ^ 3 + 1) + 6 * k + 6 := by ring
    _ = k ^ 3 + 6 * k ^ 2 + 12 * k + 9 := by ring
    _ = (k + 2) ^ 3 + 1 := by ring
    _ = ↑(k + 2) ^ 3 + 1 := by norm_cast
  }
}


-- 6.3.6.5 Example
def s : ℕ → ℤ
  | 0 => 2
  | 1 => 3
  | n + 2 => 2 * s (n + 1) + 3 * s n

example (m : ℕ) : s m ≡ 2 [ZMOD 5] ∨ s m ≡ 3 [ZMOD 5] := by {
  have H: ∀ n : ℕ, (s n ≡ 2 [ZMOD 5] ∧ s (n + 1) ≡ 3 [ZMOD 5]) ∨
    (s (n + 1) ≡ 2 [ZMOD 5] ∧ s n ≡ 3 [ZMOD 5]) := by {
    intro n
    induction' n with k hk
    · left
      constructor
      rw [s]
      rw [s]
    · obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := hk
      · right
        constructor
        · rw [s]
          calc 2 * s (k + 1) + 3 * s k
          _ ≡ 2 * 3 + 3 * 2 [ZMOD 5] := by rel [h1, h2]
          _ ≡ 2 [ZMOD 5] := by rfl
        · exact h2
      · left
        constructor
        · exact h1
        · rw [s]
          calc 2 * s (k + 1) + 3 * s k
          _ ≡ 2 * 2 + 3 * 3 [ZMOD 5] := by rel [h1, h2]
  }
  obtain ⟨H1, H2⟩ | ⟨H1, H2⟩ := H m
  · left
    apply H1
  · right
    exact H2
}


-- 6.3.6.6 Example
-- Literally a repeat of the previous problem


-- 6.3.6.7 Example
def r : ℕ → ℤ
  | 0 => 2
  | 1 => 0
  | n + 2 => 2 * r (n + 1) + r n

example : forall_sufficiently_large n : ℕ, r n ≥ 2 ^ n := by {
  use 7
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n hk => {
    have h1: n = 7 ∨ n > 7 := by exact LE.le.eq_or_gt hn
    rcases h1 with h2 | h2
    · rw [h2, r]
      repeat rw [r]
      ring_nf
      norm_num
    · have p: n ≥ 8 := by exact h2
      have h1: n = 8 ∨ n > 8 := by exact LE.le.eq_or_gt p
      rcases h1 with h1 | h1
      · rw [h1]
        repeat rw [r]
        ring_nf
        norm_num
      have h6: n ≥ 2 := by linarith
      have temp: n < n + 2 := by linarith
      have h4 : n = (n - 2) + 2 := by exact (Nat.sub_eq_iff_eq_add h6).mp rfl
      have k1 := hk (n - 1) (Nat.sub_one_lt_of_lt hn) (Nat.le_sub_one_of_lt h2)
      have k2 := hk (n - 2) (Nat.sub_lt_right_of_lt_add h6 temp) (Nat.le_sub_of_add_le h1)
      rw [h4]
      rw [r]
      calc 2 * r (n - 2 + 1) + r (n - 2)
      _ = 2 * r (n - 1) + r (n - 2) := by {
        have h5 : n - 2 + 1 = n - 1 := by exact Eq.symm ((fun {m n} => Nat.pred_eq_succ_iff.mpr) h4)
        rw [h5]
      }
      _ ≥ 2 * (2 ^ (n - 1)) + 2 ^ (n - 2) := by rel [k1, k2]
      _ = 2 ^ (n - 1 + 1) + 2 ^ (n - 2) := by ring
      _ = 2 ^ (n - 2 + 2) + 2 ^ (n - 2) := by {
        have t1 : n - 1 + 1 = n - 2 + 2 := by exact Mathlib.Tactic.Ring.add_congr (congrFun (congrArg HSub.hSub h4) 1) rfl rfl
        rw [t1]
      }
      _ ≥ 2 ^ (n - 2 + 2) := by {
        have t1: 2 ^ (n - 2) ≥ 0 := by exact Nat.zero_le (2 ^ (n - 2))
        linarith
      }
  }
}

-- 6.3.6.8 Example
-- Same idea as Example 6.3.6.7. You just gotta use constructor and stuff like that
-- to split up the equations at the end before doing two calcs.
-- Not doing it rn cause my pc sorta lags from all that repeat rw [F]
