import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.intervalCases

def b : ℕ → ℤ
  | 0 => 3
  | n + 1 => b n ^ 2 - 2

-- 6.2.1 Example
example (n : ℕ) : Odd (b n) := by
  induction' n with k hk
  · -- base case
    use 1
    calc b 0 = 3 := by rw [b]
      _ = 2 * 1 + 1 := by norm_num
  · -- inductive step
    obtain ⟨x, hx⟩ := hk
    use 2 * x ^ 2 + 2 * x - 1
    calc b (k + 1) = b k ^ 2 - 2 := by rw [b]
      _ = (2 * x + 1) ^ 2 - 2 := by rw [hx]
      _ = 2 * (2 * x ^ 2 + 2 * x - 1) + 1 := by ring

-- 6.2.2 Example
def x : ℕ → ℤ
  | 0 => 5
  | n + 1 => 2 * x n - 1

example (n : ℕ) : x n ≡ 1 [ZMOD 4] := by
  induction' n with k IH
  · -- base case
    rw [x]
    rfl
  · -- inductive step
    simp [x]
    calc
      2 * x k - 1 ≡ 2 * 1 - 1 [ZMOD 4] := Int.ModEq.sub (Int.ModEq.mul_left 2 IH) rfl
      _ ≡ 1 [ZMOD 4] := by simp only [mul_one, Int.reduceSub, Int.ModEq.refl]

def A : ℕ → ℚ
  | 0 => 0
  | n + 1 => A n + (n + 1)
-- 6.2.5 Example
def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

notation:10000 n "!" => factorial n
example (n : ℕ) : ∀ d, 1 ≤ d → d ≤ n → d ∣ n ! := by
  induction' n with k IH
  · -- base case
    intro k hk1 hk
    interval_cases k
  · -- inductive step
    intro d hk1 hk
    obtain hk2 | hk2 : d = k + 1 ∨ d < k + 1 := eq_or_lt_of_le hk
    · -- case 1: `d = k + 1`
      have h: (k + 1) ! = d * k ! := by {
        exact
          Eq.symm
            ((fun {a b} => Nat.succ_inj'.mp)
              (congrArg Nat.succ (congrFun (congrArg HMul.hMul hk2) k !)))
      }
      rw [h]
      exact Nat.dvd_mul_right d k !
    · -- case 2: `d < k + 1`
      specialize IH d hk1 (Nat.le_of_lt_succ hk2)
      rcases IH with ⟨a, ha⟩
      have test: (k + 1) ! = d * (k + 1) * a := by{
        calc (k + 1)!
        _ = (k + 1) * k ! := rfl
        _ = (k + 1) * (d * a) := by rw [ha]
        _ = d * (k + 1) * a := by ring
      }
      use (k + 1) * a
      linarith

-- 6.2.6 Example
example (n : ℕ) : (n + 1)! ≥ 2 ^ n := by {
  induction' n with k hk
  · simp only [zero_add, pow_zero, ge_iff_le]
    exact Nat.le_of_ble_eq_true rfl
  · calc (k + 1 + 1)!
    _ = (k + 1 + 1) * (k + 1)! := rfl
    _ ≥ (k + 1 + 1) * (2 ^ k) := by exact Nat.mul_le_mul_left (k + 1 + 1) hk
    _ = k * 2 ^ k + 2 * 2 ^ k := by ring
    _ ≥ 2 * 2 ^ k := by exact Nat.le_add_left (2 * 2 ^ k) (k * 2 ^ k)
    _ = 2 ^ (k + 1) := by ring
}

-- 6.2.7.1 Example
def c : ℕ → ℤ
  | 0 => 7
  | n + 1 => 3 * c n - 10

example (n : ℕ) : Odd (c n) := by {
  induction' n with k hk
  · use 3
    rw [c]
    norm_num
  · rcases hk with ⟨a, ha⟩
    use 3 * a - 4
    rw [c, ha]
    ring
}

-- 6.2.7.2 Example
example (n : ℕ) : c n = 2 * 3 ^ n + 5 := by {
  induction' n with k hk
  · rw [c]
    ring
  · rw [c, hk]
    ring
}

-- 6.2.7.3 Example
def y : ℕ → ℕ
  | 0 => 2
  | n + 1 => (y n) ^ 2

example (n : ℕ) : y n = 2 ^ (2 ^ n) := by {
  induction' n with k hk
  · rw [y]
    ring
  · rw [y, hk]
    ring
}

-- 6.2.7.4 Example
def B : ℕ → ℚ
  | 0 => 0
  | n + 1 => B n + (n + 1 : ℚ) ^ 2

example (n : ℕ) : B n = n * (n + 1) * (2 * n + 1) / 6 := by {
  induction' n with k hk
  · rw [B]
    norm_num
  · rw [B, hk]
    push_cast
    ring
}

-- 6.2.7.5 Example
def S : ℕ → ℚ
  | 0 => 1
  | n + 1 => S n + 1 / 2 ^ (n + 1)

example (n : ℕ) : S n = 2 - 1 / 2 ^ n := by {
  induction' n with k hk
  · rw [S]
    ring
  · rw [S, hk]
    ring
}

-- 6.2.7.6 Example
example (n : ℕ) : 0 < n ! := by {
  induction' n with k hk
  · rw [factorial]
    norm_num
  · have h1: (k + 1)! = (k + 1) * k ! := rfl
    rw [h1]
    simp only [add_pos_iff, zero_lt_one, or_true, mul_pos_iff_of_pos_left, gt_iff_lt]
    exact hk
}

-- 6.2.7.7 Example
example {n : ℕ} (hn : 2 ≤ n) : Even (n !) := by
  induction n using Nat.strong_induction_on with
  | _ n ih => {
    have h1: n = 2 ∨ n > 2 := by exact LE.le.eq_or_gt hn
    rcases h1 with h2 | h2
    · rw [h2]
      exact Nat.even_iff.mpr rfl
    · have h1: n ! = n * (n - 1) ! := by {
        cases n with
        | zero => {
          simp only [zero_le, Nat.sub_eq_zero_of_le, zero_mul]
          contradiction
        }
        | succ n => {
          rfl
        }
      }
      rw [h1]
      have p1: n-1 < n := by exact Nat.sub_one_lt_of_lt hn
      have p2: 2 ≤ n - 1 := by exact Nat.le_sub_one_of_lt h2
      specialize ih (n - 1) p1 p2
      exact Even.mul_left ih n
  }

-- 6.2.7.8 Example
example (n : ℕ) : (n + 1) ! ≤ (n + 1) ^ n := by {
  induction' n with k hk
  · simp only [zero_add, pow_zero]
    repeat rw [factorial]
    norm_num
  · have h0: k + 1 ≤ k + 2 := by exact Nat.le_succ (k + 1)
    have h1: (k + 1) ^ k ≤ (k + 2) ^ k := by {
      exact Nat.pow_le_pow_of_le_left h0 k
    }
    calc (k + 1 + 1)!
    _ = (k + 1 + 1) * (k + 1)! := by rfl
    _ ≤ (k + 1 + 1) * (k + 1) ^ k := by rel [hk]
    _ ≤ (k + 1 + 1) * (k + 2) ^ k := by exact Nat.mul_le_mul_left (k + 1 + 1) h1
    _ = (k + 2) ^ (k + 1) := by exact Eq.symm Nat.pow_succ'
}
