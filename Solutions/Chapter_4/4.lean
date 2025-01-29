import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

def Prime (p : ℕ) : Prop :=
  2 ≤ p ∧ ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p

-- 4.4.4 Example
example {p : ℕ} (hp : 2 ≤ p) (H : ∀ m : ℕ, 1 < m → m < p → ¬m ∣ p) : Prime p := by {
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

-- 4.4.5 Example
example {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_pyth : a ^ 2 + b ^ 2 = c ^ 2) : 3 ≤ a := by {
  have ha: a ≤ 2 ∨ 3 ≤ a := by omega
  rcases ha with ha1 | ha2
  have h1: b ≤ 1 ∨ 2 ≤ b := by omega
  rcases h1 with h2 | h3
  have h: c ^ 2 < 3 ^ 2 := by {
    calc c ^ 2
    _ = a ^ 2 + b ^ 2 := by rw [h_pyth]
    _ ≤ 2 ^ 2 + 1 ^ 2 := by rel [ha1, h2]
    _ < 3 ^ 2 := by norm_num
  }
  have h1 : c < 3 := by exact lt_of_pow_lt_pow_left' 2 h
  have haa: a = 1 ∨ a = 2:= by omega
  have hbb: b = 1 := by omega
  have hcc: c = 1 ∨ c = 2 := by omega
  rcases haa with haa1 | haa2
  rcases hcc with hcc1 | hcc2
  rw [haa1, hbb, hcc1] at h_pyth
  tauto
  rw [haa1, hbb, hcc2] at h_pyth
  tauto
  rcases hcc with hcc1 | hcc2
  rw [haa2, hbb, hcc1] at h_pyth
  tauto
  rw [haa2, hbb, hcc2] at h_pyth
  tauto
  have h1 : b ^ 2 < c ^ 2 := by {
    have : a ^ 2 > 0 := by exact Nat.pos_pow_of_pos 2 ha
    calc b ^ 2
    _ < a ^ 2 + b ^ 2 := by linarith
    _ = c ^ 2 := by rw [h_pyth]
  }
  have h2 : b < c := by exact lt_of_pow_lt_pow_left' 2 h1
  have h5 : b + 1 ≤ c := by exact lt_of_pow_lt_pow_left' 2 h1
  have h4 : c ^ 2 < (b + 1) ^ 2 := by {
    have temp: a ^ 2 ≤ 2 ^ 2 := by exact Nat.pow_le_pow_of_le_left ha1 2
    calc c ^ 2
    _ = a ^ 2 + b ^ 2 := by rw [h_pyth]
    _ ≤ 2 ^ 2 + b ^ 2 := by rel [temp]
    _ = 2 * 2 + b ^ 2 := by ring
    _ ≤ 2 * b + b ^ 2 := by rel [h3]
    _ < b ^ 2 + 2 * b + 1 := by linarith
    _ = (b + 1) ^ 2 := by ring
  }
  have contra_dict: c < (b + 1) := by exact lt_of_pow_lt_pow_left' 2 h4
  linarith
  exact ha2
}

-- 4.4.6.1 Exercises
example {x y : ℝ} (n : ℕ) (hx : 0 ≤ x) (hn : 0 < n) (h : y ^ n ≤ x ^ n) :
    y ≤ x := by {
  cases' le_total y 0 with h1 h1
  exact Preorder.le_trans y 0 x h1 hx

  have c: y ^ n = x ^ n ∨ y ^ n < x ^ n := by {
    exact Decidable.eq_or_lt_of_le h
  }
  rcases c with c1 | c2

  have h2: x = y := by {
    have h3: n ≠ 0 := by omega
    apply (pow_left_inj₀ hx h1 h3).mp
    exact id (Eq.symm c1)
  }
  rw [h2]
  have h2: y < x := by {
    exact lt_of_pow_lt_pow_left₀ n hx c2
  }
  linarith
}


def Int.ModEq (n a b : ℤ) : Prop := n ∣ a - b

notation:50 a " ≡ " b " [ZMOD " n "]" => Int.ModEq n a b

-- 4.4.6.2 Example
example (n : ℤ) (hn : n ^ 2 ≡ 4 [ZMOD 5]) : n ≡ 2 [ZMOD 5] ∨ n ≡ 3 [ZMOD 5] := by {
    dsimp [Int.ModEq] at *
    rcases hn with ⟨c, hc⟩
    have h : 5 ∣ (n + 2) * (n - 2):= by {
        use c
        linarith
    }
    have h1 : 5 ∣ (n + 2) ∨ 5 ∣ (n - 2) := by {
        have h2: 5 ∣ (n + 2) ∨ ¬(5 ∣ (n + 2)) := by omega
        cases h2 with
        | inl h3 => {
            left
            exact h3
        }
        | inr h3 => {
            -- Not sure how to finish, I have 5 ∣ (n + 2) * (n - 2)
            -- and we know 5 does not divide (n + 2), then it must divide (n - 2)
            -- hmm, not sure how to write that in lean though.
            have h4 : 5 ∣ n - 2 := by{
                sorry
            }
            right
            exact h4
        }
    }
    rcases h1 with h2 | h3
    right
    omega
    left
    omega
}

-- 4.4.6.3 Example
example : Prime 7 := by {
    constructor
    norm_num
    intro m hm
    have h1 : 7 ≥ m := by sorry
    interval_cases m <;> norm_num
    aesop
    tauto
    tauto
    tauto
    tauto
    tauto
}

-- 4.4.6.4 Example
example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by {
  have h3 :=
    calc
      (x + 2) * (x - 2) = x ^ 2 + 2 * x - 2 * x - 4 := by ring
      _ = 0 := by linarith
  rw [mul_eq_zero] at h3
  rcases h3 with h4 | h5
  linarith
  linarith
}

-- 4.4.6.5 Example
example (p : ℕ) (h : Prime p) : p = 2 ∨ Odd p := by {
  by_cases h2 : p = 2
  · left
    exact h2
  · right
    push_neg at h2
    rcases h with ⟨h3, h4⟩
    have h5: 2 < p := by exact Nat.lt_of_le_of_ne h3 fun a => h2 (id (Eq.symm a))
    apply by_contradiction
    intro h
    simp at h
    rcases h with ⟨c, hc⟩
    have h1 : 2 ∣ p := by omega
    have h6 : 2 = 1 ∨ 2 = p := by{
      exact h4 2 h1
    }
    have h7: 2 = p := by {
      cases h6 with
      | inl h => {
        linarith
      }
      | inr h => {
        exact h
      }
    }
    linarith
}
