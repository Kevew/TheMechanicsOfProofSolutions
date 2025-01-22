import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

-- 3.2.2 Example
example : (-2 : ℤ) ∣ 6 := by {
  dsimp [(· ∣ ·)]
  use -3
  norm_num
}

-- 3.2.4 Example
example {a b c : ℕ} (hab : a ∣ b) (hbc : b ^ 2 ∣ c) : a ^ 2 ∣ c := by {
  dsimp [(· ∣ ·)] at *
  rcases hab with ⟨e, he⟩
  rcases hbc with ⟨d, hd⟩
  rw [hd]
  rw [he]
  use e^2 * d
  ring
}

-- 3.2.5 Example
example {x y z : ℕ} (h : x * y ∣ z) : x ∣ z := by {
  rcases h with ⟨a, ha⟩
  rw [ha]
  use y * a
  ring
}

-- 3.2.8 Example
example {a b : ℕ} (hab : a ∣ b) (hb : 0 < b) : 0 < a := by {
  dsimp [(· ∣ ·)] at hab
  rcases hab with ⟨c, hc⟩
  have h2: 0 < a * c := by{
    calc 0
    _ < b := by rel [hb]
    _ = a * c := by rw [hc]
  }
  exact Nat.pos_of_mul_pos_right h2
}

-- 3.2.9.1 Example
example (t : ℤ) : t ∣ 0 := by {
  dsimp [(· ∣ ·)]
  use 0
  norm_num
}

-- 3.2.9.2 Example
example : ¬(3 : ℤ) ∣ -10 := by{
  dsimp [(· ∣ ·)]
  push_neg
  intro c
  intro b
  omega
}

-- 3.2.9.3 Example
example {x y : ℤ} (h : x ∣ y) : x ∣ 3 * y - 4 * y ^ 2 := by {
  dsimp [(· ∣ ·)] at *
  rcases h with ⟨c, hc⟩
  rw [hc]
  use (3 * c - 4 * (x * c ^ 2))
  ring
}

-- 3.2.9.4 Example
example {m n : ℤ} (h : m ∣ n) : m ∣ 2 * n ^ 3 + n := by {
  dsimp [(· ∣ ·)] at *
  rcases h with ⟨c, hc⟩
  rw [hc]
  use 2 * m ^ 2 * c ^ 3 + c
  ring
}

-- 3.2.9.5 Example
example {a b : ℤ} (hab : a ∣ b) : a ∣ 2 * b ^ 3 - b ^ 2 + 3 * b := by {
  dsimp [(· ∣ ·)] at *
  rcases hab with ⟨c, hc⟩
  rw [hc]
  use 2 * a ^ 2 * c ^ 3 - a * c ^ 2 + 3 * c
  ring
}

-- 3.2.9.6 Example
example {k l m : ℤ} (h1 : k ∣ l) (h2 : l ^ 3 ∣ m) : k ^ 3 ∣ m := by {
  dsimp [(· ∣ ·)] at *
  rcases h1 with ⟨c, hc⟩
  rcases h2 with ⟨d, hd⟩
  rw [hd, hc]
  use c^3 * d
  ring
}

-- 3.2.9.7 Example
example {p q r : ℤ} (hpq : p ^ 3 ∣ q) (hqr : q ^ 2 ∣ r) : p ^ 6 ∣ r := by {
  dsimp [(· ∣ ·)] at *
  rcases hpq with ⟨c, hc⟩
  rcases hqr with ⟨d, hd⟩
  rw [hd, hc]
  use c ^ 2 * d
  ring
}

-- 3.2.9.8 Example
example : ∃ n : ℕ, 0 < n ∧ 9 ∣ 2 ^ n - 1 := by {
  use 6
  apply And.intro
  norm_num
  norm_num
}

-- 3.2.9.9 Example
example : ∃ a b : ℤ, 0 < b ∧ b < a ∧ a - b ∣ a + b := by {
  use 2
  use 1
  constructor
  norm_num
  constructor
  norm_num
  norm_num
}
