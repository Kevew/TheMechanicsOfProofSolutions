import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

def Int.ModEq (n a b : ℤ) : Prop := n ∣ a - b

notation:50 a " ≡ " b " [ZMOD " n "]" => Int.ModEq n a b

-- 3.3.2 Example
example : -5 ≡ 1 [ZMOD 3] := by {
  use -2
  norm_num
}

theorem Int.ModEq.add {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a + c ≡ b + d [ZMOD n] := by
  dsimp [Int.ModEq] at *
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x + y
  calc
    a + c - (b + d) = a - b + (c - d) := by ring
    _ = n * x + n * y := by rw [hx, hy]
    _ = n * (x + y) := by ring


-- 3.3.4 Example
theorem Int.ModEq.sub {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a - c ≡ b - d [ZMOD n] := by {
  dsimp [Int.ModEq] at *
  rcases h1 with ⟨e, he⟩
  rcases h2 with ⟨f, hf⟩
  use e - f
  linarith
}

-- 3.3.5 Example
theorem Int.ModEq.neg {n a b : ℤ} (h1 : a ≡ b [ZMOD n]) : -a ≡ -b [ZMOD n] := by {
  rcases h1 with ⟨c, hc⟩
  use - c
  ring
  rw [← hc]
  ring
}


theorem Int.ModEq.mul {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a * c ≡ b * d [ZMOD n] := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x * c + b * y
  calc
    a * c - b * d = (a - b) * c + b * (c - d) := by ring
    _ = n * x * c + b * (n * y) := by rw [hx, hy]
    _ = n * (x * c + b * y) := by ring


theorem Int.ModEq.pow_two (h : a ≡ b [ZMOD n]) : a ^ 2 ≡ b ^ 2 [ZMOD n] := by
  obtain ⟨x, hx⟩ := h
  use x * (a + b)
  calc
    a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
    _ = n * x * (a + b) := by rw [hx]
    _ = n * (x * (a + b)) := by ring


-- 3.3.9 Example
theorem Int.ModEq.pow_three (h : a ≡ b [ZMOD n]) : a ^ 3 ≡ b ^ 3 [ZMOD n] := by {
  dsimp [Int.ModEq] at *
  rcases h with ⟨c, hc⟩
  use c * (a ^ 2 + a * b + b ^ 2)
  calc a ^ 3 - b ^ 3
  _ = (a - b) * (a ^ 2 + a * b + b ^ 2) := by ring
  _ = (n * c) * (a ^ 2 + a * b + b ^ 2) := by rw [hc]
  _ = n * (c * (a ^ 2 + a * b + b ^ 2)) := by exact Int.mul_assoc n c (a ^ 2 + a * b + b ^ 2)
}


theorem Int.ModEq.pow (k : ℕ) (h : a ≡ b [ZMOD n]) : a ^ k ≡ b ^ k [ZMOD n] :=
  sorry -- we'll prove this later in the book


theorem Int.ModEq.refl (a : ℤ) : a ≡ a [ZMOD n] := by
  use 0
  ring


-- 3.3.12.1 Example
example : 34 ≡ 104 [ZMOD 5] := by{
  use -14
  norm_num
}

-- 3.3.12.2 Example
theorem Int.ModEq.symm (h : a ≡ b [ZMOD n]) : b ≡ a [ZMOD n] := by {
  rcases h with ⟨c, hc⟩
  use -c
  linarith
}

-- 3.3.12.3 Example
theorem Int.ModEq.trans (h1 : a ≡ b [ZMOD n]) (h2 : b ≡ c [ZMOD n]) :
    a ≡ c [ZMOD n] := by {
  rcases h1 with ⟨d, hd⟩
  rcases h2 with ⟨e, he⟩
  use d + e
  calc a - c
  _ = (a - b) + (b - c) := by ring
  _ = (n * d) + (n * e) := by rw [← hd,← he]
  _ = n * (d + e) := by ring
}

-- 3.3.12.4 Example
example : a + n * c ≡ a [ZMOD n] := by {
  use c
  ring
}

-- 3.3.12.6 Example
example {a b : ℤ} (h : a ≡ b [ZMOD 5]) : 2 * a + 3 ≡ 2 * b + 3 [ZMOD 5] := by {
  apply Int.ModEq.add
  apply Int.ModEq.mul
  apply Int.ModEq.refl
  exact h
  apply Int.ModEq.refl
}

-- 3.3.12.7 Example
-- Literally the same proof lol
example {m n : ℤ} (h : m ≡ n [ZMOD 4]) : 3 * m - 1 ≡ 3 * n - 1 [ZMOD 4] := by {
  apply Int.ModEq.add
  apply Int.ModEq.mul
  apply Int.ModEq.refl
  exact h
  apply Int.ModEq.refl
}

-- 3.3.12.8 Example
example {k : ℤ} (hb : k ≡ 3 [ZMOD 5]) :
    4 * k + k ^ 3 + 3 ≡ 4 * 3 + 3 ^ 3 + 3 [ZMOD 5] := by{
  apply Int.ModEq.add
  apply Int.ModEq.add
  apply Int.ModEq.mul
  apply Int.ModEq.refl
  exact hb
  apply Int.ModEq.pow_three
  exact hb
  apply Int.ModEq.refl
}
