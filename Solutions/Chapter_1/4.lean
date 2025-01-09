import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith


-- 1.4.1 Example
example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by{
  calc
    y = y + 2 * x - 2 * x := by ring
    _ ≥ 3 - 2 * x := by rel [hy]
    _ = 9 - 2 * (x + 3) := by ring
    _ ≥ 9 - 2 * 2 := by rel [hx]
    _ = 5 := by ring
    _ > 3 := by simp
}

-- 1.4.2 Example
example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 :=
  calc
    r = (s + r + r - s) / 2 := by ring
    _ ≤ (3 + (s + 3) - s) / 2 := by rel [h1, h2]
    _ = 3 := by ring

-- 1.4.3 Example
example {x y : ℝ} (h1 : y ≤ x + 5) (h2 : x ≤ -2) : x + y < 2 := by{
  calc x + y
  _ ≤ x + (x + 5) := by rel [h1]
  _ = 2 * x + 5 := by ring
  _ ≤ 2 * -2 + 5 := by rel [h2]
  _ = 1 := by ring
  _ < 2 := by norm_num
}

-- 1.4.4 Example
example {u v x y A B : ℝ} (h1 : 0 < A) (h2 : A ≤ 1) (h3 : 1 ≤ B) (h4 : x ≤ B)
    (h5 : y ≤ B) (h6 : 0 ≤ u) (h7 : 0 ≤ v) (h8 : u < A) (h9 : v < A) :
    u * y + v * x + u * v < 3 * A * B :=
  calc
    u * y + v * x + u * v
      ≤ u * B + v * B + u * v := by rel [h5, h4]
    _ ≤ A * B + A * B + A * v := by rel [h8, h9]
    _ ≤ A * B + A * B + 1 * v := by rel [h2]
    _ ≤ A * B + A * B + B * v := by rel [h3]
    _ < A * B + A * B + B * A := by rel [h9]
    _ = 3 * A * B := by ring

-- 1.4.5 Example
example {t : ℚ} (ht : t ≥ 10) : t ^ 2 - 3 * t - 17 ≥ 5 :=
  calc
    t ^ 2 - 3 * t - 17
      = t * t - 3 * t - 17 := by ring
    _ ≥ 10 * t - 3 * t - 17 := by rel [ht]
    _ = 7 * t - 17 := by ring
    _ ≥ 7 * 10 - 17 := by rel [ht]
    _ = 53 := by ring
    _ ≥ 5 := by trivial

-- 1.4.6 Example
example {n : ℤ} (hn : n ≥ 5) : n ^ 2 > 2 * n + 11 :=
  calc n ^ 2
  _ = n * n := by ring
  _ ≥ 5 * n := by rel [hn]
  _ = 2 * n + 3 * n := by ring
  _ ≥ 2 * n + 3 * 5 := by rel [hn]
  _ = 2 * n + 11 + 4 := by ring
  _ > 2 * n + 11 := by norm_num

-- 1.4.7 Example
example {m n : ℤ} (h : m ^ 2 + n ≤ 2) : n ≤ 2 := by{
  have h1: m ^ 2 ≥ 0 := by exact sq_nonneg m
  calc n
    _ = 0 + n := by ring
    _ ≤ m ^ 2 + n := by rel [h1]
    _ ≤ 2 := by rel [h]
}

-- 1.4.8 Example
example {x y : ℝ} (h : x ^ 2 + y ^ 2 ≤ 1) : (x + y) ^ 2 < 3 := by{
  have h1: (x - y)^2 ≥ 0 := by exact sq_nonneg (x - y)
  calc (x + y) ^ 2
    _ = (x + y) ^ 2 + 0 := by ring
    _ ≤ (x + y) ^ 2 + (x - y) ^ 2 := by rel [h1]
    _ = 2 * (x ^ 2 + y ^ 2) := by ring
    _ ≤ 2 * 1 := by rel [h]
    _ = 2 := by ring
    _ < 3 := by linarith
}

-- 1.4.9 Example
example {a b : ℚ} (h1 : a ≥ 0) (h2 : b ≥ 0) (h3 : a + b ≤ 8) :
    3 * a * b + a ≤ 7 * b + 72 :=
  have h4: a ^ 2 ≥ 0 := by exact sq_nonneg (a)
  have h5: b ^ 2 ≥ 0 := by exact sq_nonneg (b)
  calc
    3 * a * b + a
    _ = 2 * 0 + 0 + (3 * a * b + a) := by ring
    _ ≤ 2 * b ^ 2 + a ^ 2 + (3 * a * b + a) := by rel [h4, h5]
    _ = 2 * ((a + b) * b) + (a + b) * a + a := by ring
    _ ≤ 2 * (8 * b) + 8 * a + a := by rel [h3]
    _ = 7 * b + 9 * (a + b) := by ring
    _ ≤ 7 * b + 9 * 8 := by rel [h3]
    _ = 7 * b + 72 := by ring

-- 1.4.11.1 Example
example {x y : ℤ} (h1 : x + 3 ≥ 2 * y) (h2 : 1 ≤ y) : x ≥ -1 := by {
  calc x
  _ = x + 3 - 3 := by ring
  _ ≥ 2 * y - 3 := by rel [h1]
  _ ≥ 2 * 1 - 3 := by rel [h2]
  _ = -1 := by ring
}

-- 1.4.11.2 Example
example {a b : ℚ} (h1 : 3 ≤ a) (h2 : a + 2 * b ≥ 4) : a + b ≥ 3 := by{
  calc a + b
  _ = (a + (a + 2 * b))/2 := by ring
  _ ≥ (3 + (a + 2 * b))/2 := by rel [h1]
  _ ≥ (3 + (4))/2 := by rel [h2]
  _ = 3.5 := by ring
  _ ≥ 3 := by norm_num
}

-- 1.4.11.3 Example
example {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 := by {
  calc x ^ 3 - 8 * x ^ 2 + 2 * x
  _ = x * x ^ 2 - 8 * x ^ 2 + 2 * x := by ring
  _ ≥ 9 * x ^ 2 - 8 * x ^ 2 + 2 * x := by rel [hx]
  _ = x * x + 2 * x := by ring
  _ ≥ 9 * 9 + 2 * 9 := by rel [hx]
  _ = 99 := by ring
  _ ≥ 3 := by norm_num
}

-- 1.4.11.4 Example
example {n : ℤ} (hn : n ≥ 10) : n ^ 4 - 2 * n ^ 2 > 3 * n ^ 3 := by{
  calc n ^ 4 - 2 * n ^ 2
  _ = n * n ^ 3 - 2 * n ^ 2 := by ring
  _ ≥ 10 * n ^ 3 - 2 * n ^ 2 := by rel [hn]
  _ = 3 * n ^ 3 + 7 * n * n ^ 2 - 2 * n ^ 2 := by ring
  _ ≥ 3 * n ^ 3 + 7 * 10 * n ^ 2 - 2 * n ^ 2 := by rel [hn]
  _ = 3 * n ^ 3 + 68 * n ^ 2 := by ring
  _ ≥ 3 * n ^ 3 + 68 * 10 ^ 2 := by rel [hn]
  _ = 3 * n ^ 3 + 6800 := by ring
  _ > 3 * n ^ 3 := by norm_num
}

-- 1.4.11.5 Example
example {n : ℤ} (h1 : n ≥ 5) : n ^ 2 - 2 * n + 3 > 14 := by{
  calc n ^ 2 - 2 * n + 3
  _ = n * n - 2 * n + 3 := by ring
  _ ≥ 5 * n - 2 * n + 3 := by rel [h1]
  _ = 3 * n + 3 := by ring
  _ ≥ 3 * 5 + 3 := by rel [h1]
  _ = 18 := by ring
  _ > 14 := by norm_num
}

-- 1.4.11.6 Example
example {x : ℚ} : x ^ 2 - 2 * x ≥ -1 := by{
  have h1: (x - 1) ^ 2 ≥ 0 := by exact sq_nonneg (x - 1)
  calc x ^ 2 - 2 * x
  _ = (x - 1) ^ 2 - 1 := by ring
  _ ≥ 0 - 1 := by rel [h1]
  _ = -1 := by ring
}

-- 1.4.11.7 Example
example (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b := by {
  have h1: (a - b) ^ 2 ≥ 0 := by exact sq_nonneg (a - b)
  calc a ^ 2 + b ^ 2
  _ = (a - b) ^ 2 + 2 * a * b := by ring
  _ ≥ 0 + 2 * a * b := by rel [h1]
  _ = 2 * a * b := by ring
}

-- Starting now, I'll use linarith more
