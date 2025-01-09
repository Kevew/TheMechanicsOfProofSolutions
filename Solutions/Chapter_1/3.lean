import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

-- 1.3.1 Example
example {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 := by{
  calc a
  _ = 2 * b + 5 := by rw [h1]
  _ = 2 * 3 + 5 := by rw [h2]
  _ = 11 := by ring
}

-- 1.3.2 Example
example {x : ℤ} (h1: x + 4 = 2) : x = -2 := by{
  calc x
  _ = (x + 4) - 4 := by ring
  _ = 2 - 4 := by rw [h1]
  _ = -2 := by ring
}

-- 1.3.3 Example
example {a b : ℝ} (h1: a - 5 * b = 4) (h2: b + 2 = 3) : a = 9 := by{
  calc a
  _ = a - 5 * b + 5 * b := by ring
  _ = 4 + 5 * b := by rw [h1]
  _ = -6 + 5 * (b + 2) := by ring
  _ = -6 + 5 * 3 := by rw [h2]
  _ = 9 := by ring
}

-- 1.3.4 Example
example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 := by{
  calc w
  _ = (3 * w + 1)/3 - 1/3 := by ring
  _ = 4/3 - 1/3 := by rw [h1]
  _ = 1 := by ring
}

-- 1.3.5 Example
example {x : ℤ} (h1 : 2 * x + 3 = x) : x = -3 := by{
  calc x
  _ = 2 * x + 3 - x - 3 := by ring
  _ = x - x - 3 := by rw [h1]
  _ = -3 := by ring
}

-- 1.3.6 Example
example {x y : ℤ} (h1 : 2 * x - y = 4) (h2 : y - x + 1 = 2) : x = 5 := by{
  calc x
  _ = 2 * x - y + y - x := by ring
  _ = 4 + y - x := by rw [h1]
  _ = y - x + 1 + 3 := by ring
  _ = 2 + 3 := by rw [h2]
  _ = 5 := by ring
}

-- 1.3.7 Example
example {u v : ℚ} (h1 : u + 2 * v = 4) (h2 : u - 2 * v = 6) : u = 5 := by{
  calc u
  _ = (u + 2 * v + (u - 2 * v))/2 := by ring
  _ = (4 + 6)/2 := by rw [h1, h2]
  _ = 5 := by ring
}

-- 1.3.8 Example
example {x y : ℝ} (h1 : x + y = 4) (h2 : 5 * x - 3 * y = 4) : x = 2 := by{
  calc x
  _ = (5 * x - 3 * y + 3 * x + 3 * y)/8 := by ring
  _ = (4 + 3 * x + 3 * y)/8 := by rw [h2]
  _ = (4 + 3 * (x + y))/8 := by ring
  _ = (4 + 3 * (4))/8 := by rw [h1]
  _ = 2 := by ring
}

-- 1.3.9 Example
example {a b : ℚ} (h1 : a - 3 = 2 * b) : a ^ 2 - a + 3 = 4 * b ^ 2 + 10 * b + 9 := by{
  calc a ^ 2 - a + 3
  _ = (a - 3)^2 + 5 * (a - 3) + 9 := by ring
  _ = (2 * b)^2 + 5 * (2 * b) + 9 := by rw [h1]
  _ = 4 * b ^ 2 + 10 * b + 9 := by ring
}

-- 1.3.10 Example
example {z : ℝ} (h1 : z ^ 2 - 2 = 0) : z ^ 4 - z ^ 3 - z ^ 2 + 2 * z + 1 = 3 := by{
  calc z ^ 4 - z ^ 3 - z ^ 2 + 2 * z + 1
  _ = (z ^ 2 - z + 1) * (z ^ 2 - 2) + 3 := by ring
  _ = (z ^ 2 - z + 1) * (0) + 3 := by rw [h1]
  _ = 3 := by ring
}

-- Examples ofr 1.3.11
-- 1.3.11.1 Example
example {x y : ℝ} (h1 : x = 3) (h2 : y = 4 * x - 3) : y = 9 := by {
  calc y
  _ = 4 * 3 - 3 := by rw [h2, h1]
  _ = 9 := by ring
}

-- 1.3.11.2 Example
example {a b : ℤ} (h : a - b = 0) : a = b := by{
  calc a
  _ = a - b + b := by ring
  _ = 0 + b := by rw [h]
  _ = b := by ring
}

-- 1.3.11.3 Example
example {x y : ℤ} (h1 : x - 3 * y = 5) (h2 : y = 3) : x = 14 := by{
  calc x
  _ = x - 3 * y + 3 * y := by ring
  _ = 5 + 3 * 3 := by rw [h1, h2]
  _ = 14 := by ring
}

-- 1.3.11.4 Example
example {p q : ℚ} (h1 : p - 2 * q = 1) (h2 : q = -1) : p = -1 := by{
  calc p
  _ = p - 2 * q + 2 * q := by ring
  _ = 1 + 2 * (-1) := by rw [h1, h2]
  _= -1 := by ring
}

-- 1.3.11.5 Example
example {x y : ℚ} (h1 : y + 1 = 3) (h2 : x + 2 * y = 3) : x = -1 := by{
  calc x
  _ = x + 2 * y - 2 * y := by ring
  _ = 3 - 2 * y := by rw [h2]
  _ = 5 - 2 * (y + 1) := by ring
  _ = 5 - 2 * (3) := by rw [h1]
  _ = -1 := by ring
}

-- 1.3.11.6 Example
example {p q : ℤ} (h1 : p + 4 * q = 1) (h2 : q - 1 = 2) : p = -11 := by{
  calc p
  _ = p + 4 * q - 4 * q := by ring
  _ = 1 - 4 * q := by rw [h1]
  _ = -3 - 4 * (q - 1) := by ring
  _ = -3 - 4 * 2 := by rw [h2]
  _ = -11 := by ring
}

-- 1.3.11.7 Example
example {a b c : ℝ} (h1 : a + 2 * b + 3 * c = 7) (h2 : b + 2 * c = 3)
    (h3 : c = 1) : a = 2 := by{
  calc a
  _ = a + 2 * b + 3 * c - 2 * b - 4 * c + c := by ring
  _ = 7 - 2 * b - 4 * c + c := by rw [h1]
  _ = 7 - 2 * (b + 2 * c) + c := by ring
  _ = 7 - 2 * (3) + 1 := by rw [h2,h3]
  _ = 2 := by ring
}

-- 1.3.11.8 Example
example {u v : ℚ} (h1 : 4 * u + v = 3) (h2 : v = 2) : u = 1 / 4 := by{
  calc u
  _ = (4 * u + v - v)/4 := by ring
  _ = (3 - 2)/4 := by rw [h1, h2]
  _ = 1/4 := by ring
}

-- 1.3.11.9 Example
example {c : ℚ} (h1 : 4 * c + 1 = 3 * c - 2) : c = -3 := by{
  calc c
  _ = 4 * c + 1 - 3 * c - 2 + 1:= by ring
  _ = 3 * c - 2 - 3 * c - 2 + 1 := by rw [h1]
  _ = -3 := by ring
}

-- 1.3.11.10 Example
example {p : ℝ} (h1 : 5 * p - 3 = 3 * p + 1) : p = 2 := by{
  calc p
  _ = (5 * p - 3 - 3 * p + 1 + 2)/2 := by ring
  _ = (3 * p + 1 - 3 * p + 1 + 2)/2 := by rw [h1]
  _ = 2 := by ring
}

-- 1.3.11.11 Example
example {x y : ℤ} (h1 : 2 * x + y = 4) (h2 : x + y = 1) : x = 3 := by {
  calc x
  _ = 2 * x + y - (x + y) := by ring
  _ = 4 - 1 := by rw [h1, h2]
  _ = 3 := by ring
}

-- 1.3.11.12 Example
example {a b : ℝ} (h1 : a + 2 * b = 4) (h2 : a - b = 1) : a = 2 := by{
  calc a
  _ = (a + 2 * b + 2 * (a - b))/3 := by ring
  _ = (4 + 2 * (1))/3 := by rw [h1, h2]
  _ = 2 := by ring
}

-- 1.3.11.13 Example
example {u v : ℝ} (h1 : u + 1 = v) : u ^ 2 + 3 * u + 1 = v ^ 2 + v - 1 := by {
  calc u ^ 2 + 3 * u + 1
  _ = (u + 1) ^ 2 + (u + 1) - 1 := by ring
  _ = (v) ^ 2 + v - 1 := by rw [h1]
}

-- 1.3.11.14 Example
example {t : ℚ} (ht : t ^ 2 - 4 = 0) :
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = 10 * t + 2 := by{
  calc t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2
  _ = (t ^ 2 - 4) * (t ^ 2 + 3 * t + 1) + 10 * t + 2 := by ring
  _ = (0) * (t ^ 2 + 3 * t + 1) + 10 * t + 2 := by rw [ht]
  _ = 10 * t + 2 := by ring
}

-- 1.3.11.15 Example
example {x y : ℝ} (h1 : x + 3 = 5) (h2 : 2 * x - y * x = 0) : y = 2 := by {
  have hx : x = 2 := by {
    calc x
      _ = x + 3 - 3 := by ring
      _ = 5 - 3 := by rw [h1]
      _ = 2 := by ring
  }

  rw [hx] at h2

  calc y
  _ = ((2 * 2 - y * 2) - 4)/(-2) := by ring
  _ = ((0) - 4)/(-2) := by rw [h2]
  _ = 2 := by ring
}

-- 1.3.11.16 Example
example {p q r : ℚ} (h1 : p + q + r = 0) (h2 : p * q + p * r + q * r = 2) :
    p ^ 2 + q ^ 2 + r ^ 2 = -4 := by{
  calc p ^ 2 + q ^ 2 + r ^ 2
    _ = (p + q + r) ^ 2 - 2 * (p * q + p * r + q * r) := by ring
    _ = 0 ^ 2 - 2 * (p * q + p * r + q * r) := by rw [h1]
    _ = 0 ^ 2 - 2 * 2 := by rw [h2]
    _ = -4 := by ring

}
