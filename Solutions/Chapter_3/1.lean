import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

-- 3.1.2 Example
example : Odd (-3 : ℤ) := by {
  dsimp [Odd]
  use -2
  norm_num
}

-- 3.1.4 Example
example {n : ℤ} (hn : Odd n) : Odd (7 * n - 4) := by {
  dsimp [Odd] at *
  rcases hn with ⟨k, hk⟩
  use 7 * k + 1
  rw [hk]
  ring
}

-- 3.1.6 Example
example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y + 2 * y) := by {
  dsimp [Odd] at *
  rcases hx with ⟨a, ha⟩
  rcases hy with ⟨b, hb⟩
  rw [ha, hb]
  use 2 * a * b + 3 * b + a + 1
  ring
}

-- 3.1.7 Example
example {m : ℤ} (hm : Odd m) : Even (3 * m - 5) := by {
  dsimp [Odd, Even] at *
  rcases hm with ⟨k, hk⟩
  rw [hk]
  use 3 * k - 1
  ring
}

-- 3.1.8 Example
example {n : ℤ} (hn : Even n) : Odd (n ^ 2 + 2 * n - 5) := by {
  dsimp [Odd, Even] at *
  rcases hn with ⟨r, hr⟩
  rw [hr]
  use 2 * r ^ 2 + 2 * r - 3
  ring
}

-- 3.1.10.1 Example
example : Odd (-9 : ℤ) := by {
  use -5
  ring
}

-- 3.1.10.2 Example
example : Even (26 : ℤ) := by
  use 13
  ring

-- 3.1.10.3 Example
example {m n : ℤ} (hm : Odd m) (hn : Even n) : Odd (n + m) := by {
  dsimp [Odd, Even] at *
  rcases hm with ⟨k, hk⟩
  rcases hn with ⟨r, hr⟩
  rw [hk, hr]
  use r + k
  ring
}

-- 3.1.10.4 Example
example {p q : ℤ} (hp : Odd p) (hq : Even q) : Odd (p - q - 4) := by {
  dsimp [Odd, Even] at *
  rcases hp with ⟨k, hk⟩
  rcases hq with ⟨r, hr⟩
  rw [hk, hr]
  use k - r - 2
  ring
}

-- 3.1.10.5 Example
example {a b : ℤ} (ha : Even a) (hb : Odd b) : Even (3 * a + b - 3) := by {
  dsimp [Odd, Even] at *
  rcases ha with ⟨k, hk⟩
  rcases hb with ⟨r, hr⟩
  rw [hk, hr]
  use 3 * k + r - 1
  ring
}

-- 3.1.10.6 Example
example {r s : ℤ} (hr : Odd r) (hs : Odd s) : Even (3 * r - 5 * s) := by {
  dsimp [Odd, Even] at *
  rcases hr with ⟨a, ha⟩
  rcases hs with ⟨b, hb⟩
  rw [ha, hb]
  use 3 * a - 5 * b - 1
  ring
}

-- 3.1.10.7 Example
example {x : ℤ} (hx : Odd x) : Odd (x ^ 3) := by {
  dsimp [Odd] at *
  rcases hx with ⟨k, hk⟩
  rw [hk]
  use 4 * k ^ 3 + 6 * k ^ 2 + 3 * k
  ring
}

-- 3.1.10.8 Example
example {n : ℤ} (hn : Odd n) : Even (n ^ 2 - 3 * n + 2) := by {
  dsimp [Odd, Even] at *
  rcases hn with ⟨k, hk⟩
  rw [hk]
  use 2 * k ^ 2 - k
  ring
}

-- 3.1.10.9 Example
example {a : ℤ} (ha : Odd a) : Odd (a ^ 2 + 2 * a - 4) := by {
  rcases ha with ⟨k, hk⟩
  rw [hk]
  use 2 * k ^ 2 + 4 * k - 1
  ring
}

-- 3.1.10.10 Example
example {p : ℤ} (hp : Odd p) : Odd (p ^ 2 + 3 * p - 5) := by {
  rcases hp with ⟨k, hk⟩
  rw [hk]
  use 2 * k ^ 2 + 5 * k - 1
  ring
}

-- 3.1.10.11 Example
example {x y : ℤ} (hx : Odd x) (hy : Odd y) : Odd (x * y) := by {
  dsimp [Odd, Even] at *
  rcases hx with ⟨a, ha⟩
  rcases hy with ⟨b, hb⟩
  rw [ha, hb]
  use 2 * a * b + a + b
  ring
}

-- 3.1.10.12 Example
example (n : ℤ) : Odd (3 * n ^ 2 + 3 * n - 1) := by {
  have h1: Even n ∨ Odd n := by apply Int.even_or_odd n
  rcases h1 with h2 | h3
  · dsimp [Odd, Even] at *
    rcases h2 with ⟨a, ha⟩
    rw [ha]
    use 6 * a ^ 2 + 3 * a - 1
    ring
  dsimp [Odd] at *
  rcases h3 with ⟨a, ha⟩
  rw [ha]
  use 6 * a ^ 2 + 9 * a + 2
  ring
}

-- 3.1.10.13 Example
example (n : ℤ) : ∃ m ≥ n, Odd m := by {
  have h1: Even n ∨ Odd n := by apply Int.even_or_odd n
  rcases h1 with h2 | h3
  · rcases h2 with ⟨k, hk⟩
    use n + 1
    constructor
    linarith
    rw [hk]
    use k
    ring
  rcases h3 with ⟨k, hk⟩
  use n + 2
  constructor
  linarith
  use k + 1
  rw [hk]
  ring
}

-- 3.1.10.14 Example
-- You can simplify what I wrote by replacing the use with stuff like the following:
-- exact Odd.sub_odd assump1 assump2 and the even version of it
example (a b c : ℤ) : Even (a - b) ∨ Even (a + c) ∨ Even (b - c) := by {
  have h1: Even a ∨ Odd a := by apply Int.even_or_odd a
  have h2: Even b ∨ Odd b := by apply Int.even_or_odd b
  have h3: Even c ∨ Odd c := by apply Int.even_or_odd c
  rcases h1 with h4 | h5
  rcases h2 with h6 | h7
  rcases h3 with h8 | h9
  · rcases h4 with ⟨k, hk⟩
    rcases h6 with ⟨r, hr⟩
    left
    rw [hk, hr]
    use k - r
    ring
  · rcases h4 with ⟨k, hk⟩
    rcases h6 with ⟨r, hr⟩
    left
    rw [hk, hr]
    use k - r
    ring
  · cases h3 with
    | inl h1 => {
      rcases h1 with ⟨k, hk⟩
      rcases h4 with ⟨r, hr⟩
      right
      left
      use k + r
      rw [hk, hr]
      linarith
    }
    | inr h1 => {
      right
      right
      exact Odd.sub_odd h7 h1
    }
  · cases h2 with
    | inl h1 => {
      cases h3 with
      | inl h2 => {
        rcases h1 with ⟨k, hk⟩
        rcases h2 with ⟨r, hr⟩
        right
        right
        use k - r
        rw [hk, hr]
        linarith
      }
      | inr h2 => {
        rcases h5 with ⟨k, hk⟩
        rcases h2 with ⟨r, hr⟩
        right
        left
        use k + r + 1
        rw [hk, hr]
        linarith
      }
    }
    | inr h1 => {
      cases h3 with
      | inl h2 => {
        rcases h5 with ⟨k, hk⟩
        rcases h1 with ⟨r, hr⟩
        left
        use k - r
        rw [hk, hr]
        linarith
      }
      | inr h2 => {
        rcases h5 with ⟨k, hk⟩
        rcases h1 with ⟨r, hr⟩
        left
        use k - r
        rw [hk, hr]
        linarith
      }
    }
}
