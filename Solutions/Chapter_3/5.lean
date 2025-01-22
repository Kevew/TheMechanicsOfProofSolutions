import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

-- 3.5.1 Example
example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by {
  dsimp [(· ∣ ·)] at *
  rcases hn with ⟨c, hc⟩
  use 5 * c - 3 * n
  calc n
  _ = 5 * (5 * n) - 24 * n := by ring
  _ = 5 * (8 * c) - 24 * n := by rw [hc]
  _ = 8 * (5 * c - 3 * n) := by ring
}

-- 3.5.2 Example
example {n : ℤ} (h1 : 5 ∣ 3 * n) : 5 ∣ n := by {
  dsimp [(· ∣ ·)] at *
  rcases h1 with ⟨c, hc⟩
  use 2 * c - n
  calc n
  _ = 2 * (3 * n) - 5 * n := by ring
  _ = 2 * (5 * c) - 5 * n := by rw [hc]
  _ = 5 * (2 * c - n) := by ring
}

-- 3.5.4.1 Example
example {n : ℤ} (hn : 6 ∣ 11 * n) : 6 ∣ n := by {
  dsimp [(· ∣ ·)] at *
  rcases hn with ⟨c, hc⟩
  use 2 * n - c
  calc n
  _ = 12 * n - 11 * n := by ring
  _ = 12 * n - 6 * c := by rw [hc]
  _ = 6 * (2 * n - c) := by ring
}

-- 3.5.4.2 Example
example {a : ℤ} (ha : 7 ∣ 5 * a) : 7 ∣ a := by {
  dsimp [(· ∣ ·)] at *
  rcases ha with ⟨c, hc⟩
  use 3 * c - 2 * a
  calc a
  _ = 3 * (5 * a) - 14 * a := by ring
  _ = 3 * (7 * c) - 14 * a := by rw [hc]
  _ = 7 * (3 * c - 2 * a) := by ring
}

-- 3.5.4.3 Example
example {n : ℤ} (h1 : 7 ∣ n) (h2 : 9 ∣ n) : 63 ∣ n := by {
  dsimp [(· ∣ ·)] at *
  rcases h1 with ⟨e, he⟩
  rcases h2 with ⟨d, hd⟩

  have h3: 7 * e = 9 * d := by linarith
  have h4: 7 ∣ 9 * d := by exact Dvd.intro e h3
  have h5: 7 ∣ d := by omega -- You could also just omega the whole proof

  rcases h5 with ⟨c, hc⟩

  rw [hd, hc]
  use c
  ring
}

-- 3.5.4.4 Example
example {n : ℤ} (h1 : 5 ∣ n) (h2 : 13 ∣ n) : 65 ∣ n := by {
  dsimp [(· ∣ ·)] at *
  rcases h1 with ⟨e, he⟩
  rcases h2 with ⟨d, hd⟩

  have h3: 5 * e = 13 * d := by linarith
  have h4: 5 ∣ 13 * d := by exact Dvd.intro e h3
  have h5: 5 ∣ d := by omega -- You could also just omega the whole proof

  rcases h5 with ⟨c, hc⟩

  rw [hd, hc]
  use c
  ring
}
