import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

-- 4.1.3 Example
example {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by {
  let x := (a + b)/2
  cases h x with
  | inl h1 => {
    calc a
    _ = 2 * a - a := by ring
    _ ≤ 2 * x - a := by rel [h1]
    _ = 2 * ((a + b)/2) - a := by rfl
    _ = b := by ring
  }
  | inr h1 => {
    calc a
    _ = 2 * ((a + b)/2) - b := by ring
    _ = 2 * x - b := by rfl
    _ ≤ 2 * b - b := by rel [h1]
    _ = b := by ring
  }
}

-- 4.1.4 Example
example {a b : ℝ} (ha1 : a ^ 2 ≤ 2) (hb1 : b ^ 2 ≤ 2) (ha2 : ∀ y, y ^ 2 ≤ 2 → y ≤ a)
    (hb2 : ∀ y, y ^ 2 ≤ 2 → y ≤ b) :
    a = b := by {
  apply le_antisymm
  · apply hb2
    apply ha1
  · apply ha2
    apply hb1
}

-- 4.1.6 Example
example : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by {
  use -3
  intro x y
  intro h1
  have h2: (x - y) ^ 2 ≥ 0 := by exact sq_nonneg (x - y)
  have h3: (x + y) ^ 2 ≤ 3 ^ 2 := by {
    calc (x + y) ^ 2
    _ ≤ (x + y) ^ 2 + (x - y)^2 := by linarith
    _ = 2 * (x^2 + y^2) := by ring
    _ ≤ 2 * (4) := by rel [h1]
    _ ≤ 3 ^ 2 := by norm_num
  }
  have : x + y ≥ - 3 ∧ x + y ≤ 3 := by {
    apply abs_le_of_sq_le_sq' h3
    norm_num
  }
  apply this.left
}

def Prime (p : ℕ) : Prop :=
  2 ≤ p ∧ ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p

-- 4.1.9 Example
example : ¬ Prime 6 := by
  dsimp [Prime]
  push_neg
  intro a
  use 2
  constructor
  use 3
  constructor
  norm_num
  norm_num


-- 4.1.10.1 Example
example {a : ℚ} (h : ∀ b : ℚ, a ≥ -3 + 4 * b - b ^ 2) : a ≥ 1 := by {
  let b_top : ℚ := 2
  have hb : -3 + 4 * b_top - b_top ^ 2 = 1 := by{
    ring
  }
  specialize h b_top
  rw [hb] at h
  exact h
}

-- 4.1.10.2 Example
example {n : ℤ} (hn : ∀ m, 1 ≤ m → m ≤ 5 → m ∣ n) : 15 ∣ n := by {
  have t1: 3 ∣ n := by{
    specialize hn 3
    apply hn
    norm_num
    norm_num
  }
  rcases t1 with ⟨c, hc⟩

  have t2: 5 ∣ n := by{
    specialize hn 5
    apply hn
    norm_num
    norm_num
  }
  rcases t2 with ⟨d, hd⟩

  have h1: 3 * c = 5 * d := by linarith
  have h2: 3 ∣ 5 * d := by exact Dvd.intro c h1
  have h3: 3 ∣ d := by omega

  rcases h3 with ⟨e, he⟩

  rw [hd, he]
  use e
  ring
}

-- 4.1.10.3 Example
example : ∃ n : ℕ, ∀ m : ℕ, n ≤ m := by {
  use 0
  intro m
  exact Nat.zero_le m
}

-- 4.1.10.4 Example
example : ∃ a : ℝ, ∀ b : ℝ, ∃ c : ℝ, a + b < c := by {
  use 5
  intro b
  use 6 + b
  norm_num
}

notation3 (prettyPrint := false) "forall_sufficiently_large "(...)", "r:(scoped P => ∃ C, ∀ x ≥ C, P x) => r

-- 4.1.10.5 Example
example : forall_sufficiently_large x : ℝ, x ^ 3 + 3 * x ≥ 7 * x ^ 2 + 12 := by {
  use 10
  intro x x1
  calc x ^ 3 + 3 * x
  _ = x * x ^ 2 + 3 * x := by ring
  _ ≥ 10 * x ^ 2 + 3 * x := by rel [x1]
  _ = 7 * x ^ 2 + 3 * x ^ 2 + 3 * x := by ring
  _ ≥ 7 * x ^ 2 + 3 * 10 ^ 2 + 3 * 10 := by rel [x1]
  _ = 7 * x ^ 2 + 330 := by ring
  _ ≥ 7 * x ^ 2 + 12 := by norm_num
}

-- 4.1.10.6 Example
example : ¬(Prime 45) := by {
  dsimp [Prime]
  push_neg
  intro a
  use 3
  constructor
  use 15
  constructor
  norm_num
  norm_num
}
