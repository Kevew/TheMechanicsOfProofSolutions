import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith

def Injective (f : X → Y) : Prop := ∀ {x1 x2 : X}, f x1 = f x2 → x1 = x2
def Surjective (f : X → Y) : Prop := ∀ y : Y, ∃ x : X, f x = y

-- 8.1.13.1 Example
example : Injective (fun (x : ℚ) ↦ x - 12) := by {
  dsimp [Injective]
  intro x1 x2 h1
  linarith
}


-- 8.1.13.2 Example
example : ¬ Injective (fun (x : ℝ) ↦ 3) := by {
  dsimp [Injective]
  push_neg
  use 1
  use 2
  constructor
  · rfl
  · exact OfNat.one_ne_ofNat 2
}


-- 8.1.13.3 Example
example : Injective (fun (x : ℚ) ↦ 3 * x - 1) := by
  dsimp [Injective]
  intro x1 x2 h1
  linarith


-- 8.1.13.4 Example
example : Injective (fun (x : ℤ) ↦ 3 * x - 1) := by
  dsimp [Injective]
  intro x1 x2 h1
  linarith


-- 8.1.13.5 Example
example : Surjective (fun (x : ℝ) ↦ 2 * x) := by {
  dsimp [Surjective]
  intro y
  use y/2
  ring
}


-- 8.1.13.6 Example
example : ¬ Surjective (fun (x : ℤ) ↦ 2 * x) := by{
  dsimp [Surjective]
  push_neg
  use 1
  intro n h
  have : (2 * n) % 2 = 0 := by simp only [Int.mul_emod_right]
  rw [h] at this
  norm_num at this
}


-- 8.1.13.7 Example
example : ¬ Surjective (fun (n : ℕ) ↦ n ^ 2) := by {
  dsimp [Surjective]
  push_neg
  use 2
  intro x
  match x with
  | 0 => {
    linarith
  }| 1 => {
    linarith
  }| k + 2 => {
    have h1: (k)^2 ≥ 0 := by exact sq_nonneg (k)
    have h2: (k + 2) ^ 2 > 2 := by {
      calc (k + 2) ^ 2
      _ = k ^ 2 + 4 * k + 4 := by ring
      _ > 2 := by linarith
    }
    intro h
    linarith
  }
}


-- 8.1.13.8 Example
inductive Musketeer
  | athos
  | porthos
  | aramis
  deriving DecidableEq

inductive White
  | meg
  | jack
  deriving DecidableEq

open White
open Musketeer

def h : Musketeer → White
  | athos => jack
  | porthos => meg
  | aramis => jack

example : ¬ Injective h := by
  dsimp [Injective]
  push_neg
  use athos, aramis
  constructor
  · repeat rw [h]
  · exact ne_of_beq_false rfl


-- 8.1.13.9 Example
example : Surjective h := by {
  dsimp [Surjective]
  intro y
  cases y
  · use porthos
    rw [h]
  · use athos
    rw [h]
}


-- 8.1.13.10 Example
def l : White → Musketeer
  | meg => aramis
  | jack => porthos

example : Injective l := by {
  dsimp [Injective]
  intro x1 x2 h1
  cases x1
  · cases x2
    · rw [l] at h1
    · rw [l] at h1
      rw [l] at h1
      contradiction
  · cases x2
    · rw [l] at h1
      rw [l] at h1
      contradiction
    · rw [l] at h1
}


-- 8.1.13.11 Example
example : ¬ Surjective l := by {
  dsimp [Surjective]
  push_neg
  use athos
  intro x
  cases x
  · rw [l]
    exact ne_of_beq_false rfl
  · rw [l]
    exact ne_of_beq_false rfl
}


-- 8.1.13.12 Example
example (f : X → Y) : Injective f ↔ ∀ x1 x2 : X, x1 ≠ x2 → f x1 ≠ f x2 := by {
  constructor
  dsimp [Injective]
  · intro a
    intro x1 x2 h1
    intro contra
    have h2: f x1 = f x2 → x1 = x2 := by exact fun a_1 => a contra
    apply h2 at contra
    contradiction
  · intro a
    dsimp [Injective]
    intro x1 x2 h1
    by_cases h2: x1 = x2
    · exact h2
    · push_neg at h2
      apply a at h2
      contradiction
}


-- 8.1.13.13 Example
example : ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + 1) := by {
  intro f h1
  dsimp [Injective] at *
  intro x1 x2 h2
  have h3: f x1 = f x2 := by linarith
  exact h1 (h1 (congrArg f h3))
}


-- 8.1.13.14 Example
example : ¬ ∀ (f : ℚ → ℚ), Injective f → Injective (fun x ↦ f x + x) := by {
  push_neg
  use (fun x => -x)
  dsimp [Injective]
  constructor
  · intro x1 x2 h1
    linarith
  · push_neg
    use 0, 2
    constructor
    · norm_num
    · linarith
}


-- 8.1.13.15 Example
example : ¬ ∀ (f : ℤ → ℤ), Surjective f → Surjective (fun x ↦ 2 * f x) := by
  push_neg
  use (fun x => x)
  dsimp [Surjective]
  constructor
  · intro y
    use y
  · push_neg
    use 1
    intro x
    intro p
    have : (2 * x) % 2 = 0 := by simp only [Int.mul_emod_right]
    rw [p] at this
    norm_num at this


-- 8.1.13.16 Example
example : ¬ ∀ c : ℝ, Surjective (fun x ↦ c * x) := by {
  push_neg
  use 0
  dsimp [Surjective]
  push_neg
  use 1
  intro x
  linarith
}


-- 8.1.13.17 Example
example {f : ℚ → ℚ} (hf : ∀ x y, x < y → f x < f y) : Injective f := by {
  intro x y
  have h1:= lt_trichotomy x y
  cases h1 with
  | inl h1 => {
    specialize hf x y h1
    intro contra
    linarith
  }| inr h1 => {
    rcases h1 with h2 | h2
    · intro a
      exact h2
    · intro a
      specialize hf y x h2
      linarith
  }
}


-- 8.3.13.18 Example
example {f : X → ℕ} {x0 : X} (h0 : f x0 = 0) {i : X → X}
    (hi : ∀ x, f (i x) = f x + 1) : Surjective f := by {
  intro y
  induction' y with k hk
  · use x0
  · rcases hk with ⟨p, hp⟩
    use i p
    specialize hi p
    rw [hi, hp]
}
