import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith

def Inverse (f : X → Y) (g : Y → X) : Prop := g ∘ f = id ∧ f ∘ g = id
def Injective (f : X → Y) : Prop := ∀ {x1 x2 : X}, f x1 = f x2 → x1 = x2
def Surjective (f : X → Y) : Prop := ∀ y : Y, ∃ x : X, f x = y
def Bijective (f : X → Y) : Prop := Injective f ∧ Surjective f

theorem exists_inverse_of_bijective {f : X → Y} (hf : Bijective f) :
    ∃ g : Y → X, Inverse f g := by
  dsimp [Bijective] at hf
  obtain ⟨h_inj, h_surj⟩ := hf
  dsimp [Surjective] at h_surj
  choose g hg using h_surj
  use g
  dsimp [Inverse]
  constructor
  · -- prove `g ∘ f = id`
    ext x
    dsimp [Injective] at h_inj
    apply h_inj
    calc f ((g ∘ f) x) = f (g (f x)) := by rfl
      _ = f x := by apply hg
      _ = f (id x) := by rfl
  · -- prove `f ∘ g = id`
    ext y
    apply hg

theorem bijective_of_inverse {f : X → Y} {g : Y → X} (h : Inverse f g) :
    Bijective f := by
  dsimp [Inverse] at h
  obtain ⟨hgf, hfg⟩ := h
  constructor
  · -- `f` is injective
    intro x1 x2 hx
    calc x1 = id x1 := by rfl
      _ = (g ∘ f) x1 := by rw [hgf]
      _ = g (f x1) := by rfl
      _ = g (f x2) := by rw [hx]
      _ = (g ∘ f) x2 := by rfl
      _ = id x2 := by rw [hgf]
      _ = x2 := by rfl
  · -- `f` is surjective
    intro y
    use g y
    calc f (g y) = (f ∘ g) y := by rfl
      _ = id y := by rw [hfg]
      _ = y := by rfl


theorem bijective_iff_exists_inverse (f : X → Y) :
    Bijective f ↔ ∃ g : Y → X, Inverse f g := by
  constructor
  · apply exists_inverse_of_bijective
  · intro h
    obtain ⟨g, H⟩ := h
    apply bijective_of_inverse H

-- 8.4.10.1 Example
example : Bijective (fun ((r, s) : ℚ × ℚ) ↦ (s, r - s)) := by
  rw [bijective_iff_exists_inverse]
  use (fun ((r, s) : ℚ × ℚ) ↦ (r + s, r))
  dsimp [Inverse]
  constructor
  · ext x
    · simp only [Function.comp_apply, add_sub_cancel, Prod.mk.eta, id_eq]
    · simp only [Function.comp_apply, add_sub_cancel, Prod.mk.eta, id_eq]
  · ext x
    · simp only [Function.comp_apply, add_sub_cancel_left, Prod.mk.eta, id_eq]
    · simp only [Function.comp_apply, add_sub_cancel_left, Prod.mk.eta, id_eq]

-- 8.4.10.2 Example
example : ¬ Injective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by{
  dsimp [Injective]
  push_neg
  use ⟨4, 2⟩
  use ⟨6, 3⟩
  constructor
  · simp only [Int.reduceMul, sub_self, zero_sub, Int.reduceNeg]
  · simp only [ne_eq, Prod.mk.injEq, OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, and_self,
    not_false_eq_true]
}

example : Surjective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by {
  intro y
  simp only [Prod.exists]
  use y + 1
  use 0
  ring
}


-- 8.4.10.3 Example
example : ¬ Surjective (fun ((x, y) : ℚ × ℚ) ↦ x ^ 2 + y ^ 2) := by {
  dsimp [Surjective]
  push_neg
  use -1
  intro x h1
  have : (x.1)^2 ≥ 0 := by {
    exact sq_nonneg x.1
  }
  have : (x.2)^2 ≥ 0 := by {
    exact sq_nonneg x.2
  }
  linarith
}


-- 8.4.10.4 Example
example : Surjective (fun ((x, y) : ℚ × ℚ) ↦ x ^ 2 - y ^ 2) := by {
  unfold Surjective
  intro y
  use ((1 + y) / 2, (1 - y) / 2)
  norm_num
  ring
}

-- 8.4.10.5 Example
example : Surjective (fun ((a, b) : ℚ × ℕ) ↦ a ^ b) := by {
  intro y
  simp only [Prod.exists]
  use y
  use 1
  ring
}


-- 8.4.10.6 Example
example : ¬ Injective
    (fun ((x, y, z) : ℝ × ℝ × ℝ) ↦ (x + y + z, x + 2 * y + 3 * z)) := by {
  dsimp [Injective]
  push_neg
  use ⟨1,-2,1⟩
  use ⟨0, 0, 0⟩
  constructor
  · simp only [mul_neg, mul_one, add_zero, mul_zero, Prod.mk_zero_zero, Prod.mk_eq_zero]
    constructor
    · ring
    · ring
  · simp only [Prod.mk_zero_zero, ne_eq, Prod.mk_eq_zero, one_ne_zero, neg_eq_zero,
    OfNat.ofNat_ne_zero, and_self, not_false_eq_true]
}


-- 8.4.10.7 Example
example : Injective (fun ((x, y) : ℝ × ℝ) ↦ (x + y, x + 2 * y, x + 3 * y)) := by {
  intro x1 x2
  simp only [Prod.mk.injEq, and_imp]
  intro h1 h2 h3
  have t1: x1.1 = x2.1 := by linarith
  have t2: x1.2 = x2.2 := by linarith
  exact Prod.ext t1 t2
}


-- 8.4.10.8 Example
def h : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ
  | (x, y, z) => (y, z, x)

example : h ∘ h ∘ h = id := by {
  funext x
  simp only [h, Function.comp_apply, id_eq]
}
