import Mathlib.Data.Real.Basic
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


-- 8.3.10.1 Example
inductive Humour
  | melancholic
  | choleric
  | phlegmatic
  | sanguine
  deriving DecidableEq

open Humour

def a : Humour → Humour
  | melancholic => sanguine
  | choleric => choleric
  | phlegmatic => phlegmatic
  | sanguine => melancholic

def b : Humour → Humour
  | melancholic => phlegmatic
  | choleric => phlegmatic
  | phlegmatic => melancholic
  | sanguine => sanguine

def c : Humour → Humour
  | melancholic => sanguine
  | choleric => phlegmatic
  | phlegmatic => melancholic
  | sanguine => phlegmatic

example : b ∘ a = c := by
  ext x
  cases x <;> rfl


-- 8.3.10.2 Example
def u (x : ℝ) : ℝ := 5 * x + 1

noncomputable def v (x : ℝ) : ℝ := (x - 1) / 5

example : Inverse u v := by
  constructor
  · ext x
    calc (v ∘ u) x = v (u x) := by rfl
    _ = v (5 * x + 1) := by rw [u]
    _ = ((5 * x + 1) - 1) / 5 := by rw [v]
    _ = x := by ring
  · ext x
    calc (u ∘ v) x = u (v x) := by rfl
    _ = u ((x - 1)/5) := by rw [v]
    _ = 5 * ((x - 1)/5) + 1 := by rw [u]
    _ = x := by ring


-- 8.3.10.3 Example
example {f : X → Y} (hf : Injective f) {g : Y → Z} (hg : Injective g) :
    Injective (g ∘ f) := by {
  intro x1 x2 h1
  apply hf
  apply hg
  exact h1
}


-- 8.3.10.4 Example
example {f : X → Y} (hf : Surjective f) {g : Y → Z} (hg : Surjective g) :
    Surjective (g ∘ f) := by
  intro x1
  specialize hg x1
  rcases hg with ⟨k, hk⟩
  specialize hf k
  rcases hf with ⟨s, hs⟩
  use s
  calc (g ∘ f) s = g (f s) := by rfl
  _ = x1 := by rw [hs, hk]


-- 8.3.10.5 Example
example {f : X → Y} (hf : Surjective f) : ∃ g : Y → X, f ∘ g = id := by
  dsimp [Surjective] at hf
  choose g hg using hf
  use g
  ext y
  calc (f ∘ g) y = f (g y) := by rfl
  _ = y := by exact hg y


-- 8.3.10.6 Example
example {f : X → Y} {g : Y → X} (h : Inverse f g) : Inverse g f := by {
  dsimp [Inverse] at *
  rcases h with ⟨h1, h2⟩
  constructor
  · exact h2
  · exact h1
}


-- 8.3.10.7 Example
example {f : X → Y} {g1 g2 : Y → X} (h1 : Inverse f g1) (h2 : Inverse f g2) :
    g1 = g2 := by {
  rcases h1 with ⟨hg1, hf1⟩
  rcases h2 with ⟨hg2, hf2⟩
  ext y
  have h2y : f (g2 y) = y := by
    simpa using congr_fun hf2 y
  have h1y : g1 (f (g2 y)) = g2 y := by
    simpa [Function.comp_apply] using congr_fun hg1 (g2 y)
  rw [h2y] at h1y
  exact h1y
}
