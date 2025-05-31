import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith

def Injective (f : X → Y) : Prop := ∀ {x1 x2 : X}, f x1 = f x2 → x1 = x2
def Surjective (f : X → Y) : Prop := ∀ y : Y, ∃ x : X, f x = y
def Bijective (f : X → Y) : Prop := Injective f ∧ Surjective f


-- 8.2.8.1 Example
example : Bijective (fun (x : ℝ) ↦ 4 - 3 * x) := by {
  constructor
  · dsimp [Injective]
    intro x1 x2 h1
    linarith
  · dsimp [Surjective]
    intro y
    use ((-y + 4)/3)
    ring
}


-- 8.2.8.2 Example
example : ¬ Bijective (fun (x : ℝ) ↦ x ^ 2 + 2 * x) := by {
  dsimp [Bijective, Injective]
  push_neg
  contrapose!
  intro h1
  use 0
  use -2
  constructor
  · ring
  · linarith
}


-- 8.2.8.3 Example
inductive Element
  | fire
  | water
  | earth
  | air
  deriving DecidableEq

open Element

def e : Element → Element
  | fire => earth
  | water => air
  | earth => fire
  | air => water

example : Bijective e := by {
  dsimp [Bijective]
  constructor
  · intro x1 x2 h1
    cases x1 <;> cases x2 <;> repeat rw [e] at h1 <;> contradiction
    -- Or you can do this, but u prob shouldn't
    /-
    match x1, x2 with
    | fire, earth => {
      rw [e] at h1
      rw [e] at h1
      contradiction
    }| fire, water => {
      rw [e] at h1
      rw [e] at h1
      contradiction
    }| fire, air => {
      rw [e] at h1
      rw [e] at h1
      contradiction
    }| water, earth => {
      rw [e] at h1
      rw [e] at h1
      contradiction
    }| water, air => {
      rw [e] at h1
      rw [e] at h1
      contradiction
    }| earth, air => {
      rw [e] at h1
      rw [e] at h1
      contradiction
    }| air, air => {
      rw [e] at h1
    }| water, water => {
      rw [e] at h1
    }| earth, earth => {
      rw [e] at h1
    }| fire, fire => {
      rw [e] at h1
    }-/
  · intro y
    cases y
    · use earth
      rw [e]
    · use air
      rw [e]
    · use fire
      rw [e]
    · use water
      rw [e]
}


-- 8.2.8.4 Example
inductive Subatomic
  | proton
  | neutron
  | electron
  deriving DecidableEq

open Subatomic

example : ∀ f : Subatomic → Subatomic, Injective f → Bijective f := by {
  intro f h1
  dsimp [Injective] at h1
  constructor
  · exact h1
  sorry
  -- You basically do what follows afterwards,
  -- Thereis like 27 cases, so quite a lot
  /-
  match h_p: f proton, h_n: f neutron, h_e: f electron with
  | electron, electron, electron => {
    have : electron = neutron := by {
      apply h1
      rw [h_e, h_n]
    }
    contradiction
  }| electron, electron, neutron => {
    have : proton = neutron := by {
      apply h1
      rw [h_p, h_n]
    }
    contradiction
  }| electron, electron, proton => {
    have : proton = neutron := by {
      apply h1
      rw [h_p, h_n]
    }
    contradiction
  }| electron, neutron, electron => {
    have : proton = electron := by {
      apply h1
      rw [h_e, h_p]
    }
    contradiction
  }| electron, neutron, neutron => {
    have : neutron = electron := by {
      apply h1
      rw [h_e, h_n]
    }
    contradiction
  }| electron, neutron, proton => {
    intro y
    cases y
    · use electron
    · use neutron
    · use proton
  }
  -/
}

-- 8.2.8.5 Example
-- The last question but even more cases to check...
-- Hell nah, i'm not doing all that
