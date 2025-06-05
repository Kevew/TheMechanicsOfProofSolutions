import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Set

-- 9.2.8.6 Example
example : {n : ℤ | 5 ∣ n} ∩ {n : ℤ | 8 ∣ n} ⊆ {n : ℤ | 40 ∣ n} := by {
  dsimp [Set.subset_def]
  intro x h1
  rcases h1 with ⟨h1, h2⟩
  simp only [Set.mem_setOf_eq] at h1 h2
  omega
}
