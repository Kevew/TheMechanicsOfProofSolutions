-- 5.3.1 Example
example (P Q : Prop) : ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q) := by {
  constructor
  · intro h
    by_cases hP : P
    · right
      intro hQ
      have hPQ : P ∧ Q := by {
      · constructor
        · apply hP
        · apply hQ
      }
      contradiction
    · left
      apply hP
  · intro h
    by_cases hP : Q
    intro h1
    · rcases h with h2 | h3
      have h3: P := by exact h1.left
      contradiction
      contradiction
    intro h1
    · rcases h with h2 | h3
      have h3: P := by exact h1.left
      contradiction
      have h4: Q := by exact h1.right
      contradiction
}
