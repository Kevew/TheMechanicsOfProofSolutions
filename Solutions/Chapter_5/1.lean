import Mathlib.Data.Real.Basic


-- 5.1.5 Example
example (P Q R : Prop) : (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R)) := by {
  constructor
  · intro h
    obtain ⟨h1, h2 | h2⟩ := h
    · left
      constructor
      · apply h1
      · apply h2
    · right
      constructor
      · apply h1
      · apply h2
  · intro h
    obtain ⟨h1, h2⟩ | ⟨h3, h4⟩  := h
    · constructor
      · exact h1
      · left
        exact h2
    · constructor
      · exact h3
      · right
        exact h4
}

-- 5.1.7.1 Example
example {P Q : Prop} (h : P ∧ Q) : P ∨ Q := by {
  left
  rcases h with ⟨h1, h2⟩
  exact h1
}

-- 5.1.7.2 Example
example {P Q R : Prop} (h1 : P → Q) (h2 : P → R) (h3 : P) : Q ∧ R := by {
  constructor
  · apply h1 at h3
    exact h3
  · apply h2 at h3
    exact h3
}

-- 5.1.7.3 Example
example (P : Prop) : ¬(P ∧ ¬ P) := by {
  intro P
  rcases P with ⟨h1, h2⟩
  contradiction
}

-- 5.1.7.4 Example
example {P Q : Prop} (h1 : P ↔ ¬ Q) (h2 : Q) : ¬ P := by {
  intro h
  apply h1.mp at h
  contradiction
}

-- 5.1.7.5 Example
example {P Q : Prop} (h1 : P ∨ Q) (h2 : Q → P) : P := by {
  cases h1 with
  | inl h1 => {
    exact h1
  }
  | inr h1 => {
    exact h2 h1
  }
}

-- 5.1.7.6 Example
example {P Q R : Prop} (h : P ↔ Q) : (P ∧ R) ↔ (Q ∧ R) := by {
  constructor
  · intro h1
    constructor
    · exact h.mp h1.left
    · exact h1.right
  · intro h1
    constructor
    · exact h.mpr h1.left
    · exact h1.right
}

-- 5.1.7.7 Example
example (P : Prop) : (P ∧ P) ↔ P := by {
  constructor
  · intro h
    exact h.left
  · intro h
    constructor
    · exact h
    · exact h
}

-- 5.1.7.8 Example
example (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) := by {
  constructor
  · intro h
    rcases h with h1 | h2
    · right
      exact h1
    · left
      exact h2
  · intro h
    rcases h with h1 | h2
    · right
      exact h1
    · left
      exact h2
}

-- 5.1.7.9 Example
example (P Q : Prop) : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by {
  exact not_or
}

-- 5.1.7.10 Example
example {P Q : α → Prop} (h1 : ∀ x, P x → Q x) (h2 : ∀ x, P x) : ∀ x, Q x := by {
  exact fun x => h1 x (h2 x)
}

-- 5.1.7.11 Example
example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by {
  constructor
  · intro h1
    exact (exists_congr h).mp h1
  · intro h1
    exact (exists_congr h).mpr h1
}

-- 5.1.7.12 Example
example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by {
  constructor
  · intro h
    rcases h with ⟨c, ⟨d, hc⟩⟩
    use d
    use c
  · intro h
    exact exists_comm.mp h
}

-- 5.1.7.13 Example
example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by {
  constructor
  · intro h
    exact fun y x => h x y
  · intro h
    exact fun x y => h y x
}

-- 5.1.7.14 Example
example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by {
  constructor
  · intro h
    rcases h with ⟨⟨c, hc⟩ , h2⟩
    use c
  · intro h
    rcases h with ⟨c, ⟨hc, h2⟩⟩
    constructor
    · use c
    · exact h2
}
