/- # Tactics for Logical Connectives -/

import Mathlib
import Mathlib.Tactic

/- ## True -/

example : True := by
  apply True.intro

/- ## False -/

example : False → α := by
  intro contra
  cases contra

example : False → α :=
  False.elim

/- ## Implication, Forall -/

example : (A → B) → A → B := by
  intro hab ha
  apply hab
  exact ha

example : ∀ (hab : ∀ (a : A), B) (ha : A), B := by
  intro hab ha
  apply hab
  exact ha

example : (A → B → C) → A → B → C := by
  intro habc a b
  refine habc ?_ b
  exact a

example : (A → B → C) → A → B → C := by
  intro habc a b
  refine' habc _ b
  exact a

/- ## And -/

example : A ∧ B → B ∧ A := by
  intro h
  cases' h with a b
  constructor
  · exact b
  · exact a

example : A ∧ B → B ∧ A := by
  intro h
  match h with
  | ⟨a, b⟩ => constructor <;> assumption

example : A ∧ B → B ∧ A := by
  intro h
  cases h with
  | intro a b => constructor <;> assumption

example : A ∧ B → B ∧ A := by
  intro h
  have ⟨a, b⟩ := h
  constructor <;> assumption

example : A ∧ B → B ∧ A := by
  intro ⟨a, b⟩
  constructor <;> assumption

example : (A ∧ B) ∧ C → A ∧ (B ∧ C) := by
  intro ⟨x, c⟩
  have ⟨a, b⟩ := x
  (repeat' constructor) <;> assumption

example : (A ∧ B) ∧ C → A ∧ (B ∧ C) := by
  intro ⟨⟨a, b⟩, c⟩
  (repeat' constructor) <;> assumption

/- ## Or -/

example : A ∨ B → B ∨ A := by
  intro h
  cases' h with a b
  · right
    exact a
  · left
    exact b

example : A ∨ B → B ∨ A := by
  intro h
  match h with
  | .inl a => right; assumption
  | .inr b => left; assumption

example : A ∨ B → B ∨ A := by
  intro h
  cases h with
  | inl a => right; assumption
  | inr b => left; assumption

example : A ∨ B → B ∨ A := by
  rintro (a | b)
  · right; assumption
  · left; assumption

example : A ∨ B → B ∨ A := by
  intro h
  obtain (a | b) := h
  · right; assumption
  · left; assumption

example : A ∨ B → B ∨ A := by
  intro h
  rcases h with (a | b)
  · right; assumption
  · left; assumption

/- ## Exists, Sigma -/

example {P Q : α → Prop} : (∃ x, P x) → (∀ x, P x → Q x) → ∃ x, Q x := by
  intro ex hPQ
  cases' ex with x hP
  use x
  aesop

example {P Q : α → Prop} : (∃ x, P x) → (∀ x, P x → Q x) → ∃ x, Q x := by
  intro ⟨x, hP⟩ hPQ
  exists x
  aesop

example {P Q : α → Type} : (Σ x, P x) → (∀ x, P x → Q x) → Σ x, Q x := by
  intro ⟨x, hP⟩ hPQ
  exists x
  aesop

example {P Q : α → Type} : (Σ x, P x) → (∀ x, P x → Q x) → Σ x, Q x := by
  aesop
