/- # Tactics for Logical Connectives -/

import Mathlib.Tactic

/- ## Implication, Forall -/

example : (A → B) → A → B := by
  intro hab ha
  apply hab
  exact ha

example : (hab : ∀ (a : A), B) → A → B := by
  intro hab ha
  apply hab
  exact ha

/- ## True -/

example : True := by
  exact True.intro

/- ## False -/

example : False → α := by
  intro contra
  cases contra

/- ## And -/

example : A ∧ B → B ∧ A := by
  intro h
  cases h with
  | intro a b =>
    constructor
    · assumption
    · assumption

example : A ∧ B → B ∧ A := by
  intro h
  obtain ⟨a, b⟩ := h
  constructor <;> assumption

/- ## Or -/

example : A ∨ B → B ∨ A := by
  intro h
  cases h with
  | inl a => right; assumption
  | inr b => left; assumption

example : A ∨ B → B ∨ A := by
  intro h
  cases h
  case inl a =>
    right; exact a
  case inr b =>
    left; exact b

/- ## Exists, Sigma -/

example {P Q : α → Prop} : (∃ x, P x) → (∀ x, P x → Q x) → ∃ x, Q x := by
  intro ex hPQ
  obtain ⟨x, hx⟩ := ex
  use x
  aesop

example {P Q : α → Type} : (Σ x, P x) → (∀ x, P x → Q x) → Σ x, Q x := by
  intro sig hPQ
  obtain ⟨x, hx⟩ := sig
  use x
  aesop

example {P Q : α → Type} : (Σ x, P x) → (∀ x, P x → Q x) → Σ x, Q x := by
  aesop
