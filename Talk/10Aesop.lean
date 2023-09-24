/-# Aesop: Auto-Style Proof Search -/

import Aesop

example : (A → B ∨ A → C) → (B ∨ C → D) → (B ∨ C → E) → A → D ∧ E := by
  aesop

theorem ne_nil_of_mem {a : α} {l : List α} (h : a ∈ l) : l ≠ [] := by
  aesop

theorem not_mem_cons_of_ne_of_not_mem {a y : α} {l : List α} :
    a ≠ y → a ∉ l → a ∉ y::l := by
  aesop

@[simp] theorem mem_map {f : α → β} {b : β} {l : List α} :
    b ∈ l.map f ↔ ∃ a, a ∈ l ∧ f a = b := by
  induction l <;> aesop

@[aesop safe apply]
theorem mem_map_of_mem (f : α → β) {a : α} {l : List α} (h : a ∈ l) :
    f a ∈ l.map f := by
  aesop

@[aesop safe destruct]
theorem eq_nil_of_subset_nil {l : List α} : l ⊆ [] → l = [] := by
  aesop (add 1% cases List)

attribute [local aesop 1% cases] List

example {l : List α} : l ⊆ [] → l = [] := by
  aesop
