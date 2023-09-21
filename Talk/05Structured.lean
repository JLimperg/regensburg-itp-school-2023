/- # Structured Proof -/

import Mathlib.Tactic

-- Example from A Glimpse of Lean

def SeqLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

def ContAt (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

example (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ) (hu : SeqLimit u x₀)
    (hf : ContAt f x₀) : SeqLimit (f ∘ u) (f x₀) := by
  unfold SeqLimit
  intro ε hε
  have ⟨δ, δ_pos, Hf⟩ := hf ε hε
  have ⟨N, Hu⟩ := hu δ δ_pos
  use N
  intro n hn
  apply Hf
  exact Hu n hn

example (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ) (hu : SeqLimit u x₀)
    (hf : ContAt f x₀) : SeqLimit (f ∘ u) (f x₀) := by
  show ∀ ε > 0, ∃ N, ∀ n ≥ N, |(f ∘ u) n - f x₀| ≤ ε
  intro (ε : ℝ) (hε : ε > 0)
  have ⟨δ, δ_pos, Hf⟩ : ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε :=
    hf ε hε
  have ⟨N, Hu⟩ : ∃ N, ∀ n ≥ N, |u n - x₀| ≤ δ :=
    hu δ δ_pos
  show ∃ N, ∀ n ≥ N, |(f ∘ u) n - f x₀| ≤ ε
  use N
  show ∀ n ≥ N, |(f ∘ u) n - f x₀| ≤ ε
  aesop
