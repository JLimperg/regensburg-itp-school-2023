import Mathlib

example (x y : ℝ) : 2*(x + y)*3 = 6*x + 6*y := by
  ring

example (x y z : ℝ) : (x + y*z) = z*y + x := by
  ring

example (x : ℂ) : (x + 2)/2 + (x - 2)/2 = x := by
  ring

example (x y z : ℚ) (h1 : 2*x < 3*y) (h2 : -4*x + 2*z < 0)
    (h3 : 12*y - 4*z < 0) : False := by
  linarith

example (x y : ℤ) : x < 0 → y + x < y := by
  norm_num

example (x : ℤ) (h₁ : 0 ≤ x) (h₂ : x ≠ 0) : 0 < x := by
  positivity

example (x y : ℤ) (hx : 0 < x) (hy : 0 < y) : 0 < x + y := by
  positivity

example (x y : ℤ) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x*y := by
  positivity

example (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    Continuous (f ∘ g) := by
  continuity

example (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g) :
    Measurable (f ∘ g) := by
  measurability
