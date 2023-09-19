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
