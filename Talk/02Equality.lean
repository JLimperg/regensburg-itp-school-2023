/- # Equality -/

import Mathlib.Tactic

example {n : ℕ} : n = n := by
  rfl

example : 21 * 2 = 42 := by
  rfl

example {m n o : ℕ} : m = n → n = o → m = o := by
  intros mn no
  rw [mn]
  rw [no]

example {f g : α → β} (h : ∀ a, f a = g a) : f = g := by
  funext a
  apply h

example {f : α → β → γ} : f a b = f a' b' := by
  congr
  all_goals sorry

/- ## Calc Mode -/

example {f g : α → β → γ} (fg : f = g) (ab : a = b) (bc : b = c) (xy : x = y) :
    f a x = g c y := by
  calc
    f a x = f b x := by rw [ab]
    _     = f c x := by rw [bc]
    _     = f c y := by rw [xy]
    _     = g c y := by rw [fg]

/- ## Conv Mode -/

-- Example from TPIL, more at
-- https://leanprover.github.io/theorem_proving_in_lean4/conv.html

example (a b c : ℕ) : a * (b * c) = a * (c * b) := by
  conv =>
    lhs
    right
    rw [mul_comm]

example (a b c : ℕ) : a * (b * c) = a * (c * b) := by
  conv => lhs; right; rw [mul_comm]

example (a b c : ℕ) : a * (b * c) = a * (c * b) := by
  conv in b * c => rw [mul_comm]

/- ## The Simplifier -/

-- Some examples from TPIL, more at
-- https://leanprover.github.io/theorem_proving_in_lean4/tactics.html#using-the-simplifier

example (x y z : ℕ) : (x + 0) * (0 + y * 1 + z * 0) = x * y := by
  simp

example (x y : ℕ) (P : Nat → Prop) (h : P (x + 0 + y * 0)) : P x := by
  simp at h
  assumption

example (x y : ℕ) (P : Nat → Prop) (h : P (x + 0 + y * 0)) : P (x + 0) := by
  simp at *
  assumption

example (x y : ℕ) (h : x = y) : x + 0 + y = y + y := by
  simp [h]

example (x y : ℕ) (h : x = y) : x + 0 + y = y + y := by
  simp [← h]

example (x y : ℕ) (h : x = y) : x + 0 + y = y + y := by
  simp [*]

example (x y : ℕ) (P : Nat → Prop) (h : P (x + 0 + y * 0)) : P x := by
  simp_all

def mkSymm (xs : List α) : List α :=
  xs ++ xs.reverse

@[simp]
theorem reverse_mkSymm (xs : List α) : (mkSymm xs).reverse = mkSymm xs := by
  simp [mkSymm]

example (xs ys : List α) :
    (xs ++ mkSymm ys).reverse = mkSymm ys ++ xs.reverse := by
  simp [reverse_mkSymm]

/- ### Associativity and Commutativity -/

example (x y : ℕ) : (x + y) + z = x + (y + z) := by
  simp only [add_assoc]

example (x y : ℕ) : x + y = y + x := by
  simp only [add_comm]

example (x y z : ℕ) : (x + y + z) + x = x + y + z + x := by
  simp only [add_assoc, add_comm]

/- ### Propositional Simplification -/

example (a : A) (b : B) : A ∧ B := by
  simp [*]

example : A ∧ B → B ∧ A := by
  fail_if_success (simp; done)
  intros
  simp [*]

example : A ∨ B → B ∨ A := by
  fail_if_success simp
  aesop
