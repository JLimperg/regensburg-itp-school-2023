/-# Help -/

import Mathlib.Tactic

/- ## Available commands/tactics/... -/

#help option
#help tactic
#help conv

/- ## Computation -/

#eval 1 + 1 -- 2
#reduce 1 + 1 -- 2
-- #eval fun x => x + 1 -- fails
#reduce fun x => x + 1 -- fun x => Nat.succ x

/- ## Typeclasses -/

#synth ∀ {n : ℕ},  Decidable (Even n)
-- #synth ∀ {n : ℝ}, Decidable (Even n) -- fails
#instances Decidable

/- ## library_search -/

example {m n : ℕ} : m + n = n + m := by
  exact?

example {m n : ℕ} : n.succ = m.succ → n = m := by
  exact?

example {m n : ℕ} : n.succ.succ = m.succ.succ → n = m := by
  intros
  fail_if_success exact?
  apply?

/- ## What does my automation do? -/

example {m n : ℕ} : n.succ.succ = m.succ.succ → n = m := by
  simp?

example {m n : ℕ} : n.succ.succ = m.succ.succ → n = m := by
  set_option trace.Meta.Tactic.simp.rewrite true in
  simp?

example {P Q R : Prop} : P ∨ Q → (P → R) → (Q → R) → R := by
  aesop?

example {P Q R : Prop} : P ∨ Q → (P → R) → (Q → Q) → R := by
  set_option trace.aesop true in
  aesop
  sorry
