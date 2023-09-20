/-# Help -/

import Mathlib.Tactic

/- ## Available commands/tactics/... -/

#help option
#help tactic
#help conv

/- ## Computation -/

#eval 1 + 1
#reduce 1 + 1
-- #eval fun x => x + 1 -- fails
#reduce fun x => x + 1

/- ## library_search -/

example {m n : ℕ} : m + n = n + m := by
  exact?

example {m n : ℕ} : n.succ = m.succ → n = m := by
  exact?

example {m n : ℕ} : n.succ.succ = m.succ.succ → n = m := by
  intros
  fail_if_success exact?
  apply?
