/-# Help -/

import Mathlib.Tactic

/- ## Finding Lemmas -/

-- Mathlib docs: https://leanprover-community.github.io/mathlib4_docs/

example {m n : ℕ} : m + n = n + m := by
  exact?

example {m n : ℕ} : n.succ = m.succ → n = m := by
  intros; exact?

example {m n : ℕ} : n.succ.succ = m.succ.succ → n = m := by
  intros
  fail_if_success exact?
  apply?

-- #find Real.sin _ = 0

-- Loogle: https://loogle.lean-fro.org

/- ## Finding Available Commands/Tactics/... -/

#help option
#help tactic
#help conv

/- ## Computation -/

#eval 1 + 1
#reduce 1 + 1
-- #eval fun x => x + 1 -- fails
#reduce fun x => x + 1