/- # Metaprogramming -/

import Mathlib.Tactic

/- ## Macros: Syntactic Metaprogramming -/

example (a : α) (b : β) (c : γ) : α ∧ β ∧ γ := by
  constructor
  · exact a
  · constructor
    · exact b
    · exact c

macro "constructors" : tactic =>
  `(tactic| repeat' constructor)

example (a : α) (b : β) (c : γ) : α ∧ β ∧ γ := by
  constructors
  · exact a
  · exact b
  · exact c

syntax "crush" : tactic

macro_rules
  | `(tactic| crush) => `(tactic| aesop (options := { terminal := true }))
macro_rules
  | `(tactic| crush) => `(tactic| linarith; done)
macro_rules
  | `(tactic| crush) => `(tactic| continuity)
macro_rules
  | `(tactic| crush) => `(tactic| measurability)
macro_rules
  | `(tactic| crush) => `(tactic| decide)
macro_rules
  | `(tactic| crush) => `(tactic| norm_num; done)
macro_rules
  | `(tactic| crush) => `(tactic| assumption)
macro_rules
  | `(tactic| crush) => `(tactic| contradiction)

example : α ∧ β ↔ β ∧ α := by
  crush

example : 10^100 = 10^(50 * 2) := by
  crush

example (x y z : ℚ) (h1 : 2*x < 3*y) (h2 : -4*x + 2*z < 0)
    (h3 : 12*y - 4* z < 0) : False := by
  crush

/- ## Writing Custom Tactics -/

section Tactics

open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic

/- ### Proof by Assumption -/

def assm : TacticM Unit :=
  withMainContext do
    let goal ← getMainGoal
    let target ← goal.getType
    for ldecl in ← getLCtx do
      if ← isDefEq ldecl.type target then
        goal.assign ldecl.toExpr
        pruneSolvedGoals
        return
    throwTacticEx `assm goal "no suitable assumption"

elab "assm" : tactic => assm

example (h₁ : β) (h₂ : α) : α := by
  assm

example (h : β) : α := by
  fail_if_success assm
  sorry

/- ### Splitting Disjunctions -/

#check Expr

def isOr : Expr → Bool
  | .app (.app (.const ``Or _) _) _ => true
  | _ => false

def findFirstOrHyp : TacticM (Option FVarId) :=
  withMainContext do
    for ldecl in ← getLCtx do
      if isOr ldecl.type then
        return some ldecl.fvarId
    return none

def splitOr : TacticM Unit := do
  let some fvarId ← findFirstOrHyp
    | do throwTacticEx `split_or (← getMainGoal) "no suitable assumption"
  liftMetaTactic λ goal => do
    let subgoals ← goal.cases fvarId
    return subgoals.map (·.mvarId) |>.toList

elab "split_or" : tactic => splitOr

macro "split_ors" : tactic =>
  `(tactic| repeat' split_or)

example (h₁ : α ∨ β) (h₂ : γ ∨ δ) : α ∨ β ∨ γ ∨ δ := by
  split_ors
  all_goals aesop

end Tactics