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

open Lean.Parser.Tactic Lean.Syntax in
macro "simp!!" "[" ls:(simpStar <|> simpErase <|> simpLemma),* "]" : tactic =>
  let ls : TSepArray [``simpStar, ``simpErase, ``simpLemma] "," :=
    ⟨ls.elemsAndSeps⟩
  `(tactic| (simp (discharger := crush) [$ls,*]))

example (m n : ℕ) (h₁ : m ≤ n) (h₂ : m ≥ n)
    (xy : m = n → x = y) (yz : y = z) : x = z := by
  fail_if_success simp [*]
  simp!! [*]

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

/- ### Main Data Structures -/

inductive Demo.Expr where
  | bvar (deBruijnIndex : Nat)
  | fvar (fvarId : FVarId)
  | mvar (mvarId : MVarId)
  | sort (u : Level)
  | const (declName : Name) (us : List Level)
  | app (fn : Expr) (arg : Expr)
  | lam (binderName : Name) (binderType : Expr) (body : Expr) (binderInfo : BinderInfo)
  | forallE (binderName : Name) (binderType : Expr) (body : Expr) (binderInfo : BinderInfo)
  | letE (declName : Name) (type : Expr) (value : Expr) (body : Expr) (nonDep : Bool)
  | lit : Literal → Expr
  | mdata (data : MData) (expr : Expr)
  | proj (typeName : Name) (idx : Nat) (struct : Expr)

example : Nat → Nat := by
  refine fun (n : Nat) => Nat.succ ?_
  exact n

#check Environment

elab "print_decl_info " id:ident : tactic => do
  let (some decl) := (← getEnv).find? id.getId
    | throwError "not found!"
  logInfo m!"Name: {decl.name}"
  logInfo m!"Type: {decl.type}"

example : True := by
  print_decl_info Nat
  print_decl_info Nat.zero
  trivial

#check MetavarContext

elab "print_main_goal_info" : tactic =>
  withMainContext do
    let goal ← getMainGoal
    let mdecl ← goal.getDecl
    let target := mdecl.type
    let lctx := mdecl.lctx
    logInfo m!"MVarId: {goal.name}"
    logInfo m!"Target: {target}"
    logInfo m!"Number of hyps: {lctx.size}"
    for ldecl in lctx do
      logInfo m!"FVarId: {ldecl.fvarId.name}"
      logInfo m!"Name: {ldecl.userName}"
      logInfo m!"Type: {ldecl.type}"

example (n : Nat) : ¬ n < 0 := by
  print_main_goal_info
  simp

#check Lean.Elab.Tactic.State

/- ### Splitting Disjunctions -/

variable (A B : Prop)

set_option pp.all true in
#check A ∨ B

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

/- ## Embedded Domain-Specific Languages -/

inductive Tm where
  | var : ℕ → Tm
  | lam : Tm → Tm
  | app : Tm → Tm → Tm

declare_syntax_cat tm (behavior := both)

syntax num : tm
syntax "λ " tm : tm
syntax tm ppSpace tm : tm
syntax "(" tm ")" : tm

open Lean Lean.Meta Lean.Elab Lean.Elab.Term Qq in
partial def elabTm : TSyntax `tm → TermElabM Q(Tm)
  | `(tm| $n:num) => do
    let n : Q(ℕ) ← elabTerm n q(ℕ)
    return q(Tm.var $n)
  | `(tm| λ $t:tm) => do
    return q(Tm.lam $(← elabTm t))
  | `(tm| $t:tm $u:tm) => do
    return q(Tm.app $(← elabTm t) $(← elabTm u))
  | `(tm| ($t:tm)) =>
    elabTm t
  | _ => throwUnsupportedSyntax

elab "tm%⟨" t:tm "⟩" : term =>
  elabTm t

example : Tm := tm%⟨ (λ 0 0) (λ 0 0) ⟩
-- (λ x. x x) (λ x. x x)
