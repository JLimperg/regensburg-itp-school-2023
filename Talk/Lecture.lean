import Mathlib
import Mathlib.Data.Nat.Basic

/- # Basic Tactics -/

/- ## Logic -/

/- ### True -/

example : True := by
  apply True.intro

/- ### False -/

example : False → α := by
  intro contra
  cases contra

example : False → α :=
  False.elim

/- ### Implication, Forall -/

example : (A → B) → A → B := by
  intros hab ha
  apply hab
  exact ha

example : ∀ (hab : ∀ (a : A), B) (ha : A), B := by
  intros hab ha
  apply hab
  exact ha

example : (A → B → C) → A → B → C := by
  intros habc a b
  refine habc ?_ b
  exact a

example : (A → B → C) → A → B → C := by
  intros habc a b
  refine' habc _ b
  exact a

/- ### And -/

example : A ∧ B → B ∧ A := by
  intro h
  cases' h with a b
  constructor
  · exact b
  · exact a

example : A ∧ B → B ∧ A := by
  intro h
  match h with
  | ⟨a, b⟩ => constructor <;> assumption

example : A ∧ B → B ∧ A := by
  intro h
  cases h with
  | intro a b => constructor <;> assumption

example : A ∧ B → B ∧ A := by
  intro h
  have ⟨a, b⟩ := h
  constructor <;> assumption

example : A ∧ B → B ∧ A := by
  intro ⟨a, b⟩
  constructor <;> assumption

example : (A ∧ B) ∧ C → A ∧ (B ∧ C) := by
  intro ⟨x, c⟩
  have ⟨a, b⟩ := x
  (repeat' constructor) <;> assumption

example : (A ∧ B) ∧ C → A ∧ (B ∧ C) := by
  intro ⟨⟨a, b⟩, c⟩
  (repeat' constructor) <;> assumption

example : A ∧ B → B ∧ A := by
  fail_if_success (simp; done)
  intros; simp_all

/- ### Or -/

example : A ∨ B → B ∨ A := by
  intro h
  cases' h with a b
  · right
    exact a
  · left
    exact b

example : A ∨ B → B ∨ A := by
  intro h
  match h with
  | .inl a => right; assumption
  | .inr b => left; assumption

example : A ∨ B → B ∨ A := by
  intro h
  cases h with
  | inl a => right; assumption
  | inr b => left; assumption

example : A ∨ B → B ∨ A := by
  rintro (a | b)
  · right; assumption
  · left; assumption

example : A ∨ B → B ∨ A := by
  intro h
  obtain (a | b) := h
  · right; assumption
  · left; assumption

example : A ∨ B → B ∨ A := by
  intro h
  rcases h with (a | b)
  · right; assumption
  · left; assumption

example : A ∨ B → B ∨ A := by
  fail_if_success simp
  aesop

/- ## Exists, Sigma -/

example {P Q : α → Prop} : (∃ x, P x) → (∀ x, P x → Q x) → ∃ x, Q x := by
  intro ex hPQ
  cases' ex with x hP
  use x
  aesop

example {P Q : α → Prop} : (∃ x, P x) → (∀ x, P x → Q x) → ∃ x, Q x := by
  intro ⟨x, hP⟩ hPQ
  exists x
  aesop

example {P Q : α → Type} : (Σ x, P x) → (∀ x, P x → Q x) → Σ x, Q x := by
  intro ⟨x, hP⟩ hPQ
  exists x
  aesop

example {P Q : α → Type} : (Σ x, P x) → (∀ x, P x → Q x) → Σ x, Q x := by
  aesop

/- ## Equality -/

example {n : ℕ} : n = n := by
  rfl

example : 21 * 2 = 42 := by
  rfl

example {m n o : ℕ} : m = n → n = o → m = o := by
  intros mn no
  rw [mn, no]

example {m n o : ℕ} : m = n → n = o → m = o := by
  intros mn no
  simp_all

example {f g : α → β} (h : ∀ a, f a = g a) : f = g := by
  funext a
  apply h

example {f : α → β → γ} : f a b = f a' b' := by
  congr
  repeat sorry

/- ### Calc Mode -/

example {f g : α → β → γ} (fg : f = g) (ab : a = b) (bc : b = c) (xy : x = y) :
    f a x = g c y :=
  calc
    f a x = f b x := by rw [ab]
    _     = f c x := by rw [bc]
    _     = f c y := by rw [xy]
    _     = g c y := by rw [fg]

/- ### Conv Mode -/

example (a b c : ℕ) : a * (b * c) = a * (c * b) := by
  conv =>
    lhs
    congr
    rfl
    rw [Nat.mul_comm]

example (a b c : ℕ) : a * (b * c) = a * (c * b) := by
  conv => lhs; right; rw [Nat.mul_comm]

example (a b c : ℕ) : a * (b * c) = a * (c * b) := by
  conv in b * _ => rw [Nat.mul_comm]

-- Example from TPIL. More examples:
-- https://leanprover.github.io/theorem_proving_in_lean4/conv.html

/- ## Structured Proof -/

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
  use N
  show ∀ n ≥ N, |(f ∘ u) n - f x₀| ≤ ε
  aesop

/- ## Inductive Types and Induction -/

inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

namespace MyNat

def add : MyNat → MyNat → MyNat
  | m, zero => m
  | m, (succ n) => succ (add m n)

instance : Add MyNat :=
  ⟨add⟩

protected def ofNat : Nat → MyNat
  | .zero => zero
  | .succ n => succ (MyNat.ofNat n)

instance : OfNat MyNat n where
  ofNat := .ofNat n

@[simp]
theorem succ_eq_add_one (m : MyNat) : succ m = m + 1 := rfl

@[simp]
theorem zero_eq_zero : (zero : MyNat) = 0 := rfl

@[simp]
theorem add_zero (m : MyNat) : m + 0 = m := rfl

@[simp]
theorem add_add_one (m n : MyNat) : m + (n + 1) = (m + n) + 1 := rfl

theorem one_add_add (m n : MyNat) : (m + 1) + n = m + n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp
    congr 1

@[simp]
theorem zero_add (m : MyNat) : 0 + m = m := by
  induction m with
  | zero => dsimp
  | succ m ih =>
    dsimp
    rw [ih]

theorem add_assoc (m n o : MyNat) : m + (n + o) = m + n + o := by
  induction o with
  | zero => simp
  | succ o ih => simp [ih]

theorem add_comm (m n : MyNat) : m + n = n + m := by
  induction n with
  | zero =>
    dsimp
    rw [zero_add]
  | succ n ih =>
    dsimp
    rw [one_add_add]
    rw [ih]

end MyNat

/- # Structures (and Universes) -/

structure Pair (α : Type u) (β : Type v) : Type (max u v) where
  fst : α
  snd : β

#check Pair
#check Pair.mk
#check Pair.fst
#check Pair.snd

structure Sig (α : Type u) (β : α → Type v) : Type (max u v) where
  intro ::
  fst : α
  snd : β fst

#check Sig
#check Sig.intro
#check Sig.fst
#check Sig.snd

/- # Type Classes and the Algebraic Hierarchy -/

namespace TC

class Mul (α : Type u) where
  mul : α → α → α

local infixl : 70 (priority := high) "*" => Mul.mul

example [Mul α] (x y : α) : α :=
  x * y

class One (α : Type u) where
  one : α

instance [One α] : OfNat α 1 where
  ofNat := One.one

def npowRec [One M] [Mul M] : ℕ → M → M
  | 0, _ => 1
  | n + 1, a => a * npowRec n a

class MulOneClass (M : Type u) extends One M, Mul M where
  one_mul : ∀ a : M, 1 * a = a
  mul_one : ∀ a : M, a * 1 = a

class Semigroup (G : Type u) extends Mul G where
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)

class Monoid (M : Type u) extends Semigroup M, MulOneClass M where
  npow : ℕ → M → M := npowRec
  npow_zero : ∀ x, npow 0 x = 1 := by intros; rfl
  npow_succ : ∀ (n : ℕ) (x), npow (n + 1) x = x * npow n x := by intros; rfl

-- ...
-- class Ring (R : Type u) extends Semiring R, AddCommGroup R, AddGroupWithOne R
-- ...

structure OneHom (M : Type*) (N : Type*) [One M] [One N] where
  toFun : M → N
  map_one' : toFun 1 = 1

structure MulHom (M : Type*) (N : Type*) [Mul M] [Mul N] where
  toFun : M → N
  map_mul' : ∀ x y, toFun (x * y) = toFun x * toFun y

infixr:25 " →ₙ* " => MulHom

structure MonoidHom (M : Type*) (N : Type*) [MulOneClass M] [MulOneClass N] extends
  OneHom M N, M →ₙ* N

class FunLike (F : Sort*) (α : outParam (Sort*)) (β : outParam <| α → Sort*) where
  coe : F → ∀ a : α, β a
  coe_injective' : Function.Injective coe

instance (priority := 100) [FunLike F α β] : CoeFun F fun _ ↦ ∀ a : α, β a where
  coe := FunLike.coe

class OneHomClass (F : Type*) (M N : outParam (Type*)) [One M] [One N]
    extends FunLike F M fun _ => N where
  map_one : ∀ f : F, f 1 = 1

class MulHomClass (F : Type*) (M N : outParam (Type*)) [Mul M] [Mul N]
    extends FunLike F M fun _ => N where
  map_mul : ∀ (f : F) (x y : M), f (x * y) = f x * f y

class MonoidHomClass (F : Type*) (M N : outParam (Type*)) [MulOneClass M] [MulOneClass N]
  extends MulHomClass F M N, OneHomClass F M N

end TC

/-# More Help -/

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

-- Commented because these commands take a long time to execute and drain my
-- laptop battery in the process.

-- example {m n : ℕ} : m + n = n + m := by
--   exact?

-- example {m n : ℕ} : n.succ = m.succ → n = m := by
--   exact?

-- example {m n : ℕ} : n.succ.succ = m.succ.succ → n = m := by
--   intros
--   fail_if_success exact?
--   apply?

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

/- # Foundational Differences between Coq and Lean -/

/- ## Non-Cumulative Universes -/

example (α : Type u) : Type (u + 1) := ULift.{u+1,u} α

/- ## Definitionally Proof-Irrelevant Prop -/

example (P : Prop) (p q : P) : p = q :=
  rfl

example (a : α) (b : β) : (Or.inl a : α ∨ β) = (Or.inr b : α ∨ β) :=
  rfl

example {a b : α} (p q : a = b) : p = q :=
  rfl

inductive REq {α : Type u} (a : α) : α → Type u
  | rfl : REq a a

example {a b : α} : ∀ (p q : REq a b), REq p q
  | .rfl, .rfl => .rfl

/- ## Quotients -/

#check (Quot :
         ∀ {α : Sort _}, (α → α → Prop) → Sort _)
#check (Quot.mk :
         ∀ {α} (R : α → α → Prop), α → Quot R)
#check (Quot.lift :
         ∀ {α} {R : α → α → Prop} {β} (f : α → β),
           (∀ (a b : α), R a b → f a = f b) → Quot R → β)
#check (Quot.sound :
         ∀ {α} {R : α → α → Prop} {a b : α}, R a b →
           Quot.mk R a = Quot.mk R b)
#check (Quot.ind :
         ∀ {α} {R : α → α → Prop} {P : Quot R → Prop},
           (∀ a, P (Quot.mk R a)) → ∀ (q : Quot R), P q)

example (R : α → α → Prop) (f : α → β) (resp : ∀ a b, R a b → f a = f b)
    (a : α) : Quot.lift f resp (Quot.mk R a) = f a :=
  rfl

/- # Extended Example: MiniChess -/

namespace MiniChess

inductive Color : Type
  | white : Color
  | black : Color
  deriving DecidableEq

#check Color
#print Color
#check Color.white

inductive Piece
  | rook
  | king
  deriving DecidableEq

structure Pos (n : ℕ) where
  x : Fin n
  y : Fin n
  deriving DecidableEq

#print Pos
#check Pos.x
#check Pos.y

inductive Piece.LegalMove (start stop : Pos n) : Piece → Prop
  | rookHorizontal :
    start ≠ stop →
    start.y = stop.y →
    LegalMove start stop rook
  | rookVertical :
    start ≠ stop →
    start.x = stop.x →
    LegalMove start stop rook
  | king :
    start ≠ stop →
    start.x.val.dist stop.x.val ≤ 1 →
    start.y.val.dist stop.y.val ≤ 1 →
    LegalMove start stop king

inductive Bad.LegalMove (start stop : Pos n) : Peice → Prop
-- ...

set_option autoImplicit false
set_option autoImplicit true

section LegalMove

variable {p : Piece}

theorem Piece.LegalMove.start_ne_stop : LegalMove start stop p → start ≠ stop
  | rookHorizontal h .. => h
  | rookVertical   h .. => h
  | king           h .. => h

theorem foo : p.LegalMove start stop → start ≠ stop := by
  intro legal
  cases legal with
  | rookHorizontal h _ => exact h
  | rookVertical h _ => exact h
  | king h _ _ => exact h

instance : Decidable (p.LegalMove start stop) :=
  if heq : start = stop then
    isFalse fun contra => contra.start_ne_stop heq
  else
    match p with
    | .rook =>
      if hx : start.x = stop.x then
        isTrue <| .rookVertical heq hx
      else if hy : start.y = stop.y then
        isTrue <| .rookHorizontal heq hy
      else
        isFalse fun
          | .rookHorizontal _ hy' => hy hy'
          | .rookVertical   _ hx' => hx hx'
    | .king =>
      if h : start.x.val.dist stop.x.val ≤ 1 ∧
             start.y.val.dist stop.y.val ≤ 1 then
        isTrue <| .king heq h.left h.right
      else
        isFalse <| fun | .king _ hx hy => by simp_all

end LegalMove

structure PPiece where
  color : Color
  piece : Piece
  deriving DecidableEq

def PPiece.LegalMove (p : PPiece) (start stop : Pos n) : Prop :=
  p.piece.LegalMove start stop

instance {p : PPiece} : Decidable (p.LegalMove start stop) :=
  inferInstanceAs <| Decidable (p.piece.LegalMove start stop)

def Board n := Pos n → (Option PPiece)

namespace Board

def set (b : Board n) (pos : Pos n) (p? : Option PPiece) : Board n :=
  fun pos' => if pos = pos' then p? else b pos'

theorem set_same {b : Board n} : (b.set pos p?) pos = p? := by
  simp [set]

theorem set_different {b : Board n} : pos' ≠ pos → (b.set pos p?) pos' = b pos' := by
  intro h
  simp [set]
  intros
  simp_all

def At (b : Board n) (pos : Pos n) (p : PPiece) : Prop :=
  b pos = some p

def Empty (b : Board n) (pos : Pos n) : Prop :=
  b pos = none

instance {b : Board n} : Decidable (b.At pos p) :=
  inferInstanceAs <| Decidable (b pos = some p)

end Board

structure Move (n) where
  piece : PPiece
  start : Pos n
  stop  : Pos n

namespace Move

structure Legal (m : Move n) (b : Board n) : Prop where
  hstart : b.At m.start m.piece
  hmove : m.piece.LegalMove m.start m.stop
  hstop : ∀ p, b.At m.stop p → p.color ≠ m.piece.color

#print Decidable

instance {m : Move n} : Decidable (m.Legal b) :=
  if hstart : b.At m.start m.piece then
    if hmove : m.piece.LegalMove m.start m.stop then
      match hp' : b m.stop with
      | some p' =>
        if hcolor : p'.color = m.piece.color then
          isFalse fun contra => contra.hstop p' hp' hcolor
        else
          have hstop : ∀ p', b.At m.stop p' → p'.color ≠ m.piece.color :=
            fun _ _ => by simp_all [Board.At]
          isTrue { hstart := hstart, hmove := hmove, hstop := hstop }
      | none =>
        have hstop : ∀ p', b.At m.stop p' → p'.color ≠ m.piece.color :=
          fun _ _ => by simp_all [Board.At]
        isTrue { hstart, hmove, hstop }
    else
      isFalse fun contra => hmove contra.hmove
  else
    isFalse fun contra => hstart contra.hstart

example {m : Move n} : Decidable (m.Legal b) := by
  by_cases hstart : b.At m.start m.piece
  · by_cases hmove : m.piece.LegalMove m.start m.stop
    · match hp' : b m.stop with
      | some p' =>
        by_cases hcolor : p'.color = m.piece.color
        · apply isFalse
          intro contra
          apply contra.hstop
          · exact hp'
          · exact hcolor
        · apply isTrue
          constructor
          · exact hstart
          · exact hmove
          · intros p' hp'
            simp_all [Board.At]
      | none =>
        apply isTrue
        constructor
        · exact hstart
        · exact hmove
        · intros p' hp'
          simp_all [Board.At]
    · apply isFalse
      intro contra
      apply hmove
      exact contra.hmove
  · apply isFalse
    intro contra
    apply hstart
    exact contra.hstart

attribute [aesop norm unfold] Board.At
attribute [aesop 50% constructors] Decidable
attribute [aesop safe [cases, constructors]] Move.Legal

example {m : Move n} : Decidable (m.Legal b) := by
  by_cases hstart : b.At m.start m.piece
  · by_cases hmove : m.piece.LegalMove m.start m.stop
    · match hp' : b m.stop with
      | some p' => by_cases hcolor : p'.color = m.piece.color <;> aesop
      | none => aesop
    · aesop
  · aesop

def apply (m : Move n) (b : Board n) : Board n :=
  b.set m.start none |>.set m.stop m.piece

end MiniChess.Move

/- # Metaprogramming -/

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
