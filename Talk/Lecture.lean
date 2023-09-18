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

/- # Prop -/

inductive Disj (α β : Prop) : Prop
  | left  : α → Disj α β
  | right : β → Disj α β

example (a : α) (b : β) : Disj α β :=
  Disj.left a

example (a : α) (b : β) : Disj α β :=
  Disj.right b

example (a : α) (b : β) : Disj.left a = Disj.right b :=
  rfl

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

/- # Differences between Coq and Lean -/

/- # Extended Example: MiniChess -/

/-
We'll formalize some properties of an implementation of a small subset of
chess. In the process, we'll use many of the programming and some of the
proving facilities of Lean.
-/

/-
We put our entire development into the `MiniChess` namespace. This means that
when we define a value `x`, its name is actually `MiniChess.x`. Namespaces serve
to distinguish functions which would naturally have the same name. For example,
we can have functions `Nat.add` (addition on natural numbers) and `Int.add`
(addition on integers).
-/

namespace MiniChess

/-
To start the formalisation proper, we define a type representing the player
colors of chess.
-/

inductive Color : Type
  | white : Color
  | black : Color
  deriving DecidableEq

/-
As in Coq, inductive types have 0 or more constructors, which are
distinguished functions whose return type is the type being defined (here
`Color`). In simple cases, we need not write the return type, so we could
remove `: Color` in the constructor types.

The clause `deriving DecidableEq` instructs Lean to generate a function which
decides whether two values `x, y : Color` are equal. We'll have more to say
about this later.

To inspect objects we've defined, we can use commands such as `#check` and
`#print`. The `#check` command shows the type of a term. The `#print` command
shows the definition of an object (inductive type, definition, ...).

Commands which are purely informative (i.e., they don't change the state of the
Lean system) are prefixed with `#`.
-/

#check Color
#print Color

/-
We can also check that the `white` constructor of `Color` is really a function
that returns `Color`. (Here, the function has no arguments, so it's a constant.)
Note that, unlike in Coq, the `white` constructor is placed in the `Color`
namespace.
-/

#check Color.white

/-
We'll also need a type of chess pieces. We'll consider only rooks and kings.
-/

inductive Piece
  | rook
  | king
  deriving DecidableEq

/-
Each piece in play is located at a specific position on the chess board. For
a board of size n × n, we define the type of positions `Pos n`. A `Pos n` is
a pair of an x-coordinate and a y-coordinate, both of type `Fin n`, which is the
type of natural numbers 0, ..., n - 1 (so `Fin n` has exactly `n` elements).

To support boards of any size, we parameterise the type `Pos` by the size
`n : ℕ` of the board. Thus, `Pos` has type `ℕ → Type`; it is a function, or
family, of types.
-/

structure Pos (n : ℕ) where
  x : Fin n
  y : Fin n
  deriving DecidableEq

/-
Positions are defined as a structure. Structures are specific inductive types
which represent tuples of finitely many elements. The elements are called fields
of the structure and can all have different types.

The inductive type corresponding to a structure has one constructor, called `mk`
by default, which takes one argument for each field. If we `#print Pos`, we can
see the inductive type generated for the `Pos` structure.
-/

#print Pos

/-
In addition to the type itself, the `structure` command also generates
projections `Pos.x` and `Pos.y`, which extract the fields from a `Pos` value:
-/

#check Pos.x
#check Pos.y

/-
We now define the legal moves of our chess pieces as a relation
`LegalMove ⊆ Pos n × Pos n × Piece`, where an element
`(start, stop, p) ∈ LegalMove` signifies that the piece `p` can move from
position `start` to position `stop`. We encode this relation as an inductive
predicate -- an inductive type with arguments `start`, `stop` and `p` and
codomain `Prop`.
-/

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

/-
There's a lot going on here, so we'll go through this declaration slowly.

First, a detail: we write `Piece.LegalMove`, putting the `LegalMove` type into
the `Piece` namespace. Within the declaration, Lean automatically opens the
`Piece` namespace, so we can write just `LegalMove` instead of
`Piece.LegalMove`.

Next, the codomain of `LegalMove`, `Prop`, is a universe of types, so terms `P :
Prop` can be used as types of other terms. For example, `∀ (p : P), ...` is
legal. We call `P` a proposition and `p : P` its proof. Other universes are
called `Type` (aka `Type 0`), `Type 1`, `Type 2`, etc. If we don't specify the
type of an inductive type, as with `Color` and `Piece`, Lean infers a sensible
choice, here `Type`.

As in Coq, the universes are arranged in a hierarchy:
`Prop : Type 0`, `Type 0 : Type 1`, `Type 1 : Type 2`, etc.
-/

#check Prop
#check Type
#check Type 0
#check Type 1

/-
Lean's `Prop` has slightly different properties than Coq's, which we'll come
back to.

Next, observe the arguments of `LegalMove`. The first two, `start` and `stop`,
appear before the colon and are therefore parameters. The last, of type `Piece`,
is an index. The difference is that parameters are fixed throughout the
declaration: wherever `LegalMove` appears in the declaration, it must be applied
precisely to `start` and `stop`. Indices, on the other hand, can be given
arbitrary values in the constructor types.

A detail before we get to the constructors: in the type `Pos n` of `start` and
`stop`, what is `n`? It is not bound anywhere, so Lean automatically figures out
that `n` must have type `ℕ` and generates an implicit argument `{n : ℕ}`,
inserted at the start of the type signature of `LegalMove`. We can `#check` the
type of `LegalMove` to confirm this:
-/

#check Piece.LegalMove

/-
These arguments are called auto-implicit. They are great for decluttering type
signatures since we can omit 'obvious' type annotations. However, auto-implicit
arguments can also make it harder to spot mistakes in declarations. Consider
this version of `LegalMove` with a typo:
-/

inductive Bad.LegalMove (start stop : Pos n) : Peice → Prop
-- ...

/-
If you add the same constructors as above, Lean accepts the declaration, but the
relation it defines is not at all the one we wanted. Other times you might get
confusing error messages if Lean gets confused by a wrongly inserted
auto-implicit argument. So look for suspicious colouring (auto-implicit
arguments are coloured as variables rather than defined constants). If you
prefer, you can also disable auto-implicit arguments:
-/

set_option autoImplicit false

/-
However, I like auto-implicits, so I'll reactive them.
-/

set_option autoImplicit true

/-
Let's finally consider the constructors of `LegalMove`. We have three types
of legal moves, corresponding to the three constructors. The rook can move
in a horizontal or vertical line. The king can move to any adjacent square. The
inductive type's constructors formalize these restrictions:

- The `rookHorizontal` constructor says that `(start, stop, rook)` are related
  by `LegalMove` if the y-coordinates of `start` and `stop` are equal. The
  x-coordinates of `x` and `y` can be arbitrary, with the exception that
  `start` and `stop` cannot be the same position.
- The `rookVertical` constructor says that, similarly, `(start, stop, rook)` are
  related if the x-coordinates of `start` and `stop` are equal (and `start ≠
  stop`).
- The `king` constructor says that `(start, stop, king)` are related if the
  distance between the x-coordinates of `start` and `stop` is less than or equal
  to 1, and similar for the y-coordinate, and `start ≠ stop`.
- Any proof of the proposition `(start, stop, piece) ∈ LegalMove` is an
  application of one of the three constructors. This is a general property of
  inductive types. In other words, horizontal/vertical rook moves and one-square
  king moves are the only legal moves.

In the constructor types, we pervasively use dot notation, a syntactic feature
that allows us to write, for example, `start.x` instead of `Pos.x start`. The
general rule is that if you write `t.f` and the term `t` has type `T`, and the
function `T.f` exists and has an argument of type `T`, then the dot notation
`t.f` expands into an application of `T.f` to `t`. If `T.f` has multiple
arguments of type `T`, then `t` is used as the value for the first of these. `T`
can also be an application of a type family, e.g. `T = List α`, in which case we
look for `List.f`. And finally, dot notation can be chained, so
`start.x.val.dist` is short for `Nat.dist (Fin.val (Pos.x start))`.

Two more details about the constructor types:

- The index of type `Piece` of `LegalMove` is given different values in the
  constructors: it is `rook` in the first two constructors and `king` in the
  third. This is the power of indices as opposed to parameters.
- We can write `rook` and `king`, rather than `Piece.rook` and `Piece.king`,
  because the `Piece` namespace is open in the declaration.

Now, let us prove some basic facts about legal moves. We put these facts into a
section named `LegalMove`. Certain commands are scoped to the current section,
meaning they become inactive once the current section ends. Other than that,
sections have no effect. The similar `namespace` command, which we saw earlier,
also acts as a section, but additionally modifies the names of declarations in
the `namespace` section.
-/

section LegalMove

/-
We first use a `variable` command to declare that in the following, wherever
`p` appears (and is not otherwise bound), it should be added to the type
signature of the respective declaration as an implicit argument of type `Piece`.
Variable commands are scoped to the current section.
-/

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

/- ## Writing Custom Tactics -/
