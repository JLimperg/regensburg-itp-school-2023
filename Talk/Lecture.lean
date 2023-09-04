import Mathlib

namespace Talk

/-! # Functional Programming -/

inductive Color
  | white
  | black
  deriving DecidableEq

#check Color
#print Color

inductive Piece
  | rook
  | king
  deriving DecidableEq

structure Pos (n : Nat) where
  x : Fin n
  y : Fin n
  deriving DecidableEq, Fintype

#check Pos.x

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

section LegalMove

variable {p : Piece}

theorem Piece.LegalMove.start_ne_stop :
    p.LegalMove start stop → start ≠ stop
  | rookHorizontal h .. => h
  | rookVertical   h .. => h
  | king           h .. => h

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
          | .rookVertical _ hx' => hx hx'
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

namespace PPiece

def rook (color : Color) : PPiece :=
  { color, piece := .rook }

def king (color : Color) : PPiece :=
  { color, piece := .king }

def LegalMove (p : PPiece) (start stop : Pos n) : Prop :=
  p.piece.LegalMove start stop

instance {p : PPiece} : Decidable (p.LegalMove start stop) :=
  inferInstanceAs <| Decidable (p.piece.LegalMove start stop)

end PPiece

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

instance {b : Board n} : Decidable (b.At pos p) := by
  unfold At; exact inferInstance

instance {b : Board n} : Decidable (b.Empty pos) := by
  unfold Empty; exact inferInstance

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

end Move

namespace Board

instance [Fintype α] [DecidablePred P] : Fintype { x : α // P x } where
  elems := Finset.univ.subtype P
  complete := by simp

def PiecePositions (b : Board n) (p : PPiece) : Type :=
  { pos : Pos n // b.At pos p }

instance : Fintype (PiecePositions b p) :=
  by unfold PiecePositions; exact inferInstance

def pieceCount (b : Board n) (p : PPiece) : Nat :=
  Fintype.card (PiecePositions b p)

theorem pieceCount_set_none :
    pieceCount (b.set pos none) p =
      if b.At pos p then
        pieceCount b p - 1
      else
        pieceCount b p := by
  simp only [pieceCount, set]

structure Legal (b : Board n) where
  rookCount : ∀ (c : Color), b.pieceCount (.rook c) ≤ 2
  kingCount : ∀ (c : Color), b.pieceCount (.rook c) ≤ 1

end Board

theorem Move.apply_pieceCount {b : Board n} {m : Move n} (p : PPiece) :
    m.Legal b → (m.apply b).pieceCount p ≤ b.pieceCount p := by
  intro legal
  simp [apply, Board.set, Board.pieceCount, Fintype.card, Finset.univ]
  by_cases h₁ : m.stop = pos'

theorem Move.apply_legal {b : Board n} {m : Move n} :
    b.Legal → m.Legal b → (m.apply b).Legal := by
  intros b_legal m_legal
  constructor
  case rookCount =>
    intros
    transitivity
    apply m.apply_pieceCount _ m_legal
    apply b_legal.rookCount
  case kingCount =>
    intros
    transitivity
    apply m.apply_pieceCount _ m_legal
    apply b_legal.kingCount
