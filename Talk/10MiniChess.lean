/- # Extended Example: MiniChess -/

import Mathlib

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
