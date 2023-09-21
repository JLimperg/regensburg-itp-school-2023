/- # Functional Programming -/

import Mathlib.Tactic

namespace Examples

/- ## Inductive Types -/

inductive Nat where
  | zero : Nat
  | succ : Nat → Nat

/- ## Structures -/

structure Point where
  x : Nat
  y : Nat

#check Point.mk
#check Point.x
#check Point.y

/- ## Definitions -/

def one : Nat :=
  Nat.succ Nat.zero

def add_two : Nat → Nat :=
  fun (n : Nat) => Nat.succ (Nat.succ n)

def add_two₂ : Nat → Nat
  | n => Nat.succ (Nat.succ n)

def add_two₃ (n : Nat) : Nat :=
  Nat.succ (Nat.succ n)

def add : Nat → Nat → Nat
  | m, Nat.zero => m
  | m, Nat.succ n => Nat.succ (add m n)

def add₂ (m n : Nat) : Nat :=
  match m, n with
  | m, Nat.zero   => m
  | m, Nat.succ n => Nat.succ (add₂ m n)

/- ## Namespaces -/

open Nat in
def one₂ : Nat :=
  succ zero

namespace Nat

def one : Nat :=
  succ zero

#check one

def add : Nat → Nat → Nat
  | m, zero => m
  | m, succ n => succ (add m n)

end Nat

def Nat.one₂ : Nat :=
  succ zero

/- ## Dot Notation -/

def add₃ : Nat → Nat → Nat
  | m, .zero => m
  | m, .succ n => .succ (add₃ m n)

def mul : Nat → Nat → Nat
  | _, .zero => .zero
  | m, .succ n => m.add (mul m n)

def two : Nat :=
  .succ (.succ .zero)

/- ## Notations -/

local infixl : 50 (priority := high) "+" => add
local infixl : 55 (priority := high) "*" => mul

example : one * (one + one) = two := rfl

def Nat.ofNat : _root_.Nat → Nat
  | .zero => .zero
  | .succ n => .succ (ofNat n)

instance : OfNat Nat n where
  ofNat := .ofNat n

example : (1 : Nat) * (1 + 1) = 2 := rfl

/- ## Implicit Arguments -/

def reverse {α} : List α → List α
  | .nil => .nil
  | .cons x xs => reverse xs ++ [x]

example {α} (xs : List α) : List α :=
  reverse xs

example {α} (xs : List α) : List α :=
  @reverse α xs

example {α} (xs : List α) : List α :=
  reverse (α := α) xs

def reverse₂ : List α → List α
  | .nil => .nil
  | .cons x xs => reverse xs ++ [x]

end Examples
