/- # Type Classes and the Algebraic Hierarchy -/

import Mathlib.Algebra.Module.Basic

namespace TC

class Mul (α : Type u) where
  mul : α → α → α

local infixl : 70 (priority := high) "*" => Mul.mul

example [Mul α] (x y : α) : α :=
  x * y

instance : Mul ℕ where
  mul := Nat.mul

example (x y : ℕ) : ℕ :=
  x + y

class One (α : Type u) where
  one : α

local instance [One α] : OfNat α 1 where
  ofNat := One.one

example [One α] [Mul α] : α :=
  1 * 1

def npowRec [One M] [Mul M] : ℕ → M → M
  | 0, _ => 1
  | n + 1, a => a * npowRec n a

class MulOneClass (M : Type u) extends One M, Mul M where
  one_mul : ∀ a : M, 1 * a = a
  mul_one : ∀ a : M, a * 1 = a

example [MulOneClass α] (a : α) : 1 * 1 * a = a := by
  rw [MulOneClass.one_mul, MulOneClass.one_mul]

class Semigroup (G : Type u) extends Mul G where
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)

class Monoid (M : Type u) extends Semigroup M, MulOneClass M where
  npow : ℕ → M → M := npowRec
  npow_zero : ∀ x, npow 0 x = 1 := by intros; rfl
  npow_succ : ∀ (n : ℕ) (x), npow (n + 1) x = x * npow n x := by intros; rfl

example [Monoid α] (a b c : α) : a * (1 * b * c) = a * b * c := by
  rw [MulOneClass.one_mul, Semigroup.mul_assoc]

#check Module

end TC
