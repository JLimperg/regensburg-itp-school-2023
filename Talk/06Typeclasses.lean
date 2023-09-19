/- # Type Classes and the Algebraic Hierarchy -/

import Mathlib.Data.Nat.Basic

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
