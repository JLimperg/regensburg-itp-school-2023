/- # Type Classes and the Algebraic Hierarchy -/

import Mathlib

namespace TC

class Mul (α : Type u) where
  mul : α → α → α

instance : Mul ℕ where
  mul := Nat.mul

example (x y : ℕ) : ℕ :=
  Mul.mul x y

instance : Mul ℤ where
  mul := Int.mul

example (x y : ℤ) : ℤ :=
  Mul.mul x y

local infixl : 70 (priority := high) "*" => Mul.mul

example (x y : ℕ) : ℕ :=
  x * y

example (x y : ℤ) : ℤ :=
  x * y

def square [Mul α] (x : α) : α :=
  x * x

example (x : ℕ) : ℕ :=
  square x

#check Mul.mul

class Semigroup (α : Type _) extends Mul α where
  mul_assoc : ∀ a b c : α, (a * b) * c = a * (b * c)

instance : Semigroup ℕ where
  mul_assoc := Nat.mul_assoc

class One (α : Type _) where
  one : α

local instance [One α] : OfNat α 1 where
  ofNat := One.one

example [One α] [Mul α] : α :=
  1 * 1

class Monoid (α : Type _) extends Semigroup α, One α where
  one_mul : ∀ a : α, 1 * a = a
  mul_one : ∀ a : α, a * 1 = a

example [Monoid α] (a b c : α) : a * (1 * b * c) = a * b * c := by
  rw [Monoid.one_mul, Semigroup.mul_assoc]

#check Module

#synth AddMonoid ℕ
#synth Ring ℕ
#instances Ring

end TC
