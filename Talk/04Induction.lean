/- # Inductive Types and Induction -/

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
