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
