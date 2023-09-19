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
