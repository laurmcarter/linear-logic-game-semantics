
module Petri where

open import Prelude
open import Container.List

infixr 5 _∷_
data AllVec {a b} {A : Set a} (B : A → Set b) : ∀ {n} → Vec A n → Set (a ⊔ b) where
  instance
    []  : AllVec B []
  _∷_ : ∀ {x n} {xs : Vec A n}
      → B x
      → AllVec B xs
      → AllVec B (x ∷ xs)

instance
  AllVec∷ : ∀ {a b} {A : Set a} {B : A → Set b} {x : A} {n : Nat} {xs : Vec A n}
          → {{b₀ : B x}} {{bs : AllVec B xs}}
          → AllVec B (x ∷ xs)
  AllVec∷ {{b₀}} {{bs}} = b₀ ∷ bs

Matrix : Set → List Nat → Set
Matrix A = foldr (flip Vec) A

indexMatrix : ∀ {A ds}
            → Matrix A ds
            → All Fin ds
            → A
indexMatrix m []      = m
indexMatrix m (i ∷ j) = indexMatrix (indexVec m i) j

record Petri : Set where
  field
    {P T} : Nat
    I O : Matrix Bool (P ∷ T ∷ [])

module _ (N : Petri) where
  open Petri N

  Place Transition : Set
  Place      = Fin P
  Transition = Fin T

record Enabled (N : Petri) (t : Transition N) : Set where
  field
    enabled : AllVec {!!} {!!}

record MarkedPetri : Set where
  field
    N : Petri
    M : Place N → Nat
  open Petri N
