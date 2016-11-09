
module Petri where

open import Prelude
open import Matrix

record Desc : Set where
  field
    {P T} : Nat
    I O   : Matrix Nat (P ∷ T ∷ [])
  Place Transition : Set
  Place      = Fin P
  Transition = Fin T

  inWeight : Place → Transition → Nat
  inWeight p t = indexMatrix (p ∷ t ∷ []) I

  outWeight : Transition → Place → Nat
  outWeight t p = indexMatrix (p ∷ t ∷ []) O

  InputsP OutputsP : Place → Vec Nat T
  InputsT OutputsT : Transition → Vec Nat P

  InputsP p = getMatrix $ sliceMatrix (! p ∷ ∙ ∷ []) I
  OutputsP p = getMatrix $ sliceMatrix (! p ∷ ∙ ∷ []) O

  InputsT t = getMatrix $ sliceMatrix (∙ ∷ ! t ∷ []) I
  OutputsT t = getMatrix $ sliceMatrix (∙ ∷ ! t ∷ []) O

record Petri : Set where
  field
    N : Desc
    M : Vec Nat (Desc.P N)
  open Desc N public

  Enabled : Transition → Vec Nat P → Set
  Enabled t = AllVec (uncurry _≤_) ∘ zipVec _,_ (InputsT t)

{-
record Petri : Set where
  field
    {P T} : Nat
    I O : Matrix Bool (P ∷ T ∷ [])

  Place Transition : Set
  Place      = Fin P
  Transition = Fin T

  PlaceIn PlaceOut : (p : Place) → Vec Bool T
  PlaceIn  p = getMatrix $ sliceMatrix (! p ∷ ∙ ∷ []) I
  PlaceOut p = getMatrix $ sliceMatrix (! p ∷ ∙ ∷ []) O

  TransitionIn TransitionOut : (t : Transition) → Vec Bool P
  TransitionIn  t = getMatrix $ sliceMatrix (∙ ∷ ! t ∷ []) I
  TransitionOut t = getMatrix $ sliceMatrix (∙ ∷ ! t ∷ []) O

record MarkedPetri : Set where
  field
    N : Petri
    M : Vec Nat (Petri.P N)
  open Petri N public

record Enabled (N : MarkedPetri) (t : MarkedPetri.Transition N) : Set where
  constructor enabled
  open MarkedPetri N using (P)
  Inputs : Vec (Fin P × Bool) P
  Inputs = zipVec _,_ (vecIndices _) (MarkedPetri.TransitionIn N t)
  field
    getEnabled : AllVec (uncurry λ p b → if b then indexVec (MarkedPetri.M N) p > 0 else ⊤) Inputs
open Enabled {{...}}

fire : (N : MarkedPetri) (t : MarkedPetri.Transition N) {{_ : Enabled N t}} → MarkedPetri
fire N t {{e}} =
  record N
  { M = {!!}
  }
-}
