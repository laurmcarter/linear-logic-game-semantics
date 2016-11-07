
module BlassGame where

open import Prelude

data Role : Set where
  P O : Role

record Game (I : Set) : Set where
  coinductive
  field
    history : List I
    start   : Role
    move    : I → Game I
