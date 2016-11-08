
module Concurrent where

open import Prelude hiding (¬_ ; _&_) renaming (_,_ to _·_)

infixr 6 _⊕_ _⅋_
infixr 7 _⊗_ _&_
data U : Set where
  ¬_              : U → U
  _⊗_ _⊕_ _&_ _⅋_ : U → U → U

Ctx : Set
Ctx = List U

infix 1 _─_
data _─_ : Ctx → Ctx → Set where
  ID   : ∀ {A}
       → [] ─ (A ∷ ¬ A ∷ [])
  CUT  : ∀ {A}
       → (A ∷ ¬ A ∷ []) ─ []
  [⊗]  : ∀ {A B}
       → (A ∷ B ∷ []) ─ (A ⊗ B ∷ [])
  [⅋]  : ∀ {A B}
       → (A ∷ B ∷ []) ─ (A ⅋ B ∷ [])
  [⊕]₁ : ∀ {A B}
       → (A ∷ []) ─ (A ⊕ B ∷ [])
  [⊕]₂ : ∀ {A B}
       → (B ∷ []) ─ (A ⊕ B ∷ [])
  [&]  : ∀ {A B}
       → (A ∷ B ∷ []) ─ (A & B ∷ [])

infix 2 _«_»_
data _«_»_ {a} {A : Set a} : List A → List A → List A → Set a where
  [] : [] « [] » []
  «_ : ∀ {x xs l r}
     → l « xs » r
     → x ∷ l « x ∷ xs » r
  »_ : ∀ {x xs l r}
     → l « xs » r
     → l « x ∷ xs » x ∷ r
