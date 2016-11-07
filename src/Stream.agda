
module Stream where

open import Prelude hiding (drop ; take ; splitAt ; map ; foldl ; index)
open import Coinduction

infixr 5 _∷_
data Stream {a} (A : Set a) : Set a where
  _∷_ : (x : A)
      → (xs : ∞ (Stream A))
      → Stream A

head : ∀ {a} {A : Set a}
     → Stream A
     → A
head (x ∷ xs) = x

tail : ∀ {a} {A : Set a}
     → Stream A
     → Stream A
tail (x ∷ xs) = ♭ xs

index : ∀ {a} {A : Set a}
      → Nat
      → Stream A
      → A
index zero    = head
index (suc n) = index n ∘ tail

splitAt : ∀ {a} {A : Set a}
        → Nat
        → Stream A
        → List A × Stream A
splitAt zero    xs       = [] , xs
splitAt (suc n) (x ∷ xs) = first (x ∷_) (splitAt n (♭ xs))

take : ∀ {a} {A : Set a}
     → Nat
     → Stream A
     → List A
take n = fst ∘ splitAt n

drop : ∀ {a} {A : Set a}
     → Nat
     → Stream A
     → Stream A
drop n = snd ∘ splitAt n

infixr 5 _⋎_
_⋎_ : ∀ {a} {A : Set a} → Stream A → Stream A → Stream A
(x ∷ xs) ⋎ ys = x ∷ ♯ (ys ⋎ ♭ xs)

infixr 5 _++ˢ_
_++ˢ_ : ∀ {a} {A : Set a}
      → List A
      → Stream A
      → Stream A
[]       ++ˢ ys = ys
(x ∷ xs) ++ˢ ys = x ∷ ♯ (xs ++ˢ ys)

map : ∀ {a b} {A : Set a} {B : Set b}
    → (A → B)
    → Stream A
    → Stream B
map f (x ∷ xs) = f x ∷ ♯ map f (♭ xs)

{-# NON_TERMINATING #-}
foldl : ∀ {a b} {A : Set a} {B : Set b}
      → (A → ∞ B → ∞ B)
      → Stream A
      → ∞ B
foldl f (x ∷ xs) = f x (foldl f (♭ xs))
