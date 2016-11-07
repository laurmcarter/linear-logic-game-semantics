
module Game where

open import Prelude hiding (_&_ ; ¬_ ; _∎) renaming (⊥ to Void ; ⊤ to Unit)
import LL

open import Stream using (Stream ; _∷_)
open import Coinduction

data Player : Set where
  P O : Player

other : Player → Player
other P = O
other O = P

-- Blass Games
record Game : Set₁ where
  field
    M : Set
    s : Player
    G : Stream M → Set

module _ (G : Game) where
  open Game G

  Play : Set
  Play = Stream M

  Position : Set
  Position = List M

  turn : Position → Player
  turn = foldr (const other) s

  Strategy : Player → Set
  Strategy pl =
    (p : Position)
    → {{_ : turn p ≡ pl}}
    → M

  _follows_ : ∀ {pl} (x : Play) → Strategy pl → Set
  _follows_ {pl} x σ =
    (i : Nat)
    → let py = Stream.splitAt i x
          p  = fst py
          y  = snd py
      in {{_ : turn p ≡ pl}}
         → Stream.head y ≡ σ p
