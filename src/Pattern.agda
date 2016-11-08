
module Pattern where

open import Prelude hiding (unit ; id ; true ; false ; first ; second)
open import Container.List
open import Coinduction

add-zero : (x : Nat) → x + 0 ≡ x
add-zero zero    = refl
add-zero (suc x) = cong suc (add-zero x)

add-suc : (x y : Nat) → x + suc y ≡ suc (x + y)
add-suc zero    y = refl
add-suc (suc x) y = cong suc (add-suc x y)

add-comm : (x y : Nat) → x + y ≡ y + x
add-comm zero    y = sym (add-zero y)
add-comm (suc x) y = trans (cong suc (add-comm x y)) (sym (add-suc y x))

splitFin : (x y : Nat) → Fin (x + y) → Either (Fin x) (Fin y)
splitFin zero    y n       = right n
splitFin (suc x) y zero    = left zero
splitFin (suc x) y (suc n) = either (left ∘ suc) right $ splitFin x y n

infixr 6 _⊕_
infixr 7 _⊗_
data U (x : Nat) : Set where
  𝟘 𝟙   : U x
  _⊗_   : U x → U x → U x
  _⊕_   : U x → U x → U x
  μ_    : U (suc x)
        → U x
  ⟨_⟩   : Fin x
        → U x

𝕌 : Set
𝕌 = U 0

weaken : ∀ {x} → Fin x → Fin (suc x)
weaken zero    = zero
weaken (suc x) = suc (weaken x)

weakenN : ∀ {y} (x : Nat) → Fin y → Fin (x + y)
weakenN zero    y = y
weakenN (suc x)   = weaken ∘ weakenN x

mapU : ∀ {x y} → (Fin x → Fin y) → U x → U y
mapU f 𝟘       = 𝟘
mapU f 𝟙       = 𝟙
mapU f (A ⊗ B) = mapU f A ⊗ mapU f B
mapU f (A ⊕ B) = mapU f A ⊕ mapU f B
mapU f (μ F)   = μ mapU (λ { zero → zero ; (suc x) → suc (f x) }) F
mapU f ⟨ x ⟩   = ⟨ f x ⟩

↓_ : ∀ {x} → U x → U (suc x)
↓_ = mapU suc

↑_ : ∀ {x} → 𝕌 → U x
↑_ {x} = transport U (add-zero x) ∘ mapU (weakenN x)

substUnder : ∀ {x} (n : Nat) → U (n + x) → U (n + suc x) → U (n + x)
substUnder n α 𝟘       = 𝟘
substUnder n α 𝟙       = 𝟙
substUnder n α (A ⊗ B) = substUnder n α A ⊗ substUnder n α B
substUnder n α (A ⊕ B) = substUnder n α A ⊕ substUnder n α B
substUnder n α (μ F)   = μ (substUnder (suc n) (↓ α) F)
substUnder {x = x'} n α ⟨ x  ⟩ with splitFin n (suc _) x
...| left  y       = ⟨ transport Fin (add-comm _ n) (weakenN x' y) ⟩
...| right zero    = α
...| right (suc z) = ⟨ weakenN n z ⟩

subst : ∀ {x} → U x → U (suc x) → U x
subst = substUnder 0

record Denotation {a} (A : Set a) e d : Set (a ⊔ lsuc (e ⊔ d)) where
  field
    Env : Set e
    ⟦_⟧ : A → {{env : Env}} → Set d
open Denotation {{...}} public

infixr 1 _,_
data El {x : Nat} : U x → Set where
  unit : El 𝟙
  inl  : ∀ {A B}
       → El A
       → El (A ⊕ B)
  inr  : ∀ {A B}
       → El B
       → El (A ⊕ B)
  _,_  : ∀ {A B}
       → El A
       → El B
       → El (A ⊗ B)
  roll : ∀ {F}
       → El (subst (μ F) F)
       → El (μ F)

instance
  DenotationU : ∀ {x} → Denotation (U x) lzero lzero
  DenotationU {x} = record
    { Env = ⊤
    ; ⟦_⟧ = λ A → El A
    }

data Axiom {x : Nat} : U x → U x → Set where
  ⊕id     : ∀ {A}
          → Axiom (𝟘 ⊕ A) A
  ⊕comm   : ∀ {A B}
          → Axiom (A ⊕ B) (B ⊕ A)
  ⊕assoc  : ∀ {A B C}
          → Axiom ((A ⊕ B) ⊕ C) (A ⊕ (B ⊕ C))
  ⊗id     : ∀ {A}
          → Axiom (𝟙 ⊗ A) A
  ⊗comm   : ∀ {A B}
          → Axiom (A ⊗ B) (B ⊗ A)
  ⊗assoc  : ∀ {A B C}
          → Axiom ((A ⊗ B) ⊗ C) (A ⊗ (B ⊗ C))
  distrib : ∀ {A B C}
          → Axiom (A ⊗ (B ⊕ C)) ((A ⊗ B) ⊕ (A ⊗ C))
  annihil : ∀ {A}
          → Axiom (𝟘 ⊗ A) 𝟘
  roll    : ∀ {F}
          → Axiom (subst (μ F) F) (μ F)

infix 1 _↔_
infixr 5 _▸_
data _↔_ {x : Nat} : U x → U x → Set where
  id  : ∀ {A}
      → A ↔ A
  _⁻¹ : ∀ {A B}
      → A ↔ B
      → B ↔ A
  _▸_ : ∀ {A B C}
      → A ↔ B
      → B ↔ C
      → A ↔ C
  _⊕_ : ∀ {A B C D}
      → A ↔ B
      → C ↔ D
      → A ⊕ C ↔ B ⊕ D
  _⊗_ : ∀ {A B C D}
      → A ↔ B
      → C ↔ D
      → A ⊗ C ↔ B ⊗ D
  ⟨_⟩ : ∀ {A B}
      → Axiom A B
      → A ↔ B

fwdAxm : ∀ {x} {A B : U x} → Axiom A B → ⟦ A ⟧ → ⟦ B ⟧
bwdAxm : ∀ {x} {A B : U x} → Axiom A B → ⟦ B ⟧ → ⟦ A ⟧

fwdAxm ⊕id (inl ())
fwdAxm ⊕id (inr x) = x
fwdAxm ⊕comm (inl x) = inr x
fwdAxm ⊕comm (inr x) = inl x
fwdAxm ⊕assoc (inl (inl x)) = inl x
fwdAxm ⊕assoc (inl (inr x)) = inr (inl x)
fwdAxm ⊕assoc (inr x)       = inr (inr x)
fwdAxm ⊗id (unit , x) = x
fwdAxm ⊗comm   (x , y) = y , x
fwdAxm ⊗assoc  ((x , y) , z) = x , (y , z)
fwdAxm distrib (x , inl y) = inl (x , y)
fwdAxm distrib (x , inr y) = inr (x , y)
fwdAxm annihil (() , _)
fwdAxm roll    x = roll x

bwdAxm ⊕id     x = inr x
bwdAxm ⊕comm (inl x) = inr x
bwdAxm ⊕comm (inr x) = inl x
bwdAxm ⊕assoc (inl x) = inl (inl x)
bwdAxm ⊕assoc (inr (inl x)) = inl (inr x)
bwdAxm ⊕assoc (inr (inr x)) = inr x
bwdAxm ⊗id     x = unit , x
bwdAxm ⊗comm   (x , y) = y , x
bwdAxm ⊗assoc  (x , (y , z)) = (x , y) , z
bwdAxm distrib (inl (x , y)) = x , inl y
bwdAxm distrib (inr (x , y)) = x , inr y
bwdAxm annihil ()
bwdAxm roll    (roll x) = x

fwd : ∀ {x} {A B : U x} → A ↔ B → ⟦ A ⟧ → ⟦ B ⟧
bwd : ∀ {x} {A B : U x} → A ↔ B → ⟦ B ⟧ → ⟦ A ⟧

fwd id      x       = x
fwd (i ⁻¹)          = bwd i
fwd (i ▸ j)         = fwd j ∘ fwd i
fwd (i ⊕ j) (inl x) = inl (fwd i x)
fwd (i ⊕ j) (inr x) = inr (fwd j x)
fwd (i ⊗ j) (x , y) = fwd i x , fwd j y
fwd ⟨ a ⟩           = fwdAxm a

bwd id      x       = x
bwd (i ⁻¹)          = fwd i
bwd (i ▸ j)         = bwd i ∘ bwd j
bwd (i ⊕ j) (inl x) = inl (bwd i x)
bwd (i ⊕ j) (inr x) = inr (bwd j x)
bwd (i ⊗ j) (x , y) = bwd i x , bwd j y
bwd ⟨ a ⟩           = bwdAxm a

𝟚 : 𝕌
𝟚 = μ (𝟙 ⊕ 𝟙)

ℕ : 𝕌
ℕ = μ (𝟙 ⊕ ⟨ 0 ⟩)

𝔽' : Nat → U 1
𝔽' zero          = 𝟘
𝔽' (suc zero)    = 𝟙
𝔽' (suc (suc n)) = 𝟙 ⊕ 𝔽' (suc n)

𝔽 : Nat → 𝕌
𝔽 = μ_ ∘ 𝔽'

Tree : ∀ {x} → U x → U x
Tree A = μ (↓ A ⊕ ⟨ 0 ⟩ ⊗ ⟨ 0 ⟩)

pattern false = roll (inl unit)
pattern true  = roll (inr unit)

pattern ze   = roll (inl unit)
pattern su n = roll (inr n)

pattern Fst i = i ⊗ id
pattern Snd i = id ⊗ i

pattern Left  i = i ⊕ id
pattern Right i = id ⊕ i

expandBool : (A : 𝕌) → 𝟚 ⊗ A ↔ A ⊕ A
expandBool A =
  Fst (⟨ roll ⟩ ⁻¹)
  ▸ ⟨ ⊗comm ⟩
  ▸ ⟨ distrib ⟩
  ▸ (⟨ ⊗comm ⟩ ▸ ⟨ ⊗id ⟩) ⊕ (⟨ ⊗comm ⟩ ▸ ⟨ ⊗id ⟩)

expandNat : ℕ ↔ ℕ ⊕ 𝟙
expandNat =
  ⟨ roll ⟩ ⁻¹
  ▸ ⟨ ⊕comm ⟩

unwindTree : Tree ℕ ↔ Tree ℕ ⊗ Tree ℕ ⊕ (𝟚 ⊕ ℕ)
unwindTree =
  ⟨ roll ⟩ ⁻¹
  ▸ ⟨ ⊕comm ⟩
  ▸ Right
    ( expandNat
    ▸ Left expandNat
    ▸ ⟨ ⊕assoc ⟩
    ▸ ⟨ ⊕comm ⟩
    ▸ Left ⟨ roll ⟩
    )

{-
Tree = μ x. Nat + x * x

treeUnwind :: Tree ↔ Tree * Tree + (Bool + Nat)
| Node t1 t2           ↔ Left (t1, t2)
| Leaf 0               ↔ Right (Left True)
| Leaf (Succ 0)        ↔ Right (Left False)
| Leaf (Succ (Succ n)) ↔ Right (Right n)
-}
