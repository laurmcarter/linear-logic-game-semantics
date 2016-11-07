{-# OPTIONS --no-positivity-check #-}

module Theseus where

open import Prelude hiding (_+_ ; unit)
open import Container.List

{-# NON_TERMINATING #-}
fix : ∀ {a} {A : Set a}
    → (A → A)
    → A
fix f = x
  where
  x = f x

infixr 2 _+_
_+_ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
_+_ = Either

infixr 3 _⊕_
infixr 4 _⊗_
data U : Set where
  𝟘 𝟙     : U
  _⊕_ _⊗_ : (A B : U) → U
  μ_      : (f : U → U)
          → U

⟦_⟧ : U → Set
record Rec (f : U → U) : Set where
  coinductive
  constructor wrap
  field
    unwrap : ⟦ f (μ f) ⟧
open Rec public

⟦ 𝟘     ⟧ = ⊥
⟦ 𝟙     ⟧ = ⊤
⟦ A ⊕ B ⟧ = ⟦ A ⟧ + ⟦ B ⟧
⟦ A ⊗ B ⟧ = ⟦ A ⟧ × ⟦ B ⟧
⟦ μ f   ⟧ = Rec f

data Iso : U → U → Set where
  ⊕id     : ∀ {A}     → Iso (𝟘 ⊕ A)       A
  ⊕comm   : ∀ {A B}   → Iso (A ⊕ B)       (B ⊕ A)
  ⊕assoc  : ∀ {A B C} → Iso ((A ⊕ B) ⊕ C) (A ⊕ (B ⊕ C))
  ⊗id     : ∀ {A}     → Iso (𝟙 ⊗ A)       A
  ⊗comm   : ∀ {A B}   → Iso (A ⊗ B)       (B ⊗ A)
  ⊗assoc  : ∀ {A B C} → Iso ((A ⊗ B) ⊗ C) (A ⊗ (B ⊗ C))
  distrib : ∀ {A B C} → Iso (A ⊗ (B ⊕ C)) ((A ⊗ B) ⊕ (A ⊗ C))
  annihil : ∀ {A}     → Iso (𝟘 ⊗ A)       𝟘
  unroll  : ∀ {f}     → Iso (μ f)         (f (μ f))

infix 2 _↔_
infixr 1 _▸_
data _↔_ : U → U → Set where
  I      : ∀ {A}
         → A ↔ A
  _⁻¹    : ∀ {A B}
         → A ↔ B
         → B ↔ A
  _▸_    : ∀ {A B C}
         → A ↔ B
         → B ↔ C
         → A ↔ C
  _⊕_    : ∀ {A B C D}
         → A ↔ B
         → C ↔ D
         → A ⊕ C ↔ B ⊕ D
  _⊗_    : ∀ {A B C D}
         → A ↔ B
         → C ↔ D
         → A ⊗ C ↔ B ⊗ D
  ∙      : ∀ {A B}
         → Iso A B
         → A ↔ B

invert : ∀ {A B} → A ↔ B → B ↔ A
invert I       = I
invert (i ⁻¹)  = i
invert (i ▸ j) = invert j ▸ invert i
invert (i ⊕ j) = invert i ⊕ invert j
invert (i ⊗ j) = invert i ⊗ invert j
invert i       = i ⁻¹

𝟚 : U
𝟚 = μ λ x → 𝟙 ⊕ 𝟙

ℕ : U
ℕ = μ λ x → 𝟙 ⊕ x

Tree : U
Tree = μ λ x → ℕ ⊕ x ⊗ x

id𝟚 : 𝟚 ↔ 𝟚
id𝟚 =
  I

not𝟚 : 𝟚 ↔ 𝟚
not𝟚 =
  ∙ unroll
  ▸ ∙ ⊕comm
  ▸ ∙ unroll ⁻¹

expand𝟚 : ∀ {A} → 𝟚 ⊗ A ↔ A ⊕ A
expand𝟚 =
    ∙ ⊗comm
  ▸ I ⊗ ∙ unroll
  ▸ ∙ distrib
  ▸ (∙ ⊗comm ▸ ∙ ⊗id) ⊕ (∙ ⊗comm ▸ ∙ ⊗id)

fold𝟚 : ∀ {A} → A ⊕ A ↔ 𝟚 ⊗ A
fold𝟚 =
  (∙ ⊗id ⁻¹ ▸ ∙ ⊗comm) ⊕ (∙ ⊗id ⁻¹ ▸ ∙ ⊗comm)
  ▸ ∙ distrib ⁻¹
  ▸ I ⊗ ∙ unroll ⁻¹
  ▸ ∙ ⊗comm

expandℕ : ℕ ↔ ℕ ⊕ 𝟙
expandℕ =
  ∙ unroll
  ▸ ∙ ⊕comm

foldℕ : ℕ ⊕ 𝟙 ↔ ℕ
foldℕ =
  ∙ ⊕comm
  ▸ ∙ unroll ⁻¹

treeUnwind : Tree ↔ Tree ⊗ Tree ⊕ (𝟚 ⊕ ℕ)
treeUnwind =
  ∙ unroll
  ▸ ∙ ⊕comm
  ▸ I ⊕ (expandℕ
          ▸ ∙ ⊕comm
          ▸ I ⊕ (expandℕ ▸ ∙ ⊕comm)
          ▸ ∙ ⊕assoc ⁻¹
          ▸ ∙ unroll ⁻¹ ⊕ I
         )

fwdIso : ∀ {A B} → Iso A B → ⟦ A ⟧ → ⟦ B ⟧
fwdIso ⊕id     = either ⊥-elim id
fwdIso ⊕comm   = either right left
fwdIso ⊕assoc  = either (either left (right ∘ left)) (right ∘ right)
fwdIso ⊗id     = snd
fwdIso ⊗comm   = uncurry (flip _,_)
fwdIso ⊗assoc  = uncurry (uncurry λ x y z → x , (y , z))
fwdIso distrib = uncurry λ x → either (λ y → left (x , y)) (λ z → right (x , z))
fwdIso annihil = fst
fwdIso unroll  = unwrap

bwdIso : ∀ {A B} → Iso A B → ⟦ B ⟧ → ⟦ A ⟧
bwdIso ⊕id     = right
bwdIso ⊕comm   = either right left
bwdIso ⊕assoc  = either (left ∘ left) (either (left ∘ right) right)
bwdIso ⊗id     = tt ,_
bwdIso ⊗comm   = uncurry (flip _,_)
bwdIso ⊗assoc  = uncurry λ x → uncurry λ y z → (x , y) , z
bwdIso distrib = either (uncurry λ x y → x , left y) (uncurry λ x z → x , right z)
bwdIso annihil = ⊥-elim
bwdIso unroll  = wrap

fwd : ∀ {A B} → A ↔ B → ⟦ A ⟧ → ⟦ B ⟧
bwd : ∀ {A B} → A ↔ B → ⟦ B ⟧ → ⟦ A ⟧

fwd I       = id
fwd (i ⁻¹)  = bwd i
fwd (i ▸ j) = fwd j ∘ fwd i
fwd (i ⊕ j) = either (left ∘ fwd i) (right ∘ fwd j)
fwd (i ⊗ j) = fwd i *** fwd j
fwd (∙ i)   = fwdIso i

bwd I       = id
bwd (i ⁻¹)  = fwd i
bwd (i ▸ j) = bwd i ∘ bwd j
bwd (i ⊕ j) = either (left ∘ bwd i) (right ∘ bwd j)
bwd (i ⊗ j) = bwd i *** bwd j
bwd (∙ i)   = bwdIso i
