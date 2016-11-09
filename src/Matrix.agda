
module Matrix where

open import Prelude

J : ∀ {a c} {A : Set a} (C : (x y : A) → x ≡ y → Set c)
  → (∀ x → C x x refl)
  → ∀ {x y}
  → (eq : x ≡ y)
  → C x y eq
J C c refl = c _

congᵈ : ∀ {a b} {A : Set a} {B : A → Set b}
      → (f : ∀ x → B x)
      → {x y : A}
      → (p : x ≡ y)
      → transport B p (f x) ≡ f y
congᵈ {B = B} f =
  J (λ x y p → transport B p (f x) ≡ f y) λ x →
  refl

transportᵈ : ∀ {a b c} {A : Set a}
           → {B : A → Set b}
           → (C : ∀ x → B x → Set c)
           → ∀ {x y}
           → (p : x ≡ y)
           → {α : B x} {β : B y}
           → (q : transport B p α ≡ β)
           → C x α → C y β
transportᵈ C refl refl = id

pattern ∙   = nothing
pattern ! a = just a

instance
  NumberMaybe : ∀ {a} {A : Set a}
              → {{NumberA : Number A}}
              → Number (Maybe A)
  NumberMaybe {{NumberA}} = record
    { Constraint = Number.Constraint NumberA
    ; fromNat    = λ n → just (Number.fromNat NumberA n)
    }

infixr 5 _∷_
data AllVec {a b} {A : Set a} (B : A → Set b) : ∀ {n} → Vec A n → Set (a ⊔ b) where
  []  : AllVec B []
  _∷_ : ∀ {x n} {xs : Vec A n}
      → B x
      → AllVec B xs
      → AllVec B (x ∷ xs)

mapAllVec : ∀ {a b c} {A : Set a} {B : A → Set b} {C : A → Set c}
          → (∀ {x} → B x → C x)
          → ∀ {n} {xs : Vec A n}
          → AllVec B xs → AllVec C xs
mapAllVec f [] = []
mapAllVec f (y ∷ ys) = f y ∷ mapAllVec f ys

instance
  AllVec[] : ∀ {a b} {A : Set a} {B : A → Set b} → AllVec B []
  AllVec[] = []

  AllVec∷ : ∀ {a b} {A : Set a} {B : A → Set b}
          → {x : A} {n : Nat} {xs : Vec A n}
          → {{b : B x}}
          → {{bs : AllVec B xs}}
          → AllVec B (x ∷ xs)
  AllVec∷ {{b}} {{bs}} = b ∷ bs

indexAllVec : ∀ {a b} {A : Set a} {B : A → Set b} {n : Nat} {xs : Vec A n}
            → AllVec B xs
            → (i : Fin n)
            → B (indexVec xs i)
indexAllVec (x ∷ xs) zero    = x
indexAllVec (x ∷ xs) (suc i) = indexAllVec xs i

foldrVec : ∀ {a b} {A : Set a} {B : Set b}
         → (A → B → B)
         → B
         → ∀ {n}
         → Vec A n
         → B
foldrVec f z []       = z
foldrVec f z (x ∷ xs) = f x (foldrVec f z xs)

indNat : ∀ {c} (C : Nat → Set c)
       → (cz : C 0)
       → (cs : ∀ {n} → C n → C (suc n))
       → (n : Nat)
       → C n
indNat C cz cs zero    = cz
indNat C cz cs (suc n) = cs (indNat C cz cs n)

indVec : ∀ {a c} {A : Set a}
       → (C : ∀ {n} → Vec A n → Set c)
       → (cz : C [])
       → (cs : (x : A) → ∀ {n} {xs : Vec A n} → C xs → C (x ∷ xs))
       → ∀ {n}
       → (xs : Vec A n)
       → C xs
indVec C cz cs []       = cz
indVec C cz cs (x ∷ xs) = cs x (indVec C cz cs xs)

zipVec : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
       → (A → B → C)
       → ∀ {n}
       → Vec A n
       → Vec B n
       → Vec C n
zipVec f []       []       = []
zipVec f (x ∷ xs) (y ∷ ys) = f x y ∷ zipVec f xs ys

vecIndices : (n : Nat)
           → Vec (Fin n) n
vecIndices zero    = []
vecIndices (suc n) = zero ∷ (suc <$> vecIndices n)

mapVec : ∀ {a b} {A : Set a} {B : Set b}
       → (A → B)
       → ∀ {n}
       → Vec A n → Vec B n
mapVec f []       = []
mapVec f (x ∷ xs) = f x ∷ mapVec f xs

mapVecAt : ∀ {a} {A : Set a}
         → (A → A)
         → ∀ {n}
         → Fin n
         → Vec A n → Vec A n
mapVecAt f zero    (x ∷ xs) = f x ∷ xs
mapVecAt f (suc i) (x ∷ xs) = x ∷ mapVecAt f i xs

imapVec : ∀ {a b} {A : Set a} {B : Set b}
        → ∀ {n}
        → (Fin n → A → B)
        → Vec A n → Vec B n
imapVec f []       = []
imapVec f (x ∷ xs) = f zero x ∷ imapVec (f ∘ suc) xs

genVec : ∀ {a} {A : Set a}
       → (n : Nat)
       → (Fin n → A)
       → Vec A n
genVec n f = mapVec f (vecIndices n)

Dimension : Set
Dimension = Nat
Dimensions : Nat → Set
Dimensions = Vec Dimension

record Matrix {dim a} (A : Set a) (ds : Dimensions dim) : Set a where
  constructor matrix
  field
    getMatrix : foldrVec (flip Vec) A ds
open Matrix public

mapMatrix : ∀ {dim a b} {A : Set a} {B : Set b} {ds : Dimensions dim}
          → (A → B)
          → Matrix A ds
          → Matrix B ds
mapMatrix {ds = []}     f (matrix x) = matrix (f x)
mapMatrix {ds = d ∷ ds} f (matrix m) = matrix (mapVec (getMatrix ∘ mapMatrix {ds = ds} f ∘ matrix) m)

Slice : ∀ {dim} → Dimensions dim → Set
Slice = AllVec (Maybe ∘ Fin)

Index : ∀ {dim} → Dimensions dim → Set
Index = AllVec Fin

sliceDims : ∀ {dim} {ds : Dimensions dim}
          → Slice ds
          → Σ Nat Dimensions
sliceDims              []            = 0 , []
sliceDims {ds = d ∷ _} (nothing ∷ j) = suc *** (d ∷_) $ sliceDims j
sliceDims              (just i  ∷ j) = sliceDims j

sliced : ∀ {dim} {ds : Dimensions dim} (i : Slice ds) → Dimensions (fst (sliceDims i))
sliced = snd ∘ sliceDims

sliceMatrix : ∀ {dim a} {A : Set a} {ds : Dimensions dim}
            → (i : Slice ds)
            → Matrix A ds
            → Matrix A (sliced i)
sliceMatrix []            m          = m
sliceMatrix (nothing ∷ j) (matrix m)
  with sliceDims j   | getMatrix ∘ sliceMatrix j ∘ matrix <$> m
...  | dim' , ds' | m' = matrix m'
sliceMatrix (just i  ∷ j) (matrix m) = sliceMatrix j (matrix (indexVec m i))

infixr 4 _⧸_
_⧸_ : ∀ {dim a} {A : Set a} {ds : Dimensions dim}
    → (i : Slice ds)
    → Matrix A ds
    → Matrix A (sliced i)
_⧸_ = sliceMatrix

allSliceDims : ∀ {dim} {ds : Dimensions dim}
             → (i : Index ds)
             → sliceDims (mapAllVec just i) ≡ (0 , [])
allSliceDims []      = refl
allSliceDims (i ∷ j) = allSliceDims j

allSlice : ∀ {dim} {ds : Dimensions dim}
         → (i : Index ds)
         → transport (Dimensions ∘ fst) (allSliceDims i) (sliced (mapAllVec just i))
         ≡ []
allSlice i = congᵈ snd (allSliceDims i)

indexMatrix : ∀ {dim a} {A : Set a} {ds : Dimensions dim}
            → (i : Index ds)
            → Matrix A ds
            → A
indexMatrix i =
  getMatrix
  ∘ transportᵈ (λ _ → Matrix _)
    (allSliceDims i)
    (allSlice i)
  ∘ sliceMatrix (mapAllVec just i)

matrixIndices : ∀ {dim}
              → (ds : Dimensions dim)
              → Matrix (Index ds) ds
matrixIndices =
  indVec (λ ds → Matrix (Index ds) ds)
  (matrix [])
  (λ d m →
   matrix
   $ genVec d λ x →
     getMatrix
     $ mapMatrix (x ∷_) m)

genMatrix : ∀ {a} {A : Set a} {dim}
          → (ds : Dimensions dim)
          → (Index ds → A)
          → Matrix A ds
genMatrix ds f = mapMatrix f (matrixIndices ds)

foldrMatrix : ∀ {a b} {A : Set a} {B : Set b}
            → (A → B → B) → B
            → ∀ {dim} {ds : Dimensions dim}
            → Matrix A ds
            → B
foldrMatrix f z {ds = ds} =
  (_$ z)
  ∘ indVec (λ ds → Matrix _ ds → _ → _)
    (f ∘ getMatrix)
    (λ _ k m b → foldrVec (k ∘ matrix) b (getMatrix m))
    ds

