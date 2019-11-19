------------------------------------------------------------------------
-- List utilities
------------------------------------------------------------------------

module Prelude.Lists where

open import Level            using (Level)
open import Function         using (_∘_; _∋_; case_of_)
open import Function.Inverse using (_↔_)

open import Data.Empty    using (⊥; ⊥-elim)
open import Data.Unit     using (⊤; tt)
open import Data.Product  using (_×_; _,_; map₂; proj₂; <_,_>; ∃-syntax)
open import Data.Sum      using (_⊎_; inj₁; inj₂; isInj₁; isInj₂)
open import Data.Maybe    using (Maybe; just; nothing)
open import Data.Fin      using (Fin; toℕ; fromℕ≤; inject≤; cast; inject₁; 0F)
  renaming (zero to fzero; suc to fsuc; _≟_ to _≟ᶠ_)
open import Data.Nat      using (ℕ; zero; suc; _≤_; z≤n; s≤s; pred; _<?_)
open import Data.List     using ( List; []; [_]; _∷_; _∷ʳ_; _++_; map; mapMaybe; concatMap; length
                                ; zip; sum; upTo; lookup; allFin; unzip )

open import Data.Nat.Properties using (suc-injective)

open import Data.List.Properties                           using (length-map)
open import Data.List.Membership.Propositional             using (_∈_; mapWith∈)
open import Data.List.Relation.Unary.Any                   using (here; there)
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix)

open import Relation.Nullary                      using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable            using (True)
open import Relation.Binary                       using (Decidable)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_;_∎)

------------------------------------------------------------------------
-- Indexed operations.

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c
    xs : List A

Index : List A → Set
Index = Fin ∘ length

infix 3 _‼_
_‼_ : (vs : List A) → Index vs → A
_‼_ = lookup

infix 3 _⁉_
_⁉_ : (vs : List A) → ℕ → Maybe A
[]       ⁉ _     = nothing
(x ∷ xs) ⁉ zero  = just x
(x ∷ xs) ⁉ suc n = xs ⁉ n

remove : ∀ {A : Set} → (vs : List A) → Index vs → List A
remove []       ()
remove (_ ∷ xs) fzero    = xs
remove (x ∷ vs) (fsuc f) = x ∷ remove vs f

_at_⟨_⟩ : ∀ {A : Set} → (vs : List A) → Index vs → A → List A
[]       at ()       ⟨ _ ⟩
(_ ∷ xs) at fzero    ⟨ x ⟩ = x ∷ xs
(y ∷ vs) at (fsuc f) ⟨ x ⟩ = y ∷ (vs at f ⟨ x ⟩)

_at_⟨_⟩remove_ : ∀ {A : Set} → (vs : List A) → Index vs → A → Index vs → List A
[] at () ⟨ _ ⟩remove ()
(_ ∷ vs) at fzero  ⟨ _  ⟩remove fzero  = vs
(_ ∷ vs) at fzero  ⟨ xv ⟩remove fsuc y = xv ∷ remove vs y
(_ ∷ vs) at fsuc x ⟨ xv ⟩remove fzero  = vs at x ⟨ xv ⟩
(v ∷ vs) at fsuc x ⟨ xv ⟩remove fsuc y = v ∷ vs at x ⟨ xv ⟩remove y

indices : List A → List ℕ
indices xs = upTo (length xs)

fin-indices : (xs : List A) → List (Index xs)
fin-indices = allFin ∘ length

enumerate : (xs : List A) → List (Index xs × A)
enumerate xs = zip (fin-indices xs) xs

zip-∈ : ∀ {xs : List A} {ys : List B} {x : A} {y : B}
       → (x , y) ∈ zip xs ys → (x ∈ xs) × (y ∈ ys)
zip-∈ {xs = _ ∷ xs} {_ ∷ ys} (here refl) = here refl , here refl
zip-∈ {xs = _ ∷ xs} {_ ∷ ys} (there xy∈) with zip-∈ xy∈
... | (x∈ , y∈) = there x∈ , there y∈

ix∈→x∈ : ∀ {xs : List A} {i : Index xs} {x : A}
       → (i , x) ∈ enumerate xs → x ∈ xs
ix∈→x∈ = proj₂ ∘ zip-∈

mapEnumWith∈ : (xs : List A) → (∀ (i : Index xs) (x : A) → x ∈ xs → B) → List B
mapEnumWith∈ xs f = mapWith∈ (enumerate xs) λ{ {(i , x)} ix∈ → f i x (ix∈→x∈ ix∈) }

just-injective : ∀ {A : Set} {x y} → (Maybe A ∋ just x) ≡ just y → x ≡ y
just-injective refl = refl

‼-suc : ∀ {ℓ} {A : Set ℓ} {x : A} {xs : List A} {i : Index xs}
  → (x ∷ xs ‼ fsuc i)
  ≡ (xs ‼ i)
‼-suc = refl

‼-map′ : ∀ {A B : Set} {xs : List A} {f : A → B}
  → Index xs
  → Index (map f xs)
‼-map′ {xs = x ∷ xs} fzero    = fzero
‼-map′ {xs = x ∷ xs} (fsuc i) = fsuc (‼-map′ {xs = xs} i)

‼-map : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {f : A → B} {xs : List A} {i : Index xs}
  → (map f xs ‼ cast (sym (length-map f xs)) i)
  ≡ f (xs ‼ i)
‼-map {_} {_} {A} {B} {f} {[]} {()}
‼-map {_} {_} {A} {B} {f} {x ∷ xs} {fzero} = refl
‼-map {_} {_} {A} {B} {f} {x ∷ xs} {fsuc i}
  rewrite ‼-suc {_} {A} {x} {xs} {i}
        = ‼-map {_} {_} {A} {B} {f} {xs} {i}

‼→⁉ : ∀ {ℓ} {A : Set ℓ} {xs : List A} {ix : Index xs}
    → just (xs ‼ ix) ≡ (xs ⁉ toℕ ix)
‼→⁉ {_} {_} {[]}     {()}
‼→⁉ {_} {_} {x ∷ xs} {fzero}   = refl
‼→⁉ {_} {A} {x ∷ xs} {fsuc ix} = ‼→⁉ {_} {A} {xs} {ix}

⁉→‼ : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} {ix : Index xs}
    → (len≡ : length xs ≡ length ys)
    → (xs ⁉ toℕ ix) ≡ (ys ⁉ toℕ ix)
    → (xs ‼ ix) ≡ (ys ‼ cast len≡ ix)
⁉→‼ {_} {A} {[]}     {[]}      {ix}      len≡ eq   = refl
⁉→‼ {_} {A} {[]}     {x ∷ ys}  {ix}      () eq
⁉→‼ {_} {A} {x ∷ xs} {[]}      {ix}      () eq
⁉→‼ {_} {A} {x ∷ xs} {.x ∷ ys} {fzero}   len≡ refl = refl
⁉→‼ {_} {A} {x ∷ xs} {y ∷ ys}  {fsuc ix} len≡ eq
  rewrite ‼-suc {_} {A} {x} {xs} {ix}
        = ⁉→‼ {_} {A} {xs} {ys} {ix} (suc-injective len≡) eq

------------------------------------------------------------------------
-- General utilities.

unzip₃ : List (A × B × C) → List A × List B × List C
unzip₃ = map₂ unzip ∘ unzip

filter₁ : List (A ⊎ B) → List A
filter₁ = mapMaybe isInj₁

filter₂ : List (A ⊎ B) → List B
filter₂ = mapMaybe isInj₂

-- Prefix relation, instantiated for propositional equality.
Prefix≡ : List A → List A → Set _
Prefix≡ = Prefix _≡_

-- Finite sets.
Finite : Set → Set
Finite A = ∃[ n ] (A ↔ Fin n)

finList : Finite A → List A
finList (n , record { from = record { _⟨$⟩_ = f } }) = map f (allFin n)

_≟_∶-_ : (x : A) → (y : A) → Finite A → Dec (x ≡ y)
x ≟ y ∶- (_ , record { to   = record { _⟨$⟩_ = toFin }
                     ; from = record { _⟨$⟩_ = fromFin ; cong = cong′ }
                     ; inverse-of = record { left-inverse-of  = invˡ }})
  with toFin x ≟ᶠ toFin y
... | yes x≡y = yes (begin x                 ≡⟨ sym (invˡ x) ⟩
                           fromFin (toFin x) ≡⟨ cong′ x≡y ⟩
                           fromFin (toFin y) ≡⟨ invˡ y ⟩
                           y ∎)
... | no  x≢y = no λ{ refl → x≢y refl }

≡-findec : Finite A → Decidable {A = A} _≡_
≡-findec A↔fin = _≟_∶- A↔fin
