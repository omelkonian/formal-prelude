------------------------------------------------------------------------
-- List utilities
------------------------------------------------------------------------

module Prelude.Lists where

open import Level    using (Level)
open import Function using (_∘_; _∋_; case_of_)

open import Data.Empty    using (⊥; ⊥-elim)
open import Data.Unit     using (⊤; tt)
open import Data.Product  using (_×_; _,_; map₂)
open import Data.Maybe    using (Maybe; just; nothing)
open import Data.Fin      using (Fin; toℕ; fromℕ≤; inject≤; cast; inject₁)
  renaming (zero to fzero; suc to fsuc)
open import Data.Nat      using (ℕ; zero; suc; _≤_; z≤n; s≤s; pred; _<?_)
open import Data.Nat.Properties using (suc-injective)
open import Data.List.Properties using (length-map)

open import Relation.Nullary                      using (¬_; Dec)
open import Relation.Nullary.Decidable            using (True)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

open import Data.List public
  using (List; []; [_]; _∷_; _∷ʳ_; _++_; map; concatMap; length; zip; sum; upTo; lookup; allFin; unzip)
open import Data.List.Membership.Propositional using (_∈_)

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

------------------------------------------------------------------------
-- Inductive relations on lists.

-- Less-than relation for lists (on lengths).
infix 3 _≾_
data _≾_ {ℓ} {A : Set ℓ} : List A → List A → Set where

  base-≾ : ∀ {xs : List A}

    → -------
      [] ≾ xs

  step-≾ : ∀ {x y : A} {xs ys : List A}

    → xs ≾ ys
      ---------------
    → x ∷ xs ≾ y ∷ ys

infix 3 _≾?_
_≾?_ : List A → List A → Set
[]     ≾? _      = ⊤
_ ∷ _  ≾? []     = ⊥
_ ∷ xs ≾? _ ∷ ys = xs ≾? ys

sound-≾ : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} → {p : xs ≾? ys} → xs ≾ ys
sound-≾ {_} {_} {[]}     {ys}     {tt} = base-≾
sound-≾ {_} {_} {x ∷ xs} {[]}     {()}
sound-≾ {_} {_} {_ ∷ xs} {_ ∷ ys} {pp} = step-≾ (sound-≾ {p = pp})

_ : ([ 1 ]) ≾? (1 ∷ 2 ∷ 3 ∷ [])
_ = tt

_ : ∀ {v} → True (length [ v ] <? length (1 ∷ [ v ]))
_ = tt


-- Partition relation.
data Partition {ℓ} {A : Set ℓ} : List A → (List A × List A) → Set where

  Partition-[] :

      ----------------------
      Partition [] ([] , [])


  Partition-L  : ∀ {x xs ys zs}

    → Partition xs (ys , zs)
      --------------------------------
    → Partition (x ∷ xs) (x ∷ ys , zs)


  Partition-R  : ∀ {x xs ys zs}

    → Partition xs (ys , xs)
      --------------------------------
    → Partition (x ∷ xs) (ys , x ∷ zs)

partition-[]ˡ : ∀ {ℓ} {A : Set ℓ} (xs : List A) → Partition xs ([] , xs)
partition-[]ˡ []       = Partition-[]
partition-[]ˡ (x ∷ xs) = Partition-R (partition-[]ˡ xs)

-- Prefix relation. (T0D0: upgrade stdlib and get from Data.List.Relation.Binary.Prefix)

record Prefix {A : Set} (xs ys : List A) : Set where
  constructor is-prefix-of
  field
    {k}   : List A
    proof : xs ++ k ≡ ys

open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary  using (Decidable)

Prefix? : ∀ {A : Set} → Decidable {A = A} _≡_ → Decidable (Prefix {A})
Prefix? _≟_ []       ys       = yes (is-prefix-of refl)
Prefix? _≟_ (x ∷ xs) []       = no (λ { (is-prefix-of ()) })
Prefix? _≟_ (x ∷ xs) (y ∷ ys)
  with x ≟ y
... | no ¬p                   = no λ{ (is-prefix-of refl) → ¬p refl }
... | yes refl
  with Prefix? _≟_ xs ys
... | no ¬p                   = no λ { (is-prefix-of refl) → ¬p (is-prefix-of refl) }
... | yes (is-prefix-of refl) = yes (is-prefix-of (cong (x ∷_) refl))

------------------------------------------------------------------------
-- List properties.

-- Concatenation
++-idʳ : ∀ {A : Set} {xs : List A}
       → xs ≡ xs ++ []
++-idʳ {_} {[]}     = refl
++-idʳ {_} {x ∷ xs} = cong (x ∷_) ++-idʳ


-- Sublist relation
import Data.List.Relation.Binary.Sublist.Heterogeneous as Sublist
open import Data.List.Relation.Binary.Sublist.Propositional using (_⊆_)

complement-⊆ : ∀ {A : Set} {xs ys : List A} → xs ⊆ ys → List A
complement-⊆ Sublist.[] = []
complement-⊆ (_ Sublist.∷  p) = complement-⊆ p
complement-⊆ (y Sublist.∷ʳ p) = y ∷ complement-⊆ p
