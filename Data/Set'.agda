------------------------------------------------------------------------
-- Set utilities
------------------------------------------------------------------------
{-# OPTIONS --allow-unsolved-metas #-}

open import Level         using (0ℓ)
open import Function      using (_∘_)
open import Data.Unit     using (⊤; tt)
open import Data.Empty    using (⊥; ⊥-elim)
open import Data.Product  using (_×_; ∃-syntax; proj₁; proj₂; _,_; Σ)
open import Data.Sum      using (_⊎_; inj₁; inj₂; map₁; map₂)
open import Data.Bool     using (Bool; true; false; T)
open import Data.Nat      using (ℕ)
open import Data.Fin      using (Fin)
  renaming (zero to 0ᶠ; suc to sucᶠ)
open import Data.List     using (List; []; _∷_; [_]; filter; _++_; length)

open import Data.List.Relation.Unary.Any using (Any; any; here; there; index)
open import Data.List.Relation.Unary.All using (All) renaming ([] to ∀[]; _∷_ to _∀∷_)
import Data.List.Relation.Unary.Unique.Propositional as Uniq
open import Data.List.Membership.Propositional.Properties using (∈-filter⁻; ∈-++⁻)

open import Relation.Nullary                      using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation             using (contradiction; ¬?)
open import Relation.Nullary.Decidable            using (True; False; fromWitness; toWitness; ⌊_⌋)
open import Relation.Unary                        using (Pred)
  renaming (Decidable to UnaryDec)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; inspect)

open import Utilities.Lists

module Data.Set' {A : Set} (_≟_ : Decidable (_≡_ {A = A})) where

  open import Data.List.Membership.DecPropositional _≟_ using (_∈_; _∉_; _∈?_) public

  ------------------------------------------------------------------------
  -- Decidable equality.

  _≣_ : Decidable (_≡_ {A = A})
  _≣_ = _≟_

  infix 4 _≟ₗ_
  _≟ₗ_ : Decidable {A = List A} _≡_
  []     ≟ₗ []     = yes refl
  []     ≟ₗ _ ∷ _  = no λ ()
  _ ∷ _  ≟ₗ []     = no λ ()
  x ∷ xs ≟ₗ y ∷ ys with x ≟ y
  ... | no ¬p      = no λ{refl → ¬p refl}
  ... | yes refl   with xs ≟ₗ ys
  ... | no ¬pp     = no λ{refl → ¬pp refl}
  ... | yes refl   = yes refl

  ------------------------------------------------------------------------
  -- Subset relation.

  open import Data.List.Relation.Binary.Subset.Propositional {A = A} using (_⊆_) public

  _⊆?_ : List A → List A → Set
  []       ⊆? _  = ⊤
  (x ∷ xs) ⊆? ys with x ∈? ys
  ... | yes _ = xs ⊆? ys
  ... | no  _ = ⊥

  sound-⊆ : ∀ {xs ys} → {p : xs ⊆? ys} → xs ⊆ ys
  sound-⊆ {[]} {ys} {xs⊆?ys} = λ ()
  sound-⊆ {x ∷ xs} {ys} {xs⊆?ys} with x ∈? ys
  ... | yes x∈ys = λ{ (here refl)  → x∈ys
                    ; (there y∈xs) → (sound-⊆ {p = xs⊆?ys}) y∈xs }
  ... | no  x∉ys = ⊥-elim xs⊆?ys

  ------------------------------------------------------------------------
  -- Sets as lists with no duplicates.

  open Uniq {0ℓ} {A} using (Unique) public renaming ([] to U[]; _∷_ to _U∷_)
  open import Data.List.Relation.Unary.AllPairs using (allPairs?)

  unique? : ∀ xs → Dec (Unique xs)
  unique? xs = allPairs? (λ x y → ¬? (x ≟ y)) xs

  record Set' : Set where
    constructor ⟨_⟩∶-_
    field
      list  : List A
      .uniq : Unique list
  open Set' public

  infix 4 _∈′_
  _∈′_ : A → Set' → Set
  o ∈′ ⟨ os ⟩∶- _ = o ∈ os

  ∅ : Set'
  ∅ = ⟨ [] ⟩∶- U[]

  singleton : A → Set'
  singleton a = ⟨ [ a ] ⟩∶- (∀[] U∷ U[])

  ∣_∣ : Set' → ℕ
  ∣_∣ = length ∘ list

  infixr 5 _─_
  _─_ : Set' → Set' → Set'
  ⟨ xs ⟩∶- pxs ─ ⟨ ys ⟩∶- pys = ⟨ filter (λ x → ¬? (x ∈? ys)) xs ⟩∶- {!!}
    -- where
    --   zs : List A
    --   zs = filter (λ x → ¬? (x ∈? ys)) xs

    --   lem₁ : ∀ {a as}

    --        → noDuplicates as
    --        → ¬ (a ∈ as)
    --          ---------------------
    --        → noDuplicates (a ∷ as)
    --   lem₁ {a} {as} pas a∉as with a ∈? as
    --   ... | yes a∈as = a∉as a∈as
    --   ... | no  _    = pas


    --   lem₂ : ∀ {as : List A} {P : Pred A 0ℓ} {P? : UnaryDec P}

    --      → noDuplicates as
    --        ---------------------------
    --      → noDuplicates (filter P? as)

    --   lem₂ {[]}     {P} {P?} pas = tt
    --   lem₂ {a ∷ as} {P} {P?} pas with a ∈? as | P? a | a ∈? filter P? as
    --   ... | yes _   | _     | _     = ⊥-elim pas
    --   ... | no  _   | no  _ | _     = lem₂ {as} pas
    --   ... | no _    | yes _ | no ¬p = lem₁ (lem₂ {as} pas) ¬p
    --   ... | no a∉as | yes _ | yes p = ⊥-elim (a∉as (proj₁ (∈-filter⁻ P? p)))

    --   pzs : noDuplicates zs
    --   pzs = lem₂ {as = xs} pxs

  infixr 4 _∪_
  _∪_ : Set' → Set' → Set'
  x@(⟨ xs ⟩∶- pxs) ∪ y@(⟨ ys ⟩∶- pys) = ⟨ xs ++ list (y ─ x) ⟩∶- {!!}

  fromList : List A → Set'
  fromList [] = ⟨ [] ⟩∶- U[]
  fromList (x ∷ xs) with x ∈? xs
  ... | yes _ = fromList xs
  ... | no  _ = ⟨ x ∷ list (fromList xs) ⟩∶- {!!}

  ------------------------------------------------------------------------
  -- Deletion/Non-membership.

  _\\_ : List A → List A → List A
  xs \\ [] = xs
  xs \\ (x ∷ ys) with x ∈? xs
  ... | no _     = xs \\ ys
  ... | yes x∈xs = (remove xs (index x∈xs)) \\ ys

  \\-same : ∀ {xs} → [] ≡ xs \\ xs
  \\-same {[]} = refl
  \\-same {x ∷ ys} with x ∈? (x ∷ ys)
  ... | no ¬p           = ⊥-elim (¬p (here refl))
  ... | yes (here refl) = \\-same {ys}
  ... | yes (there p)   = {!!}

  \\-left : ∀ {xs} → [] ≡ [] \\ xs
  \\-left {[]}     = refl
  \\-left {x ∷ ys} with x ∈? []
  ... | no _ = \\-left {ys}
  ... | yes ()

  \\-head : ∀ {x xs} → [] ≡ [ x ] \\ (x ∷ xs)
  \\-head {x} {xs} with x ∈? [ x ]
  ... | no ¬p = ⊥-elim (¬p (here refl))
  ... | yes p with index p
  ... | 0ᶠ    = \\-left {xs}
  ... | sucᶠ ()

  \\-‼ : ∀ {xs : List A} {i : Index xs}
       → [] ≡ [ xs ‼ i ] \\ xs
  \\-‼ {[]} {()}
  \\-‼ {x ∷ xs} {0ᶠ} with x ∈? [ x ]
  ... | no ¬p = ⊥-elim (¬p (here refl))
  ... | yes (here relf) = \\-left {xs}
  ... | yes (there ())
  \\-‼ {x ∷ xs} {sucᶠ i} with x ∈? [ xs ‼ i ]
  ... | no ¬p = \\-‼ {xs} {i}
  ... | yes (here refl) = \\-left {xs}
  ... | yes (there ())

  ------------------------------------------------------------------------
  -- Permutation relation.

  open import Data.List.Relation.Permutation.Inductive using (_↭_)
  open import Data.List.Any using (index)

  _↭?_ : List A → List A → Set
  []       ↭? []       = ⊤
  []       ↭? (_ ∷ _)  = ⊥
  (x ∷ xs) ↭? ys with x ∈? ys
  ... | no  _    = ⊥
  ... | yes x∈ys = xs ↭? remove ys (index x∈ys)

  ↭-remove : ∀ {y : A} {ys : List A} {y∈ys : y ∈ ys}
           → y ∷ remove ys (index y∈ys) ↭ ys
  ↭-remove {y} {.(y ∷ _)} {here refl} = _↭_.refl
  ↭-remove {y} {(x ∷ y ∷ _)} {there (here refl)} = _↭_.swap y x _↭_.refl
  ↭-remove {y} {(x₁ ∷ x₂ ∷ ys)} {there (there y∈ys)} =
    _↭_.trans h₁ h₂
    where
      ys′ : List A
      ys′ = remove ys (index y∈ys)

      h₁ : y ∷ x₁ ∷ x₂ ∷ ys′ ↭ x₁ ∷ x₂ ∷ y ∷ ys′
      h₁ = _↭_.trans (_↭_.swap y x₁ _↭_.refl) (_↭_.prep x₁ (_↭_.swap y x₂ _↭_.refl))

      h₂ : x₁ ∷ x₂ ∷ y ∷ ys′ ↭ x₁ ∷ x₂ ∷ ys
      h₂ = _↭_.prep x₁ (_↭_.prep x₂ ↭-remove)

  ↭-helper : ∀ {x : A} {xs ys : List A} {x∈ys : x ∈ ys}
           → xs ↭ remove ys (index x∈ys)
           → x ∷ xs ↭ ys
  ↭-helper {x} {xs} {ys} {x∈ys} h = _↭_.trans (_↭_.prep x h) ↭-remove

  sound-↭ : ∀ {xs ys} → {p : xs ↭? ys} → xs ↭ ys
  sound-↭ {[]} {[]}    {xs↭?ys} = _↭_.refl
  sound-↭ {[]} {_ ∷ _} {()}
  sound-↭ {x ∷ xs} {ys} {xs↭?ys} with x ∈? ys
  sound-↭ {x ∷ xs} {ys} {()} | no ¬x∈ys
  ... | yes x∈ys = ↭-helper (sound-↭ {p = xs↭?ys})

  -----------------------------------------------------
  -- Properties

  ≡-Set' : ∀ {xs ys px py}
         → xs ≡ ys
         → ⟨ xs ⟩∶- px ≡ ⟨ ys ⟩∶- py
  ≡-Set' refl = refl

  ∅─-identityʳ : ∀ {x} → (x ─ ∅) ≡ x
  ∅─-identityʳ {x} = {!!}

  ∅∪-identityˡ : ∀ {x} → (∅ ∪ x) ≡ x
  ∅∪-identityˡ {x} rewrite ∅─-identityʳ {x} = refl

  ∅─∅≡∅ : ∅ ─ ∅ ≡ ∅
  ∅─∅≡∅ = ∅─-identityʳ {∅}

  from↔to : ∀ {xs}
    → Unique xs
    → list (fromList xs) ≡ xs
  from↔to {[]} uniq = refl
  from↔to {x ∷ xs} uniq with x ∈? xs
  ... | no  _ = cong (x ∷_) (from↔to (Uniq.tail uniq))
  ... | yes p with uniq
  ... | p1 U∷ p2 = {!!}

  ∈-─ : ∀ {x : A} {xs ys : Set'}
    → x ∈′ (xs ─ ys)
    → x ∈′ xs
  ∈-─ {x} {xs} {ys} x∈ = proj₁ (∈-filter⁻ (λ x → ¬? (x ∈? list ys)) x∈)

  ∈-∪ : ∀ {x : A} {xs ys : Set'}
    → x ∈′ (xs ∪ ys)
    → x ∈′ xs ⊎ x ∈′ ys
  ∈-∪ {x} {xs} {ys} x∈ = map₂ (∈-─ {x} {ys} {xs}) (∈-++⁻ {v = x} (list xs) {ys = list (ys ─ xs)} x∈)
