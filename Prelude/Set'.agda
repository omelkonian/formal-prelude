------------------------------------------------------------------------
-- Set utilities
------------------------------------------------------------------------
{-# OPTIONS --allow-unsolved-metas #-}

open import Level         using (0ℓ)
open import Function      using (_∘_; case_of_)
open import Data.Unit     using (⊤; tt)
open import Data.Empty    using (⊥; ⊥-elim)
open import Data.Product  using (_×_; ∃-syntax; proj₁; proj₂; _,_; Σ)
open import Data.Sum      using (_⊎_; inj₁; inj₂; map₁; map₂)
open import Data.Bool     using (Bool; true; false; T)
open import Data.Nat      using (ℕ)
open import Data.Fin      using (Fin)
  renaming (zero to 0ᶠ; suc to sucᶠ)
open import Data.List     using (List; []; _∷_; [_]; filter; _++_; length)

open import Data.List.Relation.Unary.Any                  using (Any; any; here; there; index)
open import Data.List.Relation.Unary.All                  using (All) renaming ([] to ∀[]; _∷_ to _∀∷_)
open import Data.List.Relation.Unary.AllPairs             using (allPairs?; []; _∷_)
open import Data.List.Relation.Unary.All.Properties       using (¬Any⇒All¬)
open import Data.List.Membership.Propositional.Properties using (∈-filter⁻; ∈-++⁻)

import Data.List.Relation.Unary.Unique.Propositional as Uniq

open import Relation.Nullary                      using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation             using (contradiction; ¬?)
open import Relation.Nullary.Decidable            using (True; False; fromWitness; toWitness; ⌊_⌋)
open import Relation.Unary                        using (Pred)
  renaming (Decidable to UnaryDec)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; inspect) renaming ([_] to ≡[_])

open import Prelude.Lists

module Prelude.Set' {A : Set} (_≟_ : Decidable (_≡_ {A = A})) where

  open import Data.List.Membership.DecPropositional _≟_ using (_∈_; _∉_; _∈?_) public
  open import Data.List.Relation.Binary.Equality.DecPropositional _≟_ using (_≡?_)

  private
    variable
      x : A
      xs ys zs : List A

  ------------------------------------------------------------------------
  -- Decidable equality.

  _≣_ : Decidable (_≡_ {A = A})
  _≣_ = _≟_

  infix 4 _≟ₗ_
  _≟ₗ_ : Decidable {A = List A} _≡_
  _≟ₗ_ = _≡?_

  infix 4 _∉?_
  _∉?_ : Decidable _∉_
  x ∉? xs = ¬? (x ∈? xs)

  ------------------------------------------------------------------------
  -- Subset relation.

  open import Data.List.Relation.Binary.Subset.Propositional {A = A} using (_⊆_) public

  infix 4 _⊆?_
  _⊆?_ : (xs : List A) → (ys : List A) → Dec (xs ⊆ ys)
  []       ⊆? ys  = yes λ ()
  (x ∷ xs) ⊆? ys  with x ∈? ys
  ... | no  x∉ys  = no λ xs⊆ys → x∉ys (xs⊆ys (here refl))
  ... | yes x∈ys  with xs ⊆? ys
  ... | no  xs⊈ys = no λ xs⊆ys → xs⊈ys (λ {x} z → xs⊆ys (there z))
  ... | yes xs⊆ys = yes λ{ (here refl) → x∈ys
                         ; (there x∈)  → xs⊆ys x∈ }

  ------------------------------------------------------------------------
  -- Sets as lists with no duplicates.

  open Uniq {0ℓ} {A} using (Unique) public renaming ([] to U[]; _∷_ to _U∷_)

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

  nub : List A → List A
  nub [] = []
  nub (x ∷ xs) with x ∈? xs
  ... | yes _ = nub xs
  ... | no  _ = x ∷ nub xs

  nub-all : ∀ {P : A → Set} → All P xs → All P (nub xs)
  nub-all {xs = []}     ∀[]       = ∀[]
  nub-all {xs = x ∷ xs} (p ∀∷ ps) with x ∈? xs
  ... | yes _ = nub-all ps
  ... | no  _ = p ∀∷ nub-all ps

  nub-unique : Unique (nub xs)
  nub-unique {xs = []} = U[]
  nub-unique {xs = x ∷ xs} with x ∈? xs
  ... | yes _ = nub-unique {xs = xs}
  ... | no x∉ = nub-all {xs = xs} {P = _≢_ x} (¬Any⇒All¬ xs x∉) ∷ (nub-unique {xs = xs})

  fromList : List A → Set'
  fromList xs = ⟨ nub xs ⟩∶- (nub-unique {xs = xs})

  ------------------------------------------------------------------------
  -- Deletion/Non-membership.

  _\\_ : List A → List A → List A
  xs \\ [] = xs
  xs \\ (x ∷ ys) with x ∈? xs
  ... | no _     = xs \\ ys
  ... | yes x∈xs = (remove xs (index x∈xs)) \\ ys

  \\-same : [] ≡ xs \\ xs
  \\-same {[]} = refl
  \\-same {x ∷ ys} with x ∈? (x ∷ ys)
  ... | no ¬p           = ⊥-elim (¬p (here refl))
  ... | yes (here refl) = \\-same {ys}
  ... | yes (there p)   = {!!}

  \\-left : [] ≡ [] \\ xs
  \\-left {[]}     = refl
  \\-left {x ∷ ys} with x ∈? []
  ... | no _ = \\-left {ys}
  ... | yes ()

  \\-head : [] ≡ [ x ] \\ (x ∷ xs)
  \\-head {x = x} {xs = xs} with x ∈? [ x ]
  ... | no ¬p = ⊥-elim (¬p (here refl))
  ... | yes p with index p
  ... | 0ᶠ    = \\-left {xs = xs}
  ... | sucᶠ ()

  \\-‼ : ∀ {i : Index xs}
       → [] ≡ [ xs ‼ i ] \\ xs
  \\-‼ {xs = []} {()}
  \\-‼ {xs = x ∷ xs} {0ᶠ} with x ∈? [ x ]
  ... | no ¬p = ⊥-elim (¬p (here refl))
  ... | yes (here relf) = \\-left {xs = xs}
  ... | yes (there ())
  \\-‼ {xs = x ∷ xs} {sucᶠ i} with x ∈? [ xs ‼ i ]
  ... | no ¬p = \\-‼ {xs = xs} {i}
  ... | yes (here refl) = \\-left {xs = xs}
  ... | yes (there ())

  ------------------------------------------------------------------------
  -- Permutation relation.

  open import Data.List.Relation.Permutation.Inductive            using (_↭_; refl; prep; swap; trans; ↭-sym)
  open import Data.List.Relation.Permutation.Inductive.Properties using (∈-resp-↭; drop-∷; drop-mid; inject)
  open import Data.List.Any using (index)

  ¬[]↭ : ∀ {x : A} {xs : List A} → ¬ ([] ↭ x ∷ xs)
  ¬[]↭ (trans {.[]} {[]}     {.(_ ∷ _)} []↭ []↭₁) = ¬[]↭ []↭₁
  ¬[]↭ (trans {.[]} {x ∷ ys} {.(_ ∷ _)} []↭ []↭₁) = ¬[]↭ []↭

  ↭-remove : ∀ {x : A} {ys : List A} {x∈ys : x ∈ ys}
           → x ∷ remove ys (index x∈ys) ↭ ys
  ↭-remove {x} {.(x ∷ _)}       {here refl}          = refl
  ↭-remove {x} {(y ∷ x ∷ _)}    {there (here refl)}  = swap x y refl
  ↭-remove {x} {(x₁ ∷ x₂ ∷ ys)} {there (there x∈ys)} = trans h₁ h₂
    where
      ys′ : List A
      ys′ = remove ys (index x∈ys)

      h₁ : x ∷ x₁ ∷ x₂ ∷ ys′ ↭ x₁ ∷ x₂ ∷ x ∷ ys′
      h₁ = trans (swap x x₁ refl) (prep x₁ (swap x x₂ refl))

      h₂ : x₁ ∷ x₂ ∷ x ∷ ys′ ↭ x₁ ∷ x₂ ∷ ys
      h₂ = prep x₁ (prep x₂ ↭-remove)

  ↭-helper : ∀ {x∈ys : x ∈ ys}
           → xs ↭ remove ys (index x∈ys)
           → x ∷ xs ↭ ys
  ↭-helper {x} {xs} {ys} {x∈ys} h = trans (prep x h) ↭-remove

  ↭-helper′ : ∀ {x∈ys : x ∈ ys}
           → x ∷ xs ↭ ys
           → xs ↭ remove ys (index x∈ys)
  ↭-helper′ {x} {.(x ∷ _)}       {xs} {here refl}          h = drop-∷ h
  ↭-helper′ {x} {(y ∷ x ∷ _)}    {xs} {there (here refl)}  h = drop-mid [] [ y ] h
  ↭-helper′ {x} {(x₁ ∷ x₂ ∷ ys)} {xs} {there (there x∈ys)} h = drop-∷ {x = x} (trans h h′)
    where
      ys′ : List A
      ys′ = remove ys (index x∈ys)

      h‴ : ys ↭ x ∷ ys′
      h‴ = ↭-sym ↭-remove

      h″ : x₂ ∷ ys ↭ x ∷ x₂ ∷ ys′
      h″ = trans (prep x₂ h‴) (swap x₂ x refl)

      h′ : x₁ ∷ x₂ ∷ ys ↭ x ∷ x₁ ∷ x₂ ∷ ys′
      h′ = trans (prep x₁ h″) (swap x₁ x refl)

  _↭?_ : (xs : List A) → (ys : List A) → Dec (xs ↭ ys)
  []       ↭? []       = yes refl
  []       ↭? (x ∷ ys) = no ¬[]↭
  (x ∷ xs) ↭? ys       with x ∈? ys
  ... | no  x∉         = no λ x∷xs↭ → x∉ (∈-resp-↭ x∷xs↭ (here refl))
  ... | yes x∈         with xs ↭? remove ys (index x∈)
  ... | no ¬xs↭        = no (¬xs↭ ∘ ↭-helper′)
  ... | yes xs↭        = yes (↭-helper xs↭)

  -----------------------------------------------------
  -- Properties

  ≡-Set' : ∀ {px py}
         → xs ≡ ys
         → ⟨ xs ⟩∶- px ≡ ⟨ ys ⟩∶- py
  ≡-Set' refl = refl

  ∅─-identityʳ : ∀ {xs} → (xs ─ ∅) ≡ xs
  ∅─-identityʳ = {!!}

  ∅∪-identityˡ : ∀ {xs} → (∅ ∪ xs) ≡ xs
  ∅∪-identityˡ {xs} rewrite ∅─-identityʳ {xs} = refl

  ∅─∅≡∅ : ∅ ─ ∅ ≡ ∅
  ∅─∅≡∅ = ∅─-identityʳ {∅}

  -- from↔to : Unique xs → list (fromList xs) ≡ xs
  -- from↔to {[]} uniq = refl
  -- from↔to {x ∷ xs} uniq with x ∈? xs
  -- ... | no  _ = cong (x ∷_) (from↔to (Uniq.tail uniq))
  -- ... | yes p with uniq
  -- ... | p1 U∷ p2 = {!!}

  ∈-─ : ∀ {x : A} {xs ys : Set'}
    → x ∈′ (xs ─ ys)
    → x ∈′ xs
  ∈-─ {x} {xs} {ys} x∈ = proj₁ (∈-filter⁻ (λ x → ¬? (x ∈? list ys)) x∈)

  ∈-∪ : ∀ {x : A} {xs ys : Set'}
    → x ∈′ (xs ∪ ys)
    → x ∈′ xs ⊎ x ∈′ ys
  ∈-∪ {x} {xs} {ys} x∈ = map₂ (∈-─ {x} {ys} {xs}) (∈-++⁻ {v = x} (list xs) {ys = list (ys ─ xs)} x∈)
