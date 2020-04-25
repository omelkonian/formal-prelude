------------------------------------------------------------------------
-- Set utilities
------------------------------------------------------------------------
open import Level             using (0ℓ)
open import Function          using (_∘_; case_of_)
open import Data.Unit         using (⊤; tt)
open import Data.Empty        using (⊥; ⊥-elim)
open import Data.Product      using (_×_; ∃-syntax; proj₁; proj₂; _,_; Σ)
open import Data.Sum          using (_⊎_; inj₁; inj₂; map₁; map₂)
open import Data.Bool         using (Bool; true; false; T)
open import Data.Nat          using (ℕ)
open import Data.Fin          using (Fin; suc)
open import Data.Fin.Patterns using (0F)
open import Data.List         using (List; []; _∷_; [_]; filter; _++_; length)

open import Data.List.Properties                                     using (filter-all)


open import Data.List.Membership.Propositional            using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-filter⁻; ∈-++⁻)

open import Data.List.Relation.Unary.AllPairs                        using (allPairs?; []; _∷_)
open import Data.List.Relation.Unary.Unique.Propositional            using (Unique; tail)
open import Data.List.Relation.Unary.Unique.Propositional.Properties using (filter⁺; ++⁺)
open import Data.List.Relation.Unary.Any                             using (Any; any; here; there; index)
open import Data.List.Relation.Unary.All                             using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties                  using (¬Any⇒All¬; All¬⇒¬Any)
open import Data.List.Relation.Binary.Subset.Propositional           using (_⊆_)

open import Data.List.Relation.Binary.Disjoint.Propositional    using (Disjoint)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; refl; prep; swap; trans; ↭-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties using (∈-resp-↭; drop-∷; drop-mid; inject)


open import Relation.Nullary                      using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation             using (contradiction; ¬?)
open import Relation.Nullary.Decidable            using (True; False; fromWitness; toWitness; ⌊_⌋)
open import Relation.Unary                        using (Pred)
  renaming (Decidable to UnaryDec)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; inspect) renaming ([_] to ≡[_])

open import Prelude.Lists

module Prelude.Set' {A : Set} (_≟_ : Decidable (_≡_ {A = A})) where

  open import Data.List.Membership.DecPropositional               _≟_ using (_∈?_) public
  open import Data.List.Relation.Binary.Equality.DecPropositional _≟_ using (_≡?_)

  private
    variable
      x : A
      xs ys : List A

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
  ∅ = ⟨ [] ⟩∶- []

  singleton : A → Set'
  singleton a = ⟨ [ a ] ⟩∶- ([] ∷ [])

  ∣_∣ : Set' → ℕ
  ∣_∣ = length ∘ list

  infixr 5 _─_
  _─_ : Set' → Set' → Set'
  ⟨ xs ⟩∶- pxs ─ ⟨ ys ⟩∶- pys = ⟨ filter (_∉? ys) xs ⟩∶- filter⁺ (_∉? ys) pxs


  disjoint-─ : Disjoint xs (filter (_∉? xs) ys)
  disjoint-─ {xs = xs} {ys = ys} (x∈xs , x∈ys─xs) with ∈-filter⁻ (_∉? xs) {xs = ys} x∈ys─xs
  ... | (_ , x∉xs) = x∉xs x∈xs

  infixr 4 _∪_
  _∪_ : Set' → Set' → Set'
  (⟨ xs ⟩∶- pxs) ∪ (⟨ ys ⟩∶- pys)
    = ⟨ xs ++ filter (_∉? xs) ys
      ⟩∶- ++⁺ pxs (filter⁺ (_∉? xs) pys) (disjoint-─ {xs = xs} {ys = ys})

  nub : List A → List A
  nub [] = []
  nub (x ∷ xs) with x ∈? xs
  ... | yes _ = nub xs
  ... | no  _ = x ∷ nub xs

  nub-all : ∀ {P : A → Set} → All P xs → All P (nub xs)
  nub-all {xs = []}     []       = []
  nub-all {xs = x ∷ xs} (p ∷ ps) with x ∈? xs
  ... | yes _ = nub-all ps
  ... | no  _ = p ∷ nub-all ps

  nub-unique : Unique (nub xs)
  nub-unique {xs = []} = []
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

  \\-left : [] ≡ [] \\ xs
  \\-left {[]}     = refl
  \\-left {x ∷ ys} with x ∈? []
  ... | no _ = \\-left {ys}
  ... | yes ()

  \\-head : [] ≡ [ x ] \\ (x ∷ xs)
  \\-head {x = x} {xs = xs} with x ∈? [ x ]
  ... | no ¬p = ⊥-elim (¬p (here refl))
  ... | yes p with index p
  ... | 0F    = \\-left {xs = xs}
  ... | suc ()

  \\-‼ : ∀ {i : Index xs}
       → [] ≡ [ xs ‼ i ] \\ xs
  \\-‼ {xs = []} {()}
  \\-‼ {xs = x ∷ xs} {0F} with x ∈? [ x ]
  ... | no ¬p = ⊥-elim (¬p (here refl))
  ... | yes (here relf) = \\-left {xs = xs}
  ... | yes (there ())
  \\-‼ {xs = x ∷ xs} {suc i} with x ∈? [ xs ‼ i ]
  ... | no ¬p = \\-‼ {xs = xs} {i}
  ... | yes (here refl) = \\-left {xs = xs}
  ... | yes (there ())

  ------------------------------------------------------------------------
  -- Permutation relation.

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

  ≡-Set' : ∀ .{px : Unique xs} .{py : Unique ys}
         → xs ≡ ys
         → ⟨ xs ⟩∶- px ≡ ⟨ ys ⟩∶- py
  ≡-Set' refl = refl

  All∉[] : ∀ {ys : List A} → All (_∉ []) ys
  All∉[] {ys = []}     = []
  All∉[] {ys = y ∷ ys} = (λ ()) ∷ All∉[] {ys = ys}

  ∅─-identityʳ : ∀ {xs} → (xs ─ ∅) ≡ xs
  ∅─-identityʳ {xs = (⟨ xs ⟩∶- p)} = ≡-Set' {px = filter⁺ (_∉? []) p} {py = p} (filter-all (_∉? []) All∉[])

  ∅∪-identityˡ : ∀ {xs} → (∅ ∪ xs) ≡ xs
  ∅∪-identityˡ {xs} rewrite ∅─-identityʳ {xs} = refl

  ∅─∅≡∅ : ∅ ─ ∅ ≡ ∅
  ∅─∅≡∅ = ∅─-identityʳ {∅}

  unique-∈ : Unique (x ∷ xs) → x ∉ xs
  unique-∈ {xs = []} u ()
  unique-∈ {xs = x ∷ xs} ((x≢x ∷ _) ∷ _) (here refl) = x≢x refl
  unique-∈ {xs = x ∷ xs} ((_ ∷ p) ∷ _)   (there x∈)  = All¬⇒¬Any p x∈

  nub-from∘to : Unique xs → nub xs ≡ xs
  nub-from∘to {[]}     _ = refl
  nub-from∘to {x ∷ xs} u@(_ ∷ Uxs) with x ∈? xs
  ... | no  _    = cong (x ∷_) (nub-from∘to Uxs)
  ... | yes x∈xs = ⊥-elim (unique-∈ u x∈xs)

  from↔to : Unique xs → list (fromList xs) ≡ xs
  from↔to Uxs rewrite nub-from∘to Uxs = refl

  ∈-─ : ∀ {x : A} {xs ys : Set'}
    → x ∈′ (xs ─ ys)
    → x ∈′ xs
  ∈-─ {x} {xs} {ys} x∈ = proj₁ (∈-filter⁻ (_∉? list ys) x∈)

  ∈-∪ : ∀ {x : A} {xs ys : Set'}
    → x ∈′ (xs ∪ ys)
    → x ∈′ xs ⊎ x ∈′ ys
  ∈-∪ {x} {xs} {ys} x∈ = map₂ (∈-─ {x} {ys} {xs}) (∈-++⁻ {v = x} (list xs) {ys = list (ys ─ xs)} x∈)

  unique-nub-∈ : ∀ {x : A} {xs : List A}
    → Unique xs
    → (x ∈ nub xs) ≡ (x ∈ xs)
  unique-nub-∈ uniq rewrite nub-from∘to uniq = refl

  ∈-nub : ∀ {x : A} {xs : List A}
    → x ∈ nub xs
    → x ∈ xs
  ∈-nub {x = x} {xs = x′ ∷ xs} x∈
    with x′ ∈? xs
  ... | yes _ = there (∈-nub x∈)
  ... | no ¬p
    with x∈
  ... | (here refl) = here refl
  ... | (there x∈′) = there (∈-nub x∈′)
