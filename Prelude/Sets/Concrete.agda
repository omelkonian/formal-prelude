------------------------------------------------------------------------
-- Sets as unique lists. (COPIED from Prelude.Sets.AsUniqueLists)
------------------------------------------------------------------------

open import Prelude.Init
open L.Mem using (∈-filter⁻; ∈-filter⁺; ∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open L.Uniq using (filter⁺; ++⁺; map⁺)
open import Prelude.General
open import Prelude.Lists
open import Prelude.DecLists
open import Prelude.Membership
open import Prelude.DecEq
open import Prelude.Measurable
open import Prelude.Bifunctor
open import Prelude.Decidable
open import Prelude.Apartness
open import Prelude.Ord
open import Prelude.ToList
open import Prelude.FromList
open import Prelude.Semigroup

import Relation.Binary.Reasoning.Setoid as BinSetoid

module Prelude.Sets.Concrete {A : Set} ⦃ _ : DecEq A ⦄ where

-- ** basic definitions

-- Sets as lists with no duplicates.
record Set' : Set where
  constructor _⊣_
  field
    list  : List A
    .uniq : Unique list
open Set'
syntax Set' {A = A} = Set⟨ A ⟩

private
  variable
    x : A
    xs ys zs : List A
    Xs Ys Zs : Set'

-----------------------------------------------------------------------
-- Lifting from list predicates/relations to set predicates/relations.

private
  record Lift (F : Set → Set₁) : Set₁ where
    field ↑ : F (List A) → F Set'
  open Lift {{...}}

  instance
    Lift-Pred : Lift Pred₀
    Lift-Pred .↑ P = P ∘ list

    Lift-Rel : Lift Rel₀
    Lift-Rel .↑ _~_ = _~_ on list

-- e.g. All/Any predicates for sets
All' Any' : Pred₀ A → Pred₀ Set'
All' = ↑ ∘ All
Any' = ↑ ∘ Any

infixr 8 _─_
infixr 7 _∩_
infixr 6 _∪_
infix 4 _∈ˢ_ _∉ˢ_ _∈ˢ?_ _∉ˢ?_

_∈ˢ_ _∉ˢ_ : A → Set' → Set
o ∈ˢ (os ⊣ _) = o ∈ os
o ∉ˢ s = ¬ (o ∈ˢ s)

∈ˢ-irr : Irrelevant (x ∈ˢ Xs)
∈ˢ-irr {Xs = _ ⊣ un} = ∈-irr (recompute dec un)

_∷_∶-_ : (x : A) → (xs : Set') → ¬ x ∈ˢ xs → Set'
x ∷ (xs ⊣ p) ∶- x∉ = (x ∷ xs) ⊣ (L.All.¬Any⇒All¬ _ x∉ ∷ p)

_<$>_∶-_ : (f : A → A) → Set' → (∀ {x y} → f x ≡ f y → x ≡ y) → Set'
f <$> (xs ⊣ p) ∶- inj = map f xs ⊣ map⁺ inj p

filter′ : ∀ {P : Pred A 0ℓ} → Decidable¹ P → Set' → Set'
filter′ P? (xs ⊣ p) = filter P? xs ⊣ filter⁺ P? p

-- ** decidability
_∈ˢ?_ : Decidable² _∈ˢ_
o ∈ˢ? (os ⊣ _) = o ∈? os
_∉ˢ?_ : Decidable² _∉ˢ_
o ∉ˢ? (os ⊣ _) = ¬? (o ∈? os)

instance
  Apart-Set' : Set' // Set'
  Apart-Set' ._♯_ s s′ = ∀ {k} → ¬ (k ∈ˢ s × k ∈ˢ s′)

_++_∶-_ : ∀ (s s′ : Set') → s ♯ s′ → Set'
(xs ⊣ pxs) ++ (ys ⊣ pys) ∶- dsj =
  (xs ++ ys) ⊣ ++⁺ pxs pys dsj

count′ : ∀ {P : Pred A 0ℓ} → Decidable¹ P → Set' → ℕ
count′ P? = count P? ∘ list

∅ : Set'
∅ = [] ⊣ []

singleton : A → Set'
singleton a = [ a ] ⊣ ([] ∷ [])

singleton∈ˢ : ∀ {x x′} → x′ ∈ˢ singleton x ↔ x′ ≡ x
singleton∈ˢ = (λ where (here refl) → refl) , (λ where refl → here refl)

_∪_ _∩_ _─_ : Op₂ Set'
x ─ y = filter′ (_∉ˢ? y) x
x ∩ y = filter′ (_∈ˢ? y) x
x ∪ y = x ++ (filter′ (_∉ˢ? x) y) ∶- disjoint-─ {xs = list x} {ys = list y}
  where
    disjoint-─ : Disjoint xs (filter (_∉? xs) ys)
    disjoint-─ {xs = xs} {ys = ys} (x∈ , x∈ˢ)
      = let _ , x∉ = ∈-filter⁻ (_∉? xs) {xs = ys} x∈ˢ
        in  x∉ x∈

⋃ : (A → Set') → Set' → Set'
⋃ f = foldr _∪_ ∅ ∘ map f ∘ list

-- ** relational properties
∉∅ : ∀ x → ¬ x ∈ˢ ∅
∉∅ _ ()

∈-─⁻ : ∀ x xs ys → x ∈ˢ (xs ─ ys) → x ∈ˢ xs
∈-─⁻ x xs ys x∈ = proj₁ (∈-filter⁻ (_∉ˢ? ys) x∈)

∈-─⁺ : ∀ x xs ys → x ∈ˢ xs → ¬ x ∈ˢ ys → x ∈ˢ (xs ─ ys)
∈-─⁺ x xs ys x∈ x∉ = ∈-filter⁺ ((_∉ˢ? ys)) x∈ x∉

∈-∪⁻ : ∀ x xs ys → x ∈ˢ (xs ∪ ys) → x ∈ˢ xs ⊎ x ∈ˢ ys
∈-∪⁻ x xs ys x∈ = map₂ (∈-─⁻ x ys xs) (∈-++⁻ {v = x} (list xs) {ys = list (ys ─ xs)} x∈)

∈-∪⁺ˡ : ∀ x xs ys → x ∈ˢ xs → x ∈ˢ (xs ∪ ys)
∈-∪⁺ˡ x xs ys x∈ = ∈-++⁺ˡ x∈

∈-∪⁺ʳ : ∀ x xs ys → x ∈ˢ ys → x ∈ˢ (xs ∪ ys)
∈-∪⁺ʳ x xs ys x∈ with x ∈ˢ? xs
... | yes x∈ˢ = ∈-∪⁺ˡ x xs ys x∈ˢ
... | no  x∉  = ∈-++⁺ʳ (list xs) (∈-filter⁺ (_∉ˢ? xs) x∈ x∉)

∈-∩⁺ : ∀ x xs ys → x ∈ˢ xs → x ∈ˢ ys → x ∈ˢ (xs ∩ ys)
∈-∩⁺ _ _ ys = ∈-filter⁺ ((_∈ˢ? ys))

∈-∩⁻ : ∀ x xs ys → x ∈ˢ (xs ∩ ys) → (x ∈ˢ xs) × (x ∈ˢ ys)
∈-∩⁻ _ xs ys = ∈-filter⁻ (_∈ˢ? ys) {xs = list xs}

-- ** derived operations

-- ♯-comm : Symmetric _♯_
♯-comm : ∀ (x y : Set') → x ♯ y → y ♯ x
♯-comm x y x♯y = x♯y ∘ Product.swap

∈-∩⇒¬♯ : ∀ x xs ys → x ∈ˢ (xs ∩ ys) → ¬ (xs ♯ ys)
∈-∩⇒¬♯ x xs ys x∈ xs♯ys = xs♯ys $ ∈-∩⁻ _ xs ys x∈

♯-skipˡ : ∀ xs ys (zs : Set') → (xs ∪ ys) ♯ zs → ys ♯ zs
♯-skipˡ xs ys _ p (x∈ys , x∈zs) = p (∈-∪⁺ʳ _ xs ys x∈ys , x∈zs)

_⊆ˢ_ _⊇ˢ_ _⊈ˢ_ _⊉ˢ_ : Rel Set' _
s ⊆ˢ s′ = ∀ {x} → x ∈ˢ s → x ∈ˢ s′
s ⊈ˢ s′ = ¬ s ⊆ˢ s′
s ⊇ˢ s′ = s′ ⊆ˢ s
s ⊉ˢ s′ = ¬ s ⊇ˢ s′

⊆ˢ-trans : Transitive _⊆ˢ_
⊆ˢ-trans ij ji = ji ∘ ij


-- ** algebraic properties
_≈ˢ_ : Rel₀ Set'
s ≈ˢ s′ = (s ⊆ˢ s′) × (s′ ⊆ˢ s)

≈ˢ-equiv : IsEquivalence _≈ˢ_
≈ˢ-equiv = record
  { refl  = id , id
  ; sym   = Product.swap
  ; trans = λ where (ij , ji) (jk , kj) → jk ∘ ij , ji ∘ kj
  }
open IsEquivalence ≈ˢ-equiv renaming (refl to ≈ˢ-refl; sym to ≈ˢ-sym; trans to ≈ˢ-trans)

≈ˢ-setoid : Setoid 0ℓ 0ℓ
≈ˢ-setoid = record { Carrier = Set'; _≈_ = _≈ˢ_; isEquivalence = ≈ˢ-equiv }

module ≈ˢ-Reasoning = BinSetoid ≈ˢ-setoid

open Alg _≈ˢ_

∅─-identityʳ : RightIdentity ∅ _─_
∅─-identityʳ s rewrite L.filter-all (_∉? []) {xs = list s} All∉[] = ≈ˢ-refl {x = s}

∅∪-identityˡ : LeftIdentity ∅ _∪_
∅∪-identityˡ xs =
  begin ∅ ∪ xs ≈⟨ ≈ˢ-refl {xs ─ ∅} ⟩
        xs ─ ∅ ≈⟨ ∅─-identityʳ xs ⟩
        xs ∎
  where open ≈ˢ-Reasoning

-- ** list conversion
instance
  ToList-Set' : ToList Set' A
  ToList-Set' .toList = list

  FromList-Set' : FromList A Set'
  FromList-Set' .fromList xs = nub xs ⊣ Unique-nub {xs = xs}

from↔to : ∀ xs → Unique xs → toList (fromList {B = Set'} xs) ≡ xs
from↔to _ Uxs rewrite nub-from∘to Uxs = refl

∈ˢ-fromList : x ∈ xs ↔ x ∈ˢ fromList xs
∈ˢ-fromList = ∈-nub⁺ , ∈-nub⁻

-- ** decidability of set equality
instance
  DecEq-Set' : DecEq Set'
  DecEq-Set' ._≟_ s s′ with list s ≟ list s′
  ... | no ¬p    = no λ{ refl → ¬p refl }
  ... | yes refl = yes refl

  Measurable-Set : Measurable Set'
  Measurable-Set = record {∣_∣ = length ∘ list}

record Set'⁺ : Set where
  constructor _⊣_
  field
    set   : Set'
    .set⁺ : ∣ set ∣ > 0
syntax Set'⁺ {A = A} = Set⁺⟨ A ⟩

-- instance
--   Semigroup-Set' : ⦃ Semigroup A ⦄ → Semigroup Set'
--   Semigroup-Set' ._◇_ s@(xs ⊣ p) s′@(ys ⊣ p′) = {!!}
