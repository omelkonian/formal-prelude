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
open import Prelude.InferenceRules

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

private variable
  x x′ y y′ z z′ : A
  xs ys zs : List A
  Xs Ys Zs s s′ s″ : Set'
  P : Pred A 0ℓ

-----------------------------------------------------------------------
-- Lifting from list predicates/relations to set predicates/relations.

private
  record Lift (F : Set → Set₁) : Set₁ where
    field ↑ : F (List A) → F Set'
  open Lift ⦃...⦄

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

filter′ : Decidable¹ P → Set' → Set'
filter′ P? (xs ⊣ p) = filter P? xs ⊣ filter⁺ P? p

-- ** decidability
_∈ˢ?_ : Decidable² _∈ˢ_
o ∈ˢ? (os ⊣ _) = o ∈? os
_∉ˢ?_ : Decidable² _∉ˢ_
o ∉ˢ? (os ⊣ _) = o ∉? os

count′ : ∀ {P : Pred A 0ℓ} → Decidable¹ P → Set' → ℕ
count′ P? = count P? ∘ list

∅ : Set'
∅ = [] ⊣ []

singleton : A → Set'
singleton a = [ a ] ⊣ ([] ∷ [])

singleton∈ˢ : x′ ∈ˢ singleton x ↔ x′ ≡ x
singleton∈ˢ = (λ where (here refl) → refl) , (λ where refl → here refl)

_++_∶-_ : ∀ (s s′ : Set') → Disjoint (list s) (list s′) → Set'
(xs ⊣ pxs) ++ (ys ⊣ pys) ∶- dsj =
  (xs ++ ys) ⊣ ++⁺ pxs pys dsj

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

_⊆ˢ_ _⊇ˢ_ _⊈ˢ_ _⊉ˢ_ : Rel Set' _
s ⊆ˢ s′ = list s ⊆ list s′
s ⊇ˢ s′ = s′ ⊆ˢ s
s ⊈ˢ s′ = ¬ s ⊆ˢ s′
s ⊉ˢ s′ = ¬ s ⊇ˢ s′

_⊆?ˢ_ = Decidable² _⊆ˢ_ ∋ dec²

⊆ˢ-trans : Transitive _⊆ˢ_
⊆ˢ-trans ij ji = ji ∘ ij

-- ** algebraic properties
_≈ˢ_ : Rel₀ Set'
s ≈ˢ s′ = (s ⊆ˢ s′) × (s′ ⊆ˢ s)

_≈?ˢ_ = Decidable² _≈ˢ_ ∋ dec²

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

≈ˢ⇒⊆ˢ : s ≈ˢ s′ → s ⊆ˢ s′
≈ˢ⇒⊆ˢ = proj₁

≈ˢ⇒⊆ˢ˘ : s ≈ˢ s′ → s′ ⊆ˢ s
≈ˢ⇒⊆ˢ˘ = proj₂

∅─-identityʳ : RightIdentity ∅ _─_
∅─-identityʳ s rewrite L.filter-all (_∉? []) {xs = list s} All∉[] = ≈ˢ-refl {x = s}

∅∪-identityˡ : LeftIdentity ∅ _∪_
∅∪-identityˡ xs =
  begin ∅ ∪ xs ≈⟨ ≈ˢ-refl {xs ─ ∅} ⟩
        xs ─ ∅ ≈⟨ ∅─-identityʳ xs ⟩
        xs ∎
  where open ≈ˢ-Reasoning

∩-comm : Commutative _∩_
∩-comm s s′ = uncurry (∈-∩⁺ _ s′ s) ∘ Product.swap ∘ ∈-∩⁻ _ s s′
            , uncurry (∈-∩⁺ _ s s′) ∘ Product.swap ∘ ∈-∩⁻ _ s′ s

∪-∅ : (Xs ∪ Ys) ≈ˢ ∅ → (Xs ≈ˢ ∅) × (Ys ≈ˢ ∅)
∪-∅ {Xs}{Ys} p = (≈ˢ⇒⊆ˢ {Xs ∪ Ys}{∅} p ∘ ∈-∪⁺ˡ _ Xs Ys , λ ())
               , (≈ˢ⇒⊆ˢ {Xs ∪ Ys}{∅} p ∘ ∈-∪⁺ʳ _ Xs Ys , λ ())

∪-∅ˡ : (Xs ∪ Ys) ≈ˢ ∅ → Xs ≈ˢ ∅
∪-∅ˡ {Xs}{Ys} = proj₁ ∘ ∪-∅ {Xs}{Ys}

∪-∅ʳ : (Xs ∪ Ys) ≈ˢ ∅ → Ys ≈ˢ ∅
∪-∅ʳ {Xs}{Ys} = proj₂ ∘ ∪-∅ {Xs}{Ys}

∪-∩ : ((Xs ∪ Ys) ∩ Zs) ≈ˢ ((Xs ∩ Zs) ∪ (Ys ∩ Zs))
∪-∩ {Xs}{Ys}{Zs} =
  (λ x∈ →
  let x∈∪ , x∈Zs = ∈-∩⁻ _ (Xs ∪ Ys) Zs x∈
  in  case ∈-∪⁻ _ Xs Ys x∈∪ of λ where
        (inj₁ x∈Xs) → ∈-∪⁺ˡ _ (Xs ∩ Zs) (Ys ∩ Zs)
                              (∈-∩⁺ _ Xs Zs x∈Xs x∈Zs)
        (inj₂ x∈Ys) → ∈-∪⁺ʳ _ (Xs ∩ Zs) (Ys ∩ Zs)
                              (∈-∩⁺ _ Ys Zs x∈Ys x∈Zs))
  , (∈-∪⁻ _ (Xs ∩ Zs) (Ys ∩ Zs) >≡> λ where
       (inj₁ x∈) → let x∈Xs , x∈Zs = ∈-∩⁻ _ Xs Zs x∈
                   in ∈-∩⁺ _ (Xs ∪ Ys) Zs (∈-∪⁺ˡ _ Xs Ys x∈Xs) x∈Zs
       (inj₂ x∈) → let x∈Ys , x∈Zs = ∈-∩⁻ _ Ys Zs x∈
                   in ∈-∩⁺ _ (Xs ∪ Ys) Zs (∈-∪⁺ʳ _ Xs Ys x∈Ys) x∈Zs)

-- ** apartness
instance
  Apart-Set' : Set' // Set'
  -- Apart-Set' ._♯_ s s′ = ∀ {k} → ¬ (k ∈ˢ s × k ∈ˢ s′)
  Apart-Set' ._♯_ s s′ = (s ∩ s′) ≈ˢ ∅

_♯?ˢ_ = Decidable² (_♯_ {A = Set'}) ∋ dec²

-- ♯-comm : Symmetric _♯_
♯-comm : ∀ (x y : Set') → x ♯ y → y ♯ x
♯-comm x y = ≈ˢ-trans {i = y ∩ x}{j = x ∩ y}{k = ∅} (∩-comm y x)

∈-∩⇒¬♯ : x ∈ˢ (Xs ∩ Ys) → ¬ (Xs ♯ Ys)
∈-∩⇒¬♯ {Xs = Xs}{Ys} x∈ xs♯ys = contradict (≈ˢ⇒⊆ˢ {s = Xs ∩ Ys} {s′ = ∅} xs♯ys x∈)

♯-skipˡ : ∀ xs ys (zs : Set') → (xs ∪ ys) ♯ zs → ys ♯ zs
♯-skipˡ xs ys zs p = ∪-∅ {xs ∩ zs}{ys ∩ zs}
  (let open ≈ˢ-Reasoning in
   begin
    (xs ∩ zs) ∪ (ys ∩ zs)
   ≈˘⟨ ∪-∩ {xs}{ys}{zs} ⟩
    (xs ∪ ys) ∩ zs
   ≈⟨ p ⟩
     ∅
   ∎)
  .proj₂


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
  field set   : Set'
        .set⁺ : ∣ set ∣ > 0
syntax Set'⁺ {A = A} = Set⁺⟨ A ⟩

instance
  DecEq-Set'⁺ : DecEq Set'⁺
  DecEq-Set'⁺ ._≟_ (s ⊣ _) (s′ ⊣ _) with s ≟ s′
  ... | yes refl = yes refl
  ... | no  ¬eq  = no λ where refl → ¬eq refl

mkSet⁺ : (s : Set') ⦃ _ : True (∣ s ∣ >? 0) ⦄ → Set'⁺
mkSet⁺ s ⦃ pr ⦄ = s ⊣ toWitness pr

fromList⁺ : (xs : List A) ⦃ _ : True (length (nub xs) >? 0) ⦄ → Set'⁺
fromList⁺ = mkSet⁺ ∘ fromList

toList'⁺ : Set'⁺ → List⁺ A
toList'⁺ (s ⊣ _) with x ∷ xs ← list s = x ∷ xs

-- instance
--   Semigroup-Set' : ⦃ Semigroup A ⦄ → Semigroup Set'
--   Semigroup-Set' ._◇_ s@(xs ⊣ p) s′@(ys ⊣ p′) = {!!}
