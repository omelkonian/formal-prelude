------------------------------------------------------------------------
-- Sets as unique lists.
------------------------------------------------------------------------

open import Prelude.Init; open SetAsType
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
open import Prelude.Null
open import Prelude.Setoid

module Prelude.Sets.AsUniqueLists.Core {A : Type} ⦃ _ : DecEq A ⦄ where

-- ** basic definitions

-- Sets as lists with no duplicates.
record Set' : Set where
  constructor _⊣_
  field list  : List A
        .uniq : Unique list

  .set-∈-irr : ∀ {x : A} → Irrelevant (x ∈ list)
  set-∈-irr = ∈-irr uniq

open Set'
syntax Set' {A = A} = Set⟨ A ⟩

private variable
  x x′ y y′ z z′ : A
  xs ys zs : List A
  Xs Ys Zs s s′ s″ : Set'
  P : Pred A 0ℓ

-- ** Lifting from list predicates/relations to set predicates/relations.
private
  record Lift (F : Type → Type₁) : Type₁ where
    field ↑ : F (List A) → F Set'
  open Lift ⦃...⦄

  instance
    Lift-Pred : Lift Pred₀
    Lift-Pred .↑ P = P ∘ list

    Lift-Rel : Lift Rel₀
    Lift-Rel .↑ _~_ = _~_ on list

-- e.g. All/Any predicates for sets
Allˢ Anyˢ : Pred₀ A → Pred₀ Set'
Allˢ = ↑ ∘ All
Anyˢ = ↑ ∘ Any

allˢ? : Decidable¹ P → Decidable¹ (Allˢ P)
allˢ? P? = all? P? ∘ list

anyˢ? : Decidable¹ P → Decidable¹ (Anyˢ P)
anyˢ? P? = any? P? ∘ list

infixr 8 _─_
infixr 7 _∩_
infixr 6 _∪_
infix  4 _∈ˢ_ _∉ˢ_ _∈ˢ?_ _∉ˢ?_
infix  2 _≈ˢ_

_∈ˢ_ _∉ˢ_ : A → Set' → Type
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

pattern ∅ = [] ⊣ []

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
... | yes x∈ = ∈-∪⁺ˡ x xs ys x∈
... | no  x∉ = ∈-++⁺ʳ (list xs) (∈-filter⁺ (_∉ˢ? xs) x∈ x∉)

destruct-∈ˢ-∪ : ∀ l r {x} (x∈ : x ∈ˢ l ∪ r) →
    (∃ λ (x∈ˡ : x ∈ˢ l) → x∈ ≡ ∈-∪⁺ˡ _ l r x∈ˡ)
  ⊎ (∃ λ (x∈ʳ : x ∈ˢ r) → x∈ ≡ ∈-∪⁺ʳ _ l r x∈ʳ)
destruct-∈ˢ-∪ l r {x} x∈
  with destruct-∈-++ x∈
... | inj₁ (x∈ˡ , x∈≡) = inj₁ (x∈ˡ , x∈≡)
... | inj₂ (x∈ʳ , x∈≡)
  with ∈-filter⁻ (_∉ˢ? l) {xs = list r} x∈ʳ in x∈ʳ≡
... | x∈ʳ′ , x∉ˡ
  with x ∈? list l
... | yes x∈ˡ = ⊥-elim $ x∉ˡ x∈ˡ
... | no x∉
  = inj₂
  $ x∈ʳ′
  , (begin
        x∈
      ≡⟨ x∈≡ ⟩
        ∈-++⁺ʳ (list l) x∈ʳ
      ≡⟨ cong (∈-++⁺ʳ (list l)) $ ∈-filter⁻∙proj₁-injective (_∉ˢ? l) _ _ $
         begin
           ∈-filter⁻ (_∉ˢ? l) x∈ʳ .proj₁
         ≡⟨ cong proj₁ x∈ʳ≡ ⟩
           x∈ʳ′
         ≡˘⟨ destruct-∈-filter (_∉ˢ? l) x∈ʳ′ x∉ ⟩
           ∈-filter⁻ (_∉ˢ? l) (∈-filter⁺ (_∉ˢ? l) x∈ʳ′ x∉) .proj₁
         ∎ ⟩
        ∈-++⁺ʳ (list l) (∈-filter⁺ (_∉ˢ? l) x∈ʳ′ x∉)
      ∎
    ) where open ≡-Reasoning

∈-∩⁺ : ∀ x xs ys → x ∈ˢ xs → x ∈ˢ ys → x ∈ˢ (xs ∩ ys)
∈-∩⁺ _ _ ys = ∈-filter⁺ ((_∈ˢ? ys))

∈-∩⁻ : ∀ x xs ys → x ∈ˢ (xs ∩ ys) → (x ∈ˢ xs) × (x ∈ˢ ys)
∈-∩⁻ _ xs ys = ∈-filter⁻ (_∈ˢ? ys) {xs = list xs}

-- ** derived operations

open Derive-⊆-from-∈ _∈ˢ_ public renaming
  ( _⊆_ to _⊆ˢ_; _⊈_ to _⊈ˢ_; ⊆-trans to ⊆ˢ-trans
  ; _⊇_ to _⊇ˢ_; _⊉_ to _⊉ˢ_; ⊇-trans to ⊇ˢ-trans
  )

_⊆?ˢ_ = Decidable² _⊆ˢ_ ∋ dec²

-- ** algebraic properties
instance
  Setoid-Set : ISetoid Set'
  Setoid-Set = λ where
    .relℓ → _
    ._≈_ s s′ → (s ⊆ˢ s′) × (s′ ⊆ˢ s)

  SetoidLaws-Set : Setoid-Laws Set'
  SetoidLaws-Set .isEquivalence = record
    { refl  = id , id
    ; sym   = Product.swap
    ; trans = λ where (ij , ji) (jk , kj) → jk ∘ ij , ji ∘ kj
    }

  Nullable-Set : Nullable Set'
  Nullable-Set .Null = _≈ ∅

_≈ˢ_ = Rel₀ Set' ∋ _≈_
module ≈ˢ-Reasoning = ≈-Reasoning {A = Set'}
open Alg _≈ˢ_

.≈ˢ-cancel : ∀ s s′ (p : s ≈ˢ s′) (x∈ : x ∈ˢ s) →
  p .proj₂ (p .proj₁ x∈) ≡ x∈
≈ˢ-cancel s s′ p x∈ = set-∈-irr s (p .proj₂ $ p .proj₁ x∈) x∈

≈⇒⊆ˢ : s ≈ s′ → s ⊆ˢ s′
≈⇒⊆ˢ = proj₁

≈⇒⊆ˢ˘ : s ≈ s′ → s′ ⊆ˢ s
≈⇒⊆ˢ˘ = proj₂

∅─-identityʳ : RightIdentity ∅ _─_
∅─-identityʳ s rewrite L.filter-all (_∉? []) {xs = list s} All∉[] = ≈-refl {x = s}

∅∪-identityˡ : LeftIdentity ∅ _∪_
∅∪-identityˡ xs =
  begin ∅ ∪ xs ≈⟨ ≈-refl {x = xs ─ ∅} ⟩
        xs ─ ∅ ≈⟨ ∅─-identityʳ xs ⟩
        xs ∎ where open ≈ˢ-Reasoning

∩-comm : Commutative _∩_
∩-comm s s′ = uncurry (∈-∩⁺ _ s′ s) ∘ Product.swap ∘ ∈-∩⁻ _ s s′
            , uncurry (∈-∩⁺ _ s s′) ∘ Product.swap ∘ ∈-∩⁻ _ s′ s

∪-∅ : (Xs ∪ Ys) ≈ ∅ → (Xs ≈ ∅) × (Ys ≈ ∅)
∪-∅ {Xs}{Ys} p = (≈⇒⊆ˢ {Xs ∪ Ys}{∅} p ∘ ∈-∪⁺ˡ _ Xs Ys , λ ())
               , (≈⇒⊆ˢ {Xs ∪ Ys}{∅} p ∘ ∈-∪⁺ʳ _ Xs Ys , λ ())

∪-∅ˡ : (Xs ∪ Ys) ≈ ∅ → Xs ≈ ∅
∪-∅ˡ {Xs}{Ys} = proj₁ ∘ ∪-∅ {Xs}{Ys}

∪-∅ʳ : (Xs ∪ Ys) ≈ ∅ → Ys ≈ ∅
∪-∅ʳ {Xs}{Ys} = proj₂ ∘ ∪-∅ {Xs}{Ys}

∪-∩ : ((Xs ∪ Ys) ∩ Zs) ≈ ((Xs ∩ Zs) ∪ (Ys ∩ Zs))
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
  Apart-Set : Set' // Set'
  Apart-Set ._♯_ s s′ = s ∩ s′ ≈ ∅

_♯ˢ_  = Rel₀ Set'       ∋ _♯_
_♯ˢ?_ = Decidable² _♯ˢ_ ∋ dec²

-- ** alternative formulation of _♯_
_♯′_ : Rel₀ Set'
s ♯′ s′ = ∀ {k} → ¬ (k ∈ˢ s × k ∈ˢ s′)

♯⇔♯′ : ∀ x y →
  x ♯ y
  ═══════
  x ♯′ y
♯⇔♯′ x  y = ♯⇒♯′ , ♯′⇒♯
  module _ where
    ♯⇒♯′ : x ♯ y → x ♯′ y
    ♯⇒♯′ (⊆∅ , _) = ∉∅ _ ∘ ⊆∅ ∘ uncurry (∈-∩⁺ _ x y)

    ♯′⇒♯ : x ♯′ y → x ♯ y
    ♯′⇒♯ x♯y = (⊥-elim ∘ x♯y ∘ ∈-∩⁻  _ x y) , ⊥-elim ∘ ∉∅ _

-- ** properties of _♯_
♯-comm : ∀ x y → x ♯′ y → y ♯′ x
♯-comm x y x♯y = x♯y ∘ Product.swap

♯′-comm : ∀ x y → x ♯ˢ y → y ♯ˢ x
♯′-comm x y = ♯′⇒♯ y x ∘ ♯-comm x y ∘ ♯⇒♯′ x y

∈-∩⇒¬♯ : ∀ x xs ys → x ∈ˢ (xs ∩ ys) → ¬ (xs ♯′ ys)
∈-∩⇒¬♯ x xs ys x∈ xs♯ys = xs♯ys $ ∈-∩⁻ _ xs ys x∈

∈-∩⇒¬♯′ : ∀ x xs ys → x ∈ˢ (xs ∩ ys) → ¬ (xs ♯ ys)
∈-∩⇒¬♯′ x xs ys x∈ = ∈-∩⇒¬♯ x xs ys x∈ ∘ ♯⇒♯′ xs ys

♯-skipˡ : ∀ xs ys (zs : Set') → (xs ∪ ys) ♯′ zs → ys ♯′ zs
♯-skipˡ xs ys _ p (x∈ys , x∈zs) = p (∈-∪⁺ʳ _ xs ys x∈ys , x∈zs)

♯′-skipˡ : ∀ xs ys (zs : Set') → (xs ∪ ys) ♯ zs → ys ♯ zs
♯′-skipˡ xs ys zs = ♯′⇒♯ ys zs ∘ ♯-skipˡ xs ys zs ∘ ♯⇒♯′ (xs ∪ ys) zs

-- ** list conversion
instance
  ToList-Set : ToList Set' A
  ToList-Set .toList = list

  FromList-Set : FromList A Set'
  FromList-Set .fromList xs = nub xs ⊣ Unique-nub {xs = xs}

from↔to : ∀ xs → Unique xs → toList (fromList {B = Set'} xs) ≡ xs
from↔to _ Uxs rewrite nub-from∘to Uxs = refl

∈ˢ-fromList : x ∈ xs ↔ x ∈ˢ fromList xs
∈ˢ-fromList = ∈-nub⁺ , ∈-nub⁻

∈ˢ-fromList⁺ : x ∈ xs → x ∈ˢ fromList xs
∈ˢ-fromList⁺ = ∈ˢ-fromList .proj₁

∈ˢ-fromList⁻ : x ∈ˢ fromList xs → x ∈ xs
∈ˢ-fromList⁻ = ∈ˢ-fromList .proj₂

-- ** decidability of set equality
instance
  DecEq-Set : DecEq Set'
  DecEq-Set ._≟_ s s′ with list s ≟ list s′
  ... | no ¬p    = no λ where refl → ¬p refl
  ... | yes refl = yes refl

  Measurable-Set : Measurable Set'
  Measurable-Set = record {∣_∣ = length ∘ list}

record Set'⁺ : Set where
  constructor _⊣_
  field set   : Set'
        .set⁺ : ∣ set ∣ > 0
syntax Set'⁺ {A = A} = Set⁺⟨ A ⟩

instance
  DecEq-Set⁺ : DecEq Set'⁺
  DecEq-Set⁺ ._≟_ (s ⊣ _) (s′ ⊣ _) with s ≟ s′
  ... | yes refl = yes refl
  ... | no  ¬eq  = no λ where refl → ¬eq refl

mkSet⁺ : (s : Set') ⦃ _ : True (∣ s ∣ >? 0) ⦄ → Set'⁺
mkSet⁺ s ⦃ pr ⦄ = s ⊣ toWitness pr

fromList⁺ : (xs : List A) ⦃ _ : True (length (nub xs) >? 0) ⦄ → Set'⁺
fromList⁺ = mkSet⁺ ∘ fromList

toList'⁺ : Set'⁺ → List⁺ A
toList'⁺ (s ⊣ _) with x ∷ xs ← list s = x ∷ xs

{-
instance
  Semigroup-Set : ∀ {A} ⦃ _ : DecEq A ⦄ → Semigroup Set⟨ A ⟩
  Semigroup-Set ._◇_ = _∪_

  Functor-Set' : Functor {0ℓ} λ A {{_ : DecEq A}} → Set⟨ A ⟩
  Functor-Set' ._<$>_ f = (f <$>_) ∘ list

  PFunctor-Set : PointedFunctor λ A ⦃ _ : DecEq A ⦄ → Set⟨ A ⟩
  PFunctor-Set .point = singleton
-}
