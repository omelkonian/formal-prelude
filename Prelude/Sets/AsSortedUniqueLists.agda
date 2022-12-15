{-# OPTIONS --with-K #-}
open import Data.List.Relation.Unary.Linked using ([])

open import Prelude.Init; open SetAsType
open L.Mem using (∈-filter⁻; ∈-filter⁺; ∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.ToList
open import Prelude.FromList
open import Prelude.Lists.Dec
open import Prelude.Ord
open import Prelude.Irrelevance hiding (_─_)
open import Prelude.Irrelevance.Dec
open import Prelude.Membership
open import Prelude.Lists
open import Prelude.Lists.WithK
open import Prelude.Bifunctor
open import Prelude.Setoid
open import Prelude.Null
open import Prelude.Apartness
open import Prelude.InferenceRules
open import Prelude.Measurable

module Prelude.Sets.AsSortedUniqueLists {A : Type ℓ} ⦃ _ : DecEq A ⦄ ⦃ _ : Ord⁺⁺ A ⦄ where

Set' : Type _
Set' = Σ (List A) (Sorted Unary.∩ ·Unique)
syntax Set' {A = A} = Set⟨ A ⟩

pattern ∅ = [] , [] , []

private variable
  x x′ : A
  xs ys : List A
  Xs Ys Zs s s′ : Set'
  R : Rel A ℓ′
  P : Pred A ℓ′


mkSet≡ : Xs .proj₁ ≡ Ys .proj₁ → Xs ≡ Ys
mkSet≡ {_ , p} {_ , p′} refl rewrite ∀≡ p p′ = refl

unmkSet≡ : Xs ≡ Ys → Xs .proj₁ ≡ Ys .proj₁
unmkSet≡ refl = refl

instance
  DecEq-Sorted : DecEq (Sorted xs)
  DecEq-Sorted = Irrelevant⇒DecEq ∀≡

  DecEq-Unique : DecEq (·Unique xs)
  DecEq-Unique = Irrelevant⇒DecEq ∀≡

  -- DecEq-Set : DecEq Set'
  -- DecEq-Set ._≟_ (xs , _) (ys , _) = Nullary.map′ mkSet≡ unmkSet≡ (xs ≟ ys)

  Setoid-Set : ISetoid Set'
  Setoid-Set = mkISetoid≡

  SetoidLaws-Set : SetoidLaws Set'
  SetoidLaws-Set = mkSetoidLaws≡

  Nullable-Set : Nullable Set'
  Nullable-Set .Null = _≡ ∅

  ToList-Set : ToList Set' A
  ToList-Set .toList = proj₁

  FromList-Set : FromList A Set'
  FromList-Set .fromList xs
    = sort (nub xs)
    , sort-↗ (nub xs)
    , Unique⇒·Unique (Unique-sort⁺ $ Unique-nub {xs = xs})

  Measurable-Set : Measurable Set'
  Measurable-Set = record {∣_∣ = length ∘ toList}

  Ord-Set : Ord Set'
  Ord-Set = mkOrd≈ toList

  DecOrd-Set : DecOrd Set'
  DecOrd-Set = mkDecOrd≈ toList

  OrdLaws-Set : OrdLaws Set'
  OrdLaws-Set = mkOrdLaws≈ toList mkSet≡ unmkSet≡

-- ** Lifting from list predicates/relations to set predicates/relations.
private
  record Lift (F : ∀ {ℓ} → Type ℓ → (ℓ′ : Level) → Type (ℓ ⊔ₗ lsuc ℓ′)) : Typeω where
    field ↑ : F (List A) ℓ → F Set' ℓ
  open Lift ⦃...⦄

  instance
    Lift-Pred : Lift Pred
    Lift-Pred .↑ P = P ∘ toList

    Lift-Rel : Lift Rel
    Lift-Rel .↑ _~_ = _~_ on toList

-- e.g. All/Any predicates for sets
Allˢ Anyˢ : Pred A ℓ → Pred Set' ℓ
Allˢ = ↑ ∘ All
Anyˢ = ↑ ∘ Any

allˢ? : Decidable¹ P → Decidable¹ (Allˢ P)
allˢ? P? = all? P? ∘ toList

anyˢ? : Decidable¹ P → Decidable¹ (Anyˢ P)
anyˢ? P? = any? P? ∘ toList

infixr 8 _─_
infixr 7 _∩_
infixr 6 _∪_
infix  4 _∈ˢ_ _∉ˢ_ _∈ˢ?_ _∉ˢ?_
infix  2 _≈ˢ_

_∈ˢ_ _∉ˢ_ : A → Set' → Type _
o ∈ˢ (os , _) = o ∈ os
o ∉ˢ s = ·¬ (o ∈ˢ s)

private
  _·∉_ : A → List A → Type _
  x ·∉ xs = ·¬ (x ∈ xs)

  _·∉?_ : ∀ x xs → Dec (x ·∉ xs)
  _·∉?_ = ·¬? ∘₂ _∈?_

∈ˢ-irr : Irrelevant (x ∈ˢ Xs)
∈ˢ-irr {Xs = _ , _ , uniq} = ∈-irr (·Unique⇒Unique uniq)

private
  infix 0 _⊣_
  _⊣_ : (xs : List A) → ·Unique xs → Set'
  xs ⊣ uniq-xs = sort xs , sort-↗ xs , ·Unique-sort⁺ uniq-xs

_∷_∶-_ : (x : A) → (xs : Set') → x ∉ˢ xs → Set'
x ∷ (xs , _ , uniq-xs) ∶- x∉
  = x ∷ xs
  ⊣ L.All.map ¬⇒·¬ (L.All.¬Any⇒All¬ _ (·¬⇒¬ x∉)) ∷ uniq-xs

_<$>_∶-_ : (f : A → A) → Set' → (∀ {x y} → f x ≡ f y → x ≡ y) → Set'
f <$> (xs , _ , uniq-xs) ∶- inj
  = map f xs
  ⊣ ·Unique-map⁺ inj uniq-xs

filter′ : Decidable¹ P → Set' → Set'
-- filter′ P? (xs , _ , p) = filter P? xs ⊣ ·Unique-filter⁺ P? p
filter′ P? (xs , sorted-xs , uniq-xs)
  = filter P? xs
  , Sorted-filter⁺ P? sorted-xs
  , ·Unique-filter⁺ P? uniq-xs

-- ** decidability
_∈ˢ?_ : Decidable² _∈ˢ_
o ∈ˢ? (os , _) = o ∈? os
_∉ˢ?_ : Decidable² _∉ˢ_
o ∉ˢ? (os , _) = ·¬? (o ∈? os)

count′ : Decidable¹ P → Set' → ℕ
count′ P? = count P? ∘ toList

singleton : A → Set'
singleton a = [ a ] ⊣ ([] ∷ [])

singleton∈ˢ : x′ ∈ˢ singleton x ↔ x′ ≡ x
singleton∈ˢ = (λ where (here refl) → refl) , (λ where refl → here refl)

_++_∶-_ : ∀ (s s′ : Set') → Disjoint (toList s) (toList s′) → Set'
(xs , sorted-xs , uniq-xs) ++ (ys , sorted-ys , uniq-ys) ∶- dsj =
  (xs ++ ys) ⊣ ·Unique-++⁺ uniq-xs uniq-ys dsj

_∪_ _∩_ _─_ : Op₂ Set'
x ─ y = filter′ (_∉ˢ? y) x
x ∩ y = filter′ (_∈ˢ? y) x
x ∪ y = x ++ (filter′ (_∉ˢ? x) y) ∶- disjoint-─ {xs = toList x} {ys = toList y}
  where
    disjoint-─ : Disjoint xs (filter (_·∉? xs) ys)
    disjoint-─ {xs = xs} {ys = ys} (x∈ , x∈ˢ)
      = let _ , x∉ = ∈-filter⁻ (_·∉? xs) {xs = ys} x∈ˢ
        in  ·¬⇒¬ x∉ x∈

⋃ : (A → Set') → Set' → Set'
⋃ f = foldr _∪_ ∅ ∘ map f ∘ toList

-- ** relational properties
∉∅ : ∀ x → ¬ x ∈ˢ ∅
∉∅ _ ()

∈-─⁻ : ∀ x xs ys → x ∈ˢ (xs ─ ys) → x ∈ˢ xs
∈-─⁻ x xs ys x∈ = proj₁ (∈-filter⁻ (_∉ˢ? ys) x∈)

∈-─⁺ : ∀ x xs ys → x ∈ˢ xs → x ∉ˢ ys → x ∈ˢ (xs ─ ys)
∈-─⁺ x xs ys x∈ x∉ = ∈-filter⁺ ((_∉ˢ? ys)) x∈ x∉

∈-∪⁻ : ∀ x xs ys → x ∈ˢ (xs ∪ ys) → x ∈ˢ xs ⊎ x ∈ˢ ys
∈-∪⁻ x xs ys x∈ = map₂ (∈-─⁻ x ys xs) $ ∈-++⁻ {v = x} _ (∈-sort⁻ x∈)

∈-∪⁺ˡ : ∀ x xs ys → x ∈ˢ xs → x ∈ˢ (xs ∪ ys)
∈-∪⁺ˡ x xs ys x∈ = ∈-sort⁺ $ ∈-++⁺ˡ x∈

∈-∪⁺ʳ : ∀ x xs ys → x ∈ˢ ys → x ∈ˢ (xs ∪ ys)
∈-∪⁺ʳ x xs ys x∈ with ·¿ x ∈ˢ xs ¿
... | yes x∈ = ∈-∪⁺ˡ x xs ys x∈
... | no  x∉ = ∈-sort⁺ (∈-++⁺ʳ (toList xs) (∈-filter⁺ (_∉ˢ? xs) x∈ x∉))

∈-∩⁺ : ∀ x xs ys → x ∈ˢ xs → x ∈ˢ ys → x ∈ˢ (xs ∩ ys)
∈-∩⁺ _ _ ys = ∈-filter⁺ ((_∈ˢ? ys))

∈-∩⁻ : ∀ x xs ys → x ∈ˢ (xs ∩ ys) → (x ∈ˢ xs) × (x ∈ˢ ys)
∈-∩⁻ _ xs ys = ∈-filter⁻ (_∈ˢ? ys) {xs = toList xs}

-- ** derived operations

open Derive-⊆-from-∈ _∈ˢ_ public renaming
  ( _⊆_ to _⊆ˢ_; _⊈_ to _⊈ˢ_; ⊆-trans to ⊆ˢ-trans
  ; _⊇_ to _⊇ˢ_; _⊉_ to _⊉ˢ_; ⊇-trans to ⊇ˢ-trans
  )

_⊆?ˢ_ = Decidable² _⊆ˢ_ ∋ dec²

-- ** algebraic properties

_≈ˢ_ = Rel Set' _ ∋ _≡_
module ≈ˢ-Reasoning = ≡-Reasoning {A = Set'}
open Alg _≈ˢ_

≈⇒⊆ˢ : s ≈ s′ → s ⊆ˢ s′
≈⇒⊆ˢ refl = id

≈⇒⊆ˢ˘ : s ≈ s′ → s′ ⊆ˢ s
≈⇒⊆ˢ˘ refl = id

∅─-identityʳ : RightIdentity ∅ _─_
∅─-identityʳ _ = mkSet≡ $ L.filter-all (_·∉? []) (L.All.map ¬⇒·¬ All∉[])

∅∪-identityˡ : LeftIdentity ∅ _∪_
∅∪-identityˡ xs@(_ , sorted-xs , _)=
  begin ∅ ∪ xs ≡⟨ mkSet≡ $ Sorted⇒sort-id $ Sorted-filter⁺ (_·∉? []) sorted-xs ⟩
        xs ─ ∅ ≈⟨ ∅─-identityʳ xs ⟩
        xs ∎ where open ≈-Reasoning

-- ∩-comm : Commutative _∩_
-- ∩-comm s s′ = uncurry (∈-∩⁺ _ s′ s) ∘ Product.swap ∘ ∈-∩⁻ _ s s′
--             , uncurry (∈-∩⁺ _ s s′) ∘ Product.swap ∘ ∈-∩⁻ _ s′ s

∪-∅ : (Xs ∪ Ys) ≈ ∅ → (Xs ≈ ∅) × (Ys ≈ ∅)
∪-∅ {xs , _}{ys , _} eq
  with eqˡ , eqʳ ← Null-++ {xs = xs} $ Null-sort⁻ $ unmkSet≡ eq
  rewrite eqˡ
  = mkSet≡ refl
  , mkSet≡ (subst (_≡ []) (L.filter-all (_·∉? []) (L.All.map ¬⇒·¬ All∉[])) eqʳ)

∪-∅ˡ : (Xs ∪ Ys) ≈ ∅ → Xs ≈ ∅
∪-∅ˡ {Xs}{Ys} = proj₁ ∘ ∪-∅ {Xs}{Ys}

∪-∅ʳ : (Xs ∪ Ys) ≈ ∅ → Ys ≈ ∅
∪-∅ʳ {Xs}{Ys} = proj₂ ∘ ∪-∅ {Xs}{Ys}

-- ∪-∩ : ((Xs ∪ Ys) ∩ Zs) ≈ ((Xs ∩ Zs) ∪ (Ys ∩ Zs))
-- ∪-∩ {Xs}{Ys}{Zs} =
--   (λ x∈ →
--   let x∈∪ , x∈Zs = ∈-∩⁻ _ (Xs ∪ Ys) Zs x∈
--   in  case ∈-∪⁻ _ Xs Ys x∈∪ of λ where
--         (inj₁ x∈Xs) → ∈-∪⁺ˡ _ (Xs ∩ Zs) (Ys ∩ Zs)
--                               (∈-∩⁺ _ Xs Zs x∈Xs x∈Zs)
--         (inj₂ x∈Ys) → ∈-∪⁺ʳ _ (Xs ∩ Zs) (Ys ∩ Zs)
--                               (∈-∩⁺ _ Ys Zs x∈Ys x∈Zs))
--   , (∈-∪⁻ _ (Xs ∩ Zs) (Ys ∩ Zs) >≡> λ where
--        (inj₁ x∈) → let x∈Xs , x∈Zs = ∈-∩⁻ _ Xs Zs x∈
--                    in ∈-∩⁺ _ (Xs ∪ Ys) Zs (∈-∪⁺ˡ _ Xs Ys x∈Xs) x∈Zs
--        (inj₂ x∈) → let x∈Ys , x∈Zs = ∈-∩⁻ _ Ys Zs x∈
--                    in ∈-∩⁺ _ (Xs ∪ Ys) Zs (∈-∪⁺ʳ _ Xs Ys x∈Ys) x∈Zs)

-- ** apartness
instance
  Apart-Set : Set' // Set'
  Apart-Set ._♯_ s s′ = s ∩ s′ ≈ ∅

_♯ˢ_  = Rel Set' _ ∋ _♯_
_♯ˢ?_ = Decidable² _♯ˢ_ ∋ dec²

-- ** alternative formulation of _♯_
_♯′_ : Rel Set' _
s ♯′ s′ = ∀ {k} → ·¬ (k ∈ˢ s × k ∈ˢ s′)

♯⇔♯′ : ∀ x y →
  x ♯ y
  ═══════
  x ♯′ y
♯⇔♯′ x y = ♯⇒♯′ , ♯′⇒♯
  module _ where
    ♯⇒♯′ : x ♯ y → x ♯′ y
    ♯⇒♯′ p {k} (k∈ , k∈′) = ⊥-elim $ ∉∅ _ $ subst (k ∈ˢ_) p (∈-∩⁺ k x y k∈ k∈′)

    ♯′⇒♯ : x ♯′ y → x ♯ y
    ♯′⇒♯ p = mkSet≡
           $ L.filter-none (_∈? y .proj₁)
           $ L.All.tabulate λ {k} k∈ k∈′ → ·⊥⇒⊥ $ p (k∈ , k∈′ )

-- ** properties of _♯_
♯-comm : ∀ x y → x ♯′ y → y ♯′ x
♯-comm x y x♯y = x♯y ∘ Product.swap

♯′-comm : ∀ x y → x ♯ˢ y → y ♯ˢ x
♯′-comm x y = ♯′⇒♯ y x ∘ ♯-comm x y ∘ ♯⇒♯′ x y

∈-∩⇒¬♯ : ∀ x xs ys → x ∈ˢ (xs ∩ ys) → ¬ (xs ♯′ ys)
∈-∩⇒¬♯ x xs ys x∈ xs♯ys = ·¬⇒¬ xs♯ys $ ∈-∩⁻ _ xs ys x∈

∈-∩⇒¬♯′ : ∀ x xs ys → x ∈ˢ (xs ∩ ys) → ¬ (xs ♯ ys)
∈-∩⇒¬♯′ x xs ys x∈ = ∈-∩⇒¬♯ x xs ys x∈ ∘ ♯⇒♯′ xs ys

♯-skipˡ : ∀ xs ys (zs : Set') → (xs ∪ ys) ♯′ zs → ys ♯′ zs
♯-skipˡ xs ys _ p (x∈ys , x∈zs) = p (∈-∪⁺ʳ _ xs ys x∈ys , x∈zs)

♯′-skipˡ : ∀ xs ys (zs : Set') → (xs ∪ ys) ♯ zs → ys ♯ zs
♯′-skipˡ xs ys zs = ♯′⇒♯ ys zs ∘ ♯-skipˡ xs ys zs ∘ ♯⇒♯′ (xs ∪ ys) zs

private
  to   = (Set' → List A) ∋ toList
  from = (List A → Set') ∋ fromList

-- from↔to : ∀ xs → Unique xs → to (from xs) ≡ xs
-- from↔to _ Uxs rewrite nub-from∘to Uxs = refl

Anyˢ-fromList⁺ : Any P xs → Anyˢ P (from xs)
Anyˢ-fromList⁺ = L.Perm.Any-resp-↭ (↭-sym $ sort-↭ _) ∘ Any-nub⁺

Anyˢ-fromList⁻ : Anyˢ P (from xs) → Any P xs
Anyˢ-fromList⁻ = Any-nub⁻ ∘ L.Perm.Any-resp-↭ (sort-↭ _)

Anyˢ-fromList : Any P xs ↔ Anyˢ P (from xs)
Anyˢ-fromList = Anyˢ-fromList⁺ , Anyˢ-fromList⁻

∈ˢ-fromList⁺ : x ∈ xs → x ∈ˢ fromList xs
∈ˢ-fromList⁺ = ∈-sort⁺ ∘ ∈-nub⁺

∈ˢ-fromList⁻ : x ∈ˢ fromList xs → x ∈ xs
∈ˢ-fromList⁻ = ∈-nub⁻ ∘ ∈-sort⁻

∈ˢ-fromList : x ∈ xs ↔ x ∈ˢ fromList xs
∈ˢ-fromList = ∈ˢ-fromList⁺ , ∈ˢ-fromList⁻

Set'⁺ = Σ₀ Set' λ s → ∣ s ∣ > 0
pattern _⊣⁺_ x y = _,₀_ x y
syntax Set'⁺ {A = A} = Set⁺⟨ A ⟩

instance
  DecEq-Set⁺ : DecEq Set'⁺
  DecEq-Set⁺ ._≟_ (s ⊣⁺ _) (s′ ⊣⁺ _) with s ≟ s′
  ... | yes refl = yes refl
  ... | no  ¬eq  = no λ where refl → ¬eq refl

mkSet⁺ : (s : Set') ⦃ _ : True (∣ s ∣ >? 0) ⦄ → Set'⁺
mkSet⁺ s ⦃ pr ⦄ = s ⊣⁺ toWitness pr

fromList⁺ : (xs : List A) ⦃ _ : True (length (nub xs) >? 0) ⦄ → Set'⁺
fromList⁺ xs ⦃ p ⦄ = mkSet⁺ (fromList xs)
  ⦃ fromWitness
  $ subst (_> 0)
          (sym $ L.Perm.↭-length $ sort-↭ $ nub xs)
          (toWitness p)
  ⦄

toList'⁺ : Set'⁺ → List⁺ A
toList'⁺ (s ⊣⁺ _) with x ∷ xs ← toList s = x ∷ xs
