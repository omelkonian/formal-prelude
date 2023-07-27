{-# OPTIONS --with-K #-}
open import Prelude.Init; open SetAsType
open L.Mem using (∈-filter⁻; ∈-filter⁺; ∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.ToList; open import Prelude.FromList
open import Prelude.Ord
open import Prelude.Irrelevance hiding (_─_)
open import Prelude.Irrelevance.Dec
open import Prelude.Membership
open import Prelude.Bifunctor
open import Prelude.Setoid
open import Prelude.Null
open import Prelude.Apartness
open import Prelude.InferenceRules
open import Prelude.Measurable
open import Prelude.Indexable

open import Prelude.Ord.Product

-- open import Prelude.Lists
open import Prelude.Lists.Core
open import Prelude.Lists.WithK
open import Prelude.Lists.Dec
open import Prelude.Lists.MapMaybe
open import Prelude.Lists.SetEquality
open import Prelude.Lists.Concat
open import Prelude.Lists.Count
open import Prelude.Lists.Membership
open import Prelude.Lists.Empty
open import Prelude.Lists.Indexed hiding (_‼_)

module Prelude.Sets.AsSortedUniqueLists.Abstract where

private to = toList; from = fromList
open ≈-Reasoning

module _ {A : Type ℓ} ⦃ _ : DecEq A ⦄ ⦃ _ : Ord⁺⁺ A ⦄ where abstract
  Set' : Type ℓ
  Set' = Σ (List A) (Sorted Unary.∩ ·Unique)
  syntax Set' {A = A} = Set⟨ A ⟩

  ∅ˢ : Set'
  ∅ˢ = [] , [] , []

  instance
    ToList-Set : ToList Set' A
    ToList-Set .toList = proj₁

    FromList-Set : FromList A (const Set')
    FromList-Set .fromList xs
      = sort (nub xs)
      , sort-↗ (nub xs)
      , Unique⇒·Unique (Unique-sort⁺ $ Unique-nub {xs = xs})

  mkSet≡ : Injective≡ (toList ⦃ ToList-Set ⦄)
  mkSet≡ {_ , p} {_ , p′} refl rewrite ∀≡ p p′ = refl

  unmkSet≡ : Congruent≡ (toList ⦃ ToList-Set ⦄)
  unmkSet≡ refl = refl

  private variable
    x x′ : A
    xs ys : List A
    Xs Ys Zs s s′ : Set'
    R : Rel A ℓ′
    P : Pred A ℓ′

  instance
    DecEq-Sorted : DecEq (Sorted xs)
    DecEq-Sorted = Irrelevant⇒DecEq ∀≡

    DecEq-Unique : DecEq (·Unique xs)
    DecEq-Unique = Irrelevant⇒DecEq ∀≡

  -- ** NB: already covered by DecEq-Σ, but exposed for external use
  DecEq-Set : DecEq Set'
  DecEq-Set ._≟_ (xs , _) (ys , _) = Nullary.map′ mkSet≡ unmkSet≡ (xs ≟ ys)

  instance
    Setoid-Set : ISetoid Set'
    Setoid-Set = mkISetoid≡

    SetoidLaws-Set : SetoidLaws Set'
    SetoidLaws-Set = mkSetoidLaws≡

    Nullable-Set : Nullable Set' {ℓ}
    Nullable-Set .Null = _≡ ∅ˢ

    Measurable-Set : Measurable Set'
    Measurable-Set = record {∣_∣ = length ∘ toList}

    Ord-Set : Ord Set'
    Ord-Set = mkOrd≈ toList

    DecOrd-Set : DecOrd Set'
    DecOrd-Set = mkDecOrd≈ toList

    OrdLaws-Set : OrdLaws Set'
    OrdLaws-Set = mkOrdLaws≈ toList mkSet≡ unmkSet≡

    ·Ord-Set : ·Ord Set'
    ·Ord-Set = record {}

    Ord⁺⁺-Set : Ord⁺⁺ Set'
    Ord⁺⁺-Set = mkOrd⁺⁺

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

  _∈ˢ_ _∉ˢ_ : A → Set' → Type ℓ
  o ∈ˢ (os , _) = o ∈ os
  o ∉ˢ s = ·¬ (o ∈ˢ s)

  private
    _·∉_ : A → List A → Type ℓ
    x ·∉ xs = ·¬ (x ∈ xs)

    _·∉?_ : ∀ x xs → Dec (x ·∉ xs)
    _·∉?_ = ·¬? ∘₂ _∈?_

  ∈ˢ-irr : Irrelevant (x ∈ˢ Xs)
  ∈ˢ-irr {Xs = _ , _ , uniq} = ∈-irr (·Unique⇒Unique uniq)

  -- from↔to : ∀ xs → Unique xs → to (from xs) ≡ xs
  -- from↔to _ Uxs rewrite nub-from∘to Uxs = refl

  ∈-to∘from⁻ : x ∈ to (from {B = const Set'} xs) → x ∈ xs
  ∈-to∘from⁻ = ∈-nub⁻ ∘ ∈-sort⁻

  ∈-to⁻ : x ∈ to Xs → x ∈ˢ Xs
  ∈-to⁻ = id

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
  ⋃ f = foldr _∪_ ∅ˢ ∘ map f ∘ toList

  -- ** relational properties
  ∉∅ : ∀ (x : A) → ¬ (x ∈ˢ ∅ˢ)
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

  _⊆?ˢ_ : Decidable² _⊆ˢ_
  _⊆?ˢ_ = dec²

  -- ** algebraic properties

  _≈ˢ_ : Rel Set' ℓ
  _≈ˢ_ = _≡_
  module ≈ˢ-Reasoning = ≈-Reasoning {A = Set'}
  open Alg _≈ˢ_

  ≈⇒⊆ˢ : s ≈ s′ → s ⊆ˢ s′
  ≈⇒⊆ˢ refl = id

  ≈⇒⊆ˢ˘ : s ≈ s′ → s′ ⊆ˢ s
  ≈⇒⊆ˢ˘ refl = id

  ∅─-identityʳ : RightIdentity ∅ˢ _─_
  ∅─-identityʳ _ = mkSet≡ $ L.filter-all (_·∉? []) (L.All.map ¬⇒·¬ All∉[])

  ∅∪-identityˡ : LeftIdentity ∅ˢ _∪_
  ∅∪-identityˡ xs@(_ , sorted-xs , _)=
    begin ∅ˢ ∪ xs ≡⟨ mkSet≡ $ Sorted⇒sort-id $ Sorted-filter⁺ (_·∉? []) sorted-xs ⟩
          xs ─ ∅ˢ ≈⟨ ∅─-identityʳ xs ⟩
          xs ∎

  -- ∩-comm : Commutative _∩_
  -- ∩-comm s s′ = uncurry (∈-∩⁺ _ s′ s) ∘ Product.swap ∘ ∈-∩⁻ _ s s′
  --             , uncurry (∈-∩⁺ _ s s′) ∘ Product.swap ∘ ∈-∩⁻ _ s′ s

  ∪-∅ : (Xs ∪ Ys) ≈ ∅ˢ → (Xs ≈ ∅ˢ) × (Ys ≈ ∅ˢ)
  ∪-∅ {xs , _}{ys , _} eq
    with eqˡ , eqʳ ← Null-++ {xs = xs} $ Null-sort⁻ $ unmkSet≡ eq
    rewrite eqˡ
    = mkSet≡ refl
    , mkSet≡ (subst (_≡ []) (L.filter-all (_·∉? []) (L.All.map ¬⇒·¬ All∉[])) eqʳ)

  ∪-∅ˡ : (Xs ∪ Ys) ≈ ∅ˢ → Xs ≈ ∅ˢ
  ∪-∅ˡ {Xs}{Ys} = proj₁ ∘ ∪-∅ {Xs}{Ys}

  ∪-∅ʳ : (Xs ∪ Ys) ≈ ∅ˢ → Ys ≈ ∅ˢ
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
    Apart-Set : Set' //^⦅ ℓ ⦆ Set'
    Apart-Set ._♯_ s s′ = s ∩ s′ ≈ ∅ˢ

  _♯ˢ_ : Rel Set' ℓ
  _♯ˢ_ = _♯_

  _♯ˢ?_ : Decidable² _♯ˢ_
  _♯ˢ?_ = dec²

  -- ** alternative formulation of _♯_
  _♯′_ : Rel Set' ℓ
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

  Set'⁺ : Type ℓ
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

  Nullˢ : Pred Set' ℓ
  Nullˢ = Null

  Null?ˢ : Decidable¹ Nullˢ
  Null?ˢ = Null?

  Nullᵇˢ : Set' → Bool
  Nullᵇˢ = Nullᵇ

  -- private variable xs ys zs : Set⟨ A ⟩

  toList∘singleton : toList (singleton x) ≡ [ x ]
  toList∘singleton = refl

  fromList∘singleton : fromList [ x ] ≡ singleton x
  fromList∘singleton = refl

  ∈ˢ-toList⁻ : x ∈ˢ Xs → x ∈ toList Xs
  ∈ˢ-toList⁻ = id
  ∈ˢ-toList⁺ : x ∈ toList Xs → x ∈ˢ Xs
  ∈ˢ-toList⁺ = id

  postulate
    ∪-congˡ : Ys ≈ Zs → Xs ∪ Ys ≈ Xs ∪ Zs
    ∪-congʳ : Xs ≈ Ys → Xs ∪ Zs ≈ Ys ∪ Zs

module _ {A : Type ℓ} ⦃ _ : DecEq A ⦄ ⦃ _ : Ord⁺⁺ A ⦄ where abstract
  private variable
    x x′ : A; xs xs′ ys zs : Set⟨ A ⟩

  ∈ˢ-singleton : x ∈ˢ singleton x
  ∈ˢ-singleton = singleton∈ˢ .proj₂ refl

  infixr 5 _∷ˢ_
  _∷ˢ_ : A → Set⟨ A ⟩ → Set⟨ A ⟩
  x ∷ˢ xs = singleton x ∪ xs

  ∈ˢ-∷⁺ˡ hereˢ : x ∈ˢ x ∷ˢ xs
  ∈ˢ-∷⁺ˡ {xs = xs} = ∈-∪⁺ˡ _ (singleton _) xs ∈ˢ-singleton
  hereˢ  {xs = xs} = ∈ˢ-∷⁺ˡ {xs = xs}

  ∈ˢ-∷⁺ʳ thereˢ : x ∈ˢ xs → x ∈ˢ x′ ∷ˢ xs
  ∈ˢ-∷⁺ʳ {xs = xs} = ∈-∪⁺ʳ _ (singleton _) xs
  thereˢ {xs = xs} = ∈ˢ-∷⁺ʳ {xs = xs}

  ∈ˢ-∷⁻ : x ∈ˢ x′ ∷ˢ xs → (x ≡ x′) ⊎ (x ∈ˢ xs)
  ∈ˢ-∷⁻ {xs = xs} x∈ with ∈-∪⁻ _ (singleton _) xs x∈
  ... | inj₁ (here refl) = inj₁ refl
  ... | inj₂ x∈          = inj₂ x∈

  postulate
    from-∷ˢ : ∀ {xs} → from (x ∷ xs) ≈ (x ∷ˢ from xs)
    from-++ˢ : ∀ {xs ys : List A} → from (xs ++ ys) ≡ (from xs ∪ from ys)
    from-≈ : ∀ {xs ys : List A} →
      xs ∼[set] ys
      ──────────────────
      from xs ≈ from ys
    from-≈˘ : ∀ {xs ys : List A} →
      from xs ≈ from ys
      ──────────────────
      xs ∼[set] ys
    to-∷ˢ : (to $ x ∷ˢ xs) ∼[set] (x ∷ to xs)
    to-++ˢ : (to $ xs ∪ ys) ∼[set] (to xs ++ to ys)

    to-≈ :
      xs ≈ ys
      ──────────────────
      to xs ∼[set] to ys

  headˢ : Set⟨ A ⟩ → Maybe A
  headˢ = L.head ∘ to

  private variable P : A → Type ℓ

  filterˢ : Decidable¹ P → Op₁ Set⟨ A ⟩
  filterˢ P? = from ∘ filter P? ∘ to

  module _ {B : Type ℓ} ⦃ _ : DecEq B ⦄ ⦃ _ : Ord⁺⁺ B ⦄ where

    mapˢ : (A → B) → (Set⟨ A ⟩ → Set⟨ B ⟩)
    mapˢ f = from ∘ map f ∘ to

    mapWith∈ˢ : (xs : Set⟨ A ⟩) → (∀ {x} → x ∈ˢ xs → B) → Set⟨ B ⟩
    mapWith∈ˢ xs f = from (L.Mem.mapWith∈ (to xs) (f ∘ ∈-to⁻))

    module _ (f : A → B) where

--       module _ {P : Pred B ℓ} {xs} where
--         Anyˢ-map⁺ : Anyˢ (P ∘ f) xs → Anyˢ P (mapˢ f xs)
--         Anyˢ-map⁺ = Anyˢ-fromList⁺ ∘ L.Any.map⁺

--         Anyˢ-map⁻ :  Anyˢ P (mapˢ f xs) → Anyˢ (P ∘ f) xs
--         Anyˢ-map⁻ = L.Any.map⁻ ∘ Anyˢ-fromList⁻

--         Anyˢ-map : Anyˢ (P ∘ f) xs ↔ Anyˢ P (mapˢ f xs)
--         Anyˢ-map = Anyˢ-map⁺ , Anyˢ-map⁻

--       ∈ˢ-map⁺ : x ∈ˢ xs → f x ∈ˢ mapˢ f xs
--       ∈ˢ-map⁺ = ∈ˢ-fromList⁺ ∘ L.Mem.∈-map⁺ f

--       ∈ˢ-map⁻ : ∀ {y} → y ∈ˢ mapˢ f xs → ∃ λ x → x ∈ˢ xs × y ≡ f x
--       ∈ˢ-map⁻ = L.Mem.∈-map⁻ f ∘ ∈ˢ-fromList⁻

      postulate mapˢ-∪ : mapˢ f (xs ∪ ys) ≈ (mapˢ f xs ∪ mapˢ f ys)

    mapMaybeˢ : (A → Maybe B) → (Set⟨ A ⟩ → Set⟨ B ⟩)
    mapMaybeˢ f = from ∘ mapMaybe f ∘ to

--     module _ (f : A → Maybe B) where

--       module _ {y} where
--         ∈ˢ-mapMaybe⁺ : x ∈ˢ xs → f x ≡ just y → y ∈ˢ mapMaybeˢ f xs
--         ∈ˢ-mapMaybe⁺ = ∈ˢ-fromList⁺ ∘₂ ∈-mapMaybe⁺ f

--         ∈ˢ-mapMaybe⁻ : y ∈ˢ mapMaybeˢ f xs → ∃ λ x → (x ∈ˢ xs) × (f x ≡ just y)
--         ∈ˢ-mapMaybe⁻ = ∈-mapMaybe⁻ f ∘ ∈ˢ-fromList⁻

--       postulate
--         mapMaybeˢ-∪ : mapMaybeˢ f (xs ∪ ys) ≈ (mapMaybeˢ f xs ∪ mapMaybeˢ f ys)

-- ** align/zip/partition
module _ {A B C : Type}
  ⦃ _ : DecEq A ⦄ ⦃ _ : DecEq B ⦄ ⦃ _ : DecEq C ⦄
  ⦃ _ : Ord⁺⁺ A ⦄ ⦃ _ : Ord⁺⁺ B ⦄ ⦃ _ : Ord⁺⁺ C ⦄
  where abstract
  alignWithˢ : (These A B → C) → Set⟨ A ⟩ → Set⟨ B ⟩ → Set⟨ C ⟩
  alignWithˢ f xs ys = from $ L.alignWith f (to xs) (to ys)

  zipWithˢ : (A → B → C) → Set⟨ A ⟩ → Set⟨ B ⟩ → Set⟨ C ⟩
  zipWithˢ f xs ys = from $ L.zipWith f (to xs) (to ys)

  unalignWithˢ : (A → These B C) → Set⟨ A ⟩ → Set⟨ B ⟩ × Set⟨ C ⟩
  unalignWithˢ f = (λ (xs , ys) → from xs , from ys) ∘ L.unalignWith f ∘ to

  unzipWithˢ : (A → B × C) → Set⟨ A ⟩ → Set⟨ B ⟩ × Set⟨ C ⟩
  unzipWithˢ f = (λ (xs , ys) → from xs , from ys) ∘ L.unzipWith f ∘ to

  partitionSumsWithˢ : (A → B ⊎ C) → Set⟨ A ⟩ → Set⟨ B ⟩ × Set⟨ C ⟩
  partitionSumsWithˢ f = unalignWithˢ (∣These∣.fromSum ∘′ f)

module _ {A B : Type}
  ⦃ _ : DecEq A ⦄ ⦃ _ : DecEq B ⦄
  ⦃ _ : Ord⁺⁺ A ⦄ ⦃ _ : Ord⁺⁺ B ⦄
  where abstract
  alignˢ : Set⟨ A ⟩ → Set⟨ B ⟩ → Set⟨ These A B ⟩
  alignˢ = alignWithˢ id

  zipˢ : Set⟨ A ⟩ → Set⟨ B ⟩ → Set⟨ A × B ⟩
  zipˢ = zipWithˢ (_,_)

  unalignˢ : Set⟨ These A B ⟩ → Set⟨ A ⟩ × Set⟨ B ⟩
  unalignˢ = unalignWithˢ id

  unzipˢ : Set⟨ A × B ⟩ → Set⟨ A ⟩ × Set⟨ B ⟩
  unzipˢ = unzipWithˢ id

  -- partitionSumsˢ : Set⟨ A ⊎ B ⟩ → Set⟨ A ⟩ × Set⟨ B ⟩
  -- partitionSumsˢ = partitionSumsWithˢ id

  partitionSumsˢ : Set⟨ A ⊎ B ⟩ → Set⟨ A ⟩ × Set⟨ B ⟩
  partitionSumsˢ = (λ (as , bs) → from as , from bs) ∘ partitionSums ∘ to

  leftsˢ : Set⟨ A ⊎ B ⟩ → Set⟨ A ⟩
  leftsˢ = proj₁ ∘ partitionSumsˢ

  rightsˢ : Set⟨ A ⊎ B ⟩ → Set⟨ B ⟩
  rightsˢ = proj₂ ∘ partitionSumsˢ

  leftsˢ∘inj₁ : ∀ {a : A} {abs : Set⟨ A ⊎ B ⟩}
    →  leftsˢ (inj₁ a ∷ˢ abs)
    ≈ (a ∷ˢ leftsˢ abs)
  leftsˢ∘inj₁ {a = a}{abs} =
    begin
      leftsˢ (inj₁ a ∷ˢ abs)
    ≡⟨⟩
      from (lefts $ to $ inj₁ a ∷ˢ abs)
    ≈⟨ from-≈ {xs = lefts $ to $ inj₁ a ∷ˢ abs}
              {ys = lefts $ inj₁ a ∷ to abs}
     $ lefts-seteq
     $ to-∷ˢ {x = inj₁ a} {xs = abs}
     ⟩
      from (lefts $ inj₁ a ∷ to abs)
    ≡⟨⟩
      from (a ∷ lefts (to abs))
    ≈⟨ from-∷ˢ {xs = lefts $ to abs} ⟩
      (a ∷ˢ from (lefts $ to abs))
    ≡⟨⟩
      (a ∷ˢ leftsˢ abs)
    ∎

  leftsˢ∘inj₂ : ∀ {b : B} {abs : Set⟨ A ⊎ B ⟩}
    →  leftsˢ (inj₂ b ∷ˢ abs)
    ≈ leftsˢ abs
  leftsˢ∘inj₂ {b = b}{abs} =
    begin
      leftsˢ (inj₂ b ∷ˢ abs)
    ≡⟨⟩
      from (lefts $ to $ inj₂ b ∷ˢ abs)
    ≈⟨ from-≈ {xs = lefts $ to $ inj₂ b ∷ˢ abs}
               {ys = lefts $ inj₂ b ∷ to abs}
     $ lefts-seteq
     $ to-∷ˢ {x = inj₂ b} {xs = abs}
     ⟩
      from (lefts $ inj₂ b ∷ to abs)
    ≡⟨⟩
      from (lefts $ to abs)
    ≡⟨⟩
      leftsˢ abs
    ∎

  rightsˢ∘inj₁ : ∀ {a : A} {abs : Set⟨ A ⊎ B ⟩}
    →  rightsˢ (inj₁ a ∷ˢ abs)
    ≈ rightsˢ abs
  rightsˢ∘inj₁ {a = a}{abs} =
    begin
      rightsˢ (inj₁ a ∷ˢ abs)
    ≡⟨⟩
      from (rights $ to $ inj₁ a ∷ˢ abs)
    ≈⟨ from-≈ {xs = rights $ to $ inj₁ a ∷ˢ abs}
               {ys = rights $ inj₁ a ∷ to abs}
     $ rights-seteq
     $ to-∷ˢ {x = inj₁ a} {xs = abs}
     ⟩
      from (rights $ inj₁ a ∷ to abs)
    ≡⟨⟩
      from (rights $ to abs)
    ≡⟨⟩
      rightsˢ abs
    ∎

  rightsˢ∘inj₂ : ∀ {b : B} {abs : Set⟨ A ⊎ B ⟩}
    →  rightsˢ (inj₂ b ∷ˢ abs)
    ≈ (b ∷ˢ rightsˢ abs)
  rightsˢ∘inj₂ {b = b}{abs} =
    begin
      rightsˢ (inj₂ b ∷ˢ abs)
    ≡⟨⟩
      from (rights $ to $ inj₂ b ∷ˢ abs)
    ≈⟨ from-≈ {xs = rights $ to $ inj₂ b ∷ˢ abs}
               {ys = rights $ inj₂ b ∷ to abs}
     $ rights-seteq
     $ to-∷ˢ {x = inj₂ b} {xs = abs}
     ⟩
      from (rights $ inj₂ b ∷ to abs)
    ≡⟨⟩
      from (b ∷ rights (to abs))
    ≈⟨ from-∷ˢ {xs = rights $ to abs} ⟩
      (b ∷ˢ from (rights $ to abs))
    ≡⟨⟩
      (b ∷ˢ rightsˢ abs)
    ∎

module _ {A B C : Type}
  ⦃ _ : DecEq A ⦄ ⦃ _ : DecEq B ⦄ ⦃ _ : DecEq C ⦄
  ⦃ _ : Ord⁺⁺ A ⦄ ⦃ _ : Ord⁺⁺ B ⦄ ⦃ _ : Ord⁺⁺ C ⦄
  where abstract
  unzip₃ˢ : Set⟨ A × B × C ⟩ → Set⟨ A ⟩ × Set⟨ B ⟩ × Set⟨ C ⟩
  unzip₃ˢ = map₂ unzipˢ ∘ unzipˢ

module _ {A B : Type ℓ}
  ⦃ _ : DecEq A ⦄ ⦃ _ : Ord⁺⁺ A ⦄
  ⦃ _ : DecEq B ⦄ ⦃ _ : Ord⁺⁺ B ⦄
  where abstract

  filterˢ₁ : Set⟨ A ⊎ B ⟩ → Set⟨ A ⟩
  filterˢ₁ = mapMaybeˢ isInj₁

  filterˢ₂ : Set⟨ A ⊎ B ⟩ → Set⟨ B ⟩
  filterˢ₂ = mapMaybeˢ isInj₂

-- ** sum
sumˢ : Set⟨ ℕ ⟩ → ℕ
sumˢ = sum ∘ to

module _ {A : Type ℓ} ⦃ _ : DecEq A ⦄ ⦃ _ : Ord⁺⁺ A ⦄ where abstract

  private variable
    x x′ : A; xs xs′ ys zs : Set⟨ A ⟩
    B : Type ℓ; P : Pred A ℓ

  -- ** set mappings
  infix 0 mk↦_
  data _↦′_ : Set⟨ A ⟩ → Pred A ℓ → Type ℓ where
    mk↦_ : (∀ {x} → x ∈ˢ xs → P x) → xs ↦′ P

  unmk↦_ : xs ↦′ P → (∀ {x} → x ∈ˢ xs → P x)
  unmk↦ (mk↦ p) = p

  map↦ : Set⟨ A ⟩ → Pred A ℓ → Type ℓ
  map↦ = _↦′_
  syntax map↦ xs (λ x → f) = ∀[ x ∈ xs ] f

  _↦_ : Set⟨ A ⟩ → Type ℓ → Type ℓ
  xs ↦ B = xs ↦′ const B

  dom : xs ↦′ P → Set⟨ A ⟩
  dom {xs = xs} _ = xs

  codom : ⦃ _ : DecEq B ⦄ ⦃ _ : Ord⁺⁺ B ⦄ → xs ↦ B → Set⟨ B ⟩
  codom {xs = xs} (mk↦ f) = mapWith∈ˢ xs f

  weaken-↦ : xs ↦′ P → ys ⊆ˢ xs → ys ↦′ P
  weaken-↦ (mk↦ f) ys⊆xs = mk↦ f ∘ ys⊆xs

  cons-↦ : (x : A) → P x → xs ↦′ P → (x ∷ˢ xs) ↦′ P
  cons-↦ {xs = xs} x y (mk↦ f) = mk↦ ∈ˢ-∷⁻ {x′ = x}{xs} >≡> λ where
      (inj₁ refl) → y
      (inj₂ x∈)   → f x∈

  uncons-↦ : (x ∷ˢ xs) ↦′ P → xs ↦′ P
  uncons-↦ {x = x}{xs} (mk↦ f) = mk↦ f ∘ thereˢ {xs = xs}{x}

  -- _↭ˢ_ : Rel (Set⟨ A ⟩) ℓ
  -- _↭ˢ_ = _↭_ on toList

  module _ {xs ys} where abstract
    -- permute-↦ : xs ↭ˢ ys → xs ↦′ P → ys ↦′ P
    -- permute-↦ xs↭ys (mk↦ xs↦) = mk↦
    --   xs↦ ∘ ∈ˢ-toList⁺ {xs = xs} ∘ L.Perm.∈-resp-↭ (↭-sym xs↭ys) ∘ ∈ˢ-toList⁻ {xs = ys}

    _∪/↦_ : xs ↦′ P → ys ↦′ P → (xs ∪ ys) ↦′ P
    (mk↦ xs↦) ∪/↦ (mk↦ ys↦) = mk↦ ∈-∪⁻ _ xs ys >≡> λ where
      (inj₁ x∈) → xs↦ x∈
      (inj₂ y∈) → ys↦ y∈

    destruct-∪/↦ : (xs ∪ ys) ↦′ P → (xs ↦′ P) × (ys ↦′ P)
    destruct-∪/↦ (mk↦ xys↦) = (mk↦ xys↦ ∘ ∈-∪⁺ˡ _ xs ys)
                            , (mk↦ xys↦ ∘ ∈-∪⁺ʳ _ xs ys)

    destruct≡-∪/↦ : zs ≡ xs ∪ ys → zs ↦′ P → (xs ↦′ P) × (ys ↦′ P)
    destruct≡-∪/↦ refl = destruct-∪/↦

  -- extend-↦ : zs ↭ˢ (xs ∪ ys) → xs ↦′ P → ys ↦′ P → zs ↦′ P
  -- extend-↦ zs↭ xs↦ ys↦ = permute-↦ (↭-sym zs↭) (xs↦ ∪/↦ ys↦)

  cong-↦ : xs ↦′ P → xs′ ≈ xs → xs′ ↦′ P
  cong-↦ f refl = f

module _ {A : Type} ⦃ _ : DecEq A ⦄ ⦃ _ : Ord⁺⁺ A ⦄ where abstract
  private variable
    x x′ : A; xs xs′ ys zs : Set⟨ A ⟩

  instance
    Indexable-Set : Indexable Set⟨ A ⟩ A {0ℓ}
    Indexable-Set = λ where
      .Ix s → Fin ∣ s ∣
      ._‼_ s i → toList s ‼ i

  Indexˢ : Pred₀ (Set⟨ A ⟩)
  Indexˢ = Ix

  module _ {xs : List A} where postulate
    ‼-sort⁺ : Ix xs → Ix (sort xs)
    ‼-sort⁻ : Ix (sort xs) → Ix xs

  module _ {xs : List A} where abstract
    ‼-from⁺ : Ix xs → Indexˢ (fromList xs)
    ‼-from⁺ = ‼-sort⁺ {xs = nub xs} ∘ ‼-nub⁺ {xs = xs}

    ‼-from⁻ : Indexˢ (fromList xs) → Ix xs
    ‼-from⁻ = ‼-nub⁻ {xs = xs} ∘ ‼-sort⁻ {xs = nub xs}

  ‼-to⁺ : Ix xs → Ix (toList xs)
  ‼-to⁺ = id

  ‼-to⁻ : Ix (toList xs) → Ix xs
  ‼-to⁻ = id

  mapWithIxˢ : {B : Type ℓ′} ⦃ _ : DecEq B ⦄
             → (xs : Set⟨ A ⟩) → (A → Ix xs → B)
             → List B
  mapWithIxˢ xs f = map (λ (i , x) → f x i) (enumerate $ to xs)

module _ {A : Type} ⦃ _ : DecEq A ⦄ ⦃ _ : Ord⁺⁺ A ⦄
         {B : Type} ⦃ _ : DecEq B ⦄ ⦃ _ : Ord⁺⁺ B ⦄ where
  module _ (f : A → B) {xs : Set⟨ A ⟩} where abstract
    ‼-mapˢ : Ix xs → Ix (mapˢ f xs)
    ‼-mapˢ = ‼-from⁺ {xs = map f (xs ∙toList)}
           ∘ ‼-map⁺ f {xs ∙toList}

  module _ {xs : Set⟨ A ⟩} (f : ∀ {x} → x ∈ˢ xs → B) where abstract

    ‼-mapWith∈ˢ : Ix xs → Ix (mapWith∈ˢ xs f)
    ‼-mapWith∈ˢ = ‼-from⁺ {xs = L.Mem.mapWith∈ (xs ∙toList) _}
                ∘ ‼-mapWith∈ {xs = xs ∙toList}

  module _ xs (f : A → Ix xs → B) where abstract

    ‼-mapWithIx : Ix xs → Ix (mapWithIx xs f)
    ‼-mapWithIx i = ‼-mapWithIx⁺ {xs = xs ∙toList} f i

instance DecEq-Set-EXPOSE = DecEq-Set
