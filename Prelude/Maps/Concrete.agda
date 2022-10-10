open import Prelude.Init
open SetAsType
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.DecLists
open import Prelude.Membership
open import Prelude.ToList
open import Prelude.FromList
open import Prelude.Functor
open import Prelude.Semigroup
open import Prelude.Monoid
open import Prelude.Ord
open import Prelude.Measurable
open import Prelude.Apartness renaming (_♯_ to _♯₀_)
open import Prelude.Setoid    renaming (_≈_ to _≈₀_)

module Prelude.Maps.Concrete {K V : Type} ⦃ _ : DecEq K ⦄ ⦃ _ : DecEq V ⦄ where

import Prelude.Sets.Concrete as S

record Map : Type where
  constructor _⊣_
  field
    kvs   : S.Set⟨ K × V ⟩                    -- NB: redundant proof `kvs .uniq`
    .uniq : Unique $ proj₁ <$> toList kvs
open Map
syntax Map {K = K} {V = V} = Map⟨ K ↦ V ⟩

instance
  DecEq-Map : DecEq Map
  DecEq-Map ._≟_ m m′ with m .kvs ≟ m′ .kvs
  ... | yes refl = yes refl
  ... | no  m≢m′ = no  λ where refl → m≢m′ refl

∅ : Map
∅ = S.∅ ⊣ auto

singleton : K × V → Map
singleton (k , v) = S.singleton (k , v) ⊣ auto

module _ {a b} {A : Type a} {B : Type b} ⦃ _ : DecEq A ⦄ ⦃ _ : DecEq B ⦄ (f : A → B) where

  nub∘nubBy≗nubBy : ∀ (xs : List A) → nub (nubBy f xs) ≡ nubBy f xs
  nub∘nubBy≗nubBy = nub-from∘to ∘ Unique-nubBy f

  Unique-map∘nub∘nubBy : ∀ (xs : List A) → Unique (map f $ nub $ nubBy f xs)
  Unique-map∘nub∘nubBy xs rewrite nub∘nubBy≗nubBy xs = Unique-map∘nubBy f xs

-- NB: right-biased union
infixr 5 _∪_
_∪_ : Op₂ Map
(kvs ⊣ _) ∪ (kvs′ ⊣ _)
  = (fromList $ nubBy proj₁ (kvs ∙toList ++ kvs′ ∙toList))
  ⊣ Unique-map∘nub∘nubBy proj₁ (kvs ∙toList ++ kvs′ ∙toList)

infix 4 _∈ᵈ_ _∉ᵈ_ _∈ᵈ?_
_∈ᵈ_ : K → Map → Type
k ∈ᵈ m = k ∈ (proj₁ <$> m .kvs ∙toList)

_∉ᵈ_ : K → Map → Type
k ∉ᵈ m = ¬ (k ∈ᵈ m)

_∈ᵈ?_ : Decidable² _∈ᵈ_
k ∈ᵈ? m = dec

instance
  Apart-Map : Map // Map
  Apart-Map ._♯₀_ m m′ = ∀ k → ¬ ((k ∈ᵈ m) × (k ∈ᵈ m′))

private infix 4 _♯_; _♯_ = Rel₀ Map ∋ _♯₀_

_⁉_ : Map → K → Maybe V
m ⁉ k with k ∈ᵈ? m
... | no _   = nothing
... | yes k∈ = just (L.Mem.∈-map⁻ proj₁ k∈ .proj₁ .proj₂)

_[_↦_] : Map → K → V → Type
m [ k ↦ v ] = (k , v) S.∈ˢ m .kvs

_[_↦?_] : Decidable³ _[_↦_]
m [ k ↦? v ] = dec

insert : K × V → Op₁ Map
insert (k , v) m = m ∪ singleton (k , v)

insertWith : Op₂ V → K × V → Op₁ Map
insertWith _⊗_ (k , v) m with m ⁉ k
... | nothing = insert (k , v) m
... | just v′ = insert (k , v ⊗ v′) m

unionWith : Op₂ V → Op₂ Map
unionWith _⊗_ m m′ = foldr (insertWith _⊗_) m (m′ .kvs ∙toList)

instance
  Semigroup-Map : ⦃ Semigroup V ⦄ → Semigroup Map
  Semigroup-Map ._◇_ m m′ = unionWith _◇_ m m′

module _ {A B : Type} (f : A → B) {P : Pred₀ A} (P? : Decidable¹ P) where
  All-map∘filter : ∀ (Q : Pred₀ B) (xs : List A) →
    All Q (map f xs) → All Q (map f $ filter P? xs)
  All-map∘filter Q []       _          = []
  All-map∘filter Q (x ∷ xs) (qx ∷ qxs)
    with IH ← All-map∘filter Q xs qxs
    with P? x
  ... | yes _ = qx ∷ IH
  ... | no  _ = IH

  Unique-map∘filter : ∀ (xs : List A) →
    Unique (map f xs) → Unique (map f $ filter P? xs)
  Unique-map∘filter []       _        = []
  Unique-map∘filter (x ∷ xs) (x∉ ∷ p)
    with IH ← Unique-map∘filter xs p
    with P? x
  ... | yes _ = All-map∘filter (f x ≢_) _ x∉ ∷ IH
  ... | no  _ = IH

filterKV : {P : Pred₀ (K × V)} → Decidable¹ P → Op₁ Map
filterKV P? m@(_ ⊣ uniq-kvs) = S.filter′ P? (m .kvs) ⊣ Unique-map∘filter proj₁ P? _ uniq-kvs

filterK : {P : Pred₀ K} → Decidable¹ P → Op₁ Map
filterK = filterKV ∘ (_∘ proj₁)

filterV : {P : Pred₀ V} → Decidable¹ P → Op₁ Map
filterV = filterKV ∘ (_∘ proj₂)

postulate
  -- introduction/elimination of union
  ∈ᵈ-∪⁻ : ∀ k s₁ s₂ → k ∈ᵈ (s₁ ∪ s₂) → (k ∈ᵈ s₁) ⊎ (k ∈ᵈ s₂)
  ∈ᵈ-∪⁺ : ∀ k s₁ s₂ → (k ∈ᵈ s₁) ⊎ (k ∈ᵈ s₂) → k ∈ᵈ (s₁ ∪ s₂)
  ∪-chooseₗ : ∀ {s₁ s₂} → s₁ ♯ s₂ → (∀ {k} → k ∉ᵈ s₂ → (s₁ ∪ s₂) ⁉ k ≡ s₁ ⁉ k)
  ∪-chooseᵣ : ∀ {s₁ s₂} → s₁ ♯ s₂ → (∀ {k} → k ∈ᵈ s₂ → (s₁ ∪ s₂) ⁉ k ≡ s₂ ⁉ k)

∈ᵈ-∪⁺ˡ : ∀ k s₁ s₂ → k ∈ᵈ s₁ → k ∈ᵈ (s₁ ∪ s₂)
∈ᵈ-∪⁺ˡ k s₁ s₂ = ∈ᵈ-∪⁺ k s₁ s₂ ∘ inj₁

∈ᵈ-∪⁺ʳ : ∀ k s₁ s₂ → k ∈ᵈ s₂ → k ∈ᵈ (s₁ ∪ s₂)
∈ᵈ-∪⁺ʳ k s₁ s₂ = ∈ᵈ-∪⁺ k s₁ s₂ ∘ inj₂

module _
  ⦃ _ : Ord V ⦄
  ⦃ _ : _≤_ {A = V} ⁇² ⦄
  ⦃ _ : _<_ {A = V} ⁇² ⦄
  ⦃ _ : Monoid V ⦄
  where

  normalize : Op₁ Map
  normalize = filterV (_>? ε)

  _≤ᵐ_ : Rel₀ Map
  m ≤ᵐ m′ =
    S.Allˢ (λ where (k , v) → v ≤ fromMaybe ε (m′ ⁉ k))
           (m .kvs)

  _≤?ᵐ_ : Decidable² _≤ᵐ_
  m ≤?ᵐ m′ = dec

  instance
    Setoid-Map : ISetoid Map
    Setoid-Map = λ where
      .relℓ → _
      ._≈₀_ m m′ → (m ≤ᵐ m′) × (m′ ≤ᵐ m)

  private infix 4 _≈_; _≈_ = Rel₀ Map ∋ _≈₀_

  ⟨_⊎_⟩≡_ : Map → Map → Map → Type
  ⟨ m ⊎ m′ ⟩≡ m″ = (m ♯ m′) × ((m ∪ m′) ≈ m″)

  postulate
    ⁉⇒∈ᵈ : ∀ {s k} → Is-just (s ⁉ k) → k ∈ᵈ s
    ∈ᵈ⇒⁉ : ∀ {s k} → k ∈ᵈ s → Is-just (s ⁉ k)

    -- _∪_ is left-biased
    ↦-∪⁺ˡ : ∀ {s₁ s₂ k v} → s₁ [ k ↦ v ] → (s₁ ∪ s₂) [ k ↦ v ]
    ↦-∪⁺ʳ : ∀ {s₁ s₂ k} → k ∉ᵈ s₁ → s₂ ⁉ k ≡ (s₁ ∪ s₂) ⁉ k

    -- commutativity
    ♯-comm : Symmetric _♯_
    ∪-comm : ∀ {s₁}{s₂} → s₁ ♯ s₂ → (s₁ ∪ s₂) ≈ (s₂ ∪ s₁)

    -- congruences
    ♯-cong : ∀ {s₁ s₂ s₃} → s₁ ≈ s₂ → s₁ ♯ s₃ → s₂ ♯ s₃
    ∪-cong : ∀ {s₁ s₂ s₃} → s₁ ≈ s₂ → (s₁ ∪ s₃) ≈ (s₂ ∪ s₃)
    ∈ᵈ-cong : ∀ {k s₁ s₂} → s₁ ≈ s₂ → k ∈ᵈ s₁ → k ∈ᵈ s₂

    ♯-∪⁻ʳ : ∀ {s₁}{s₂}{s₃} → s₁ ♯ (s₂ ∪ s₃) → (s₁ ♯ s₂) × (s₁ ♯ s₃)
    ♯-∪⁻ˡ : ∀ {s₁}{s₂}{s₃} → (s₁ ∪ s₂) ♯ s₃ → (s₁ ♯ s₃) × (s₂ ♯ s₃)
    ♯-∪⁺ˡ : ∀ {s₁}{s₂}{s₃} → (s₁ ♯ s₃) × (s₂ ♯ s₃) → (s₁ ∪ s₂) ♯ s₃
    ♯-∪⁺ʳ : ∀ {s₁}{s₂}{s₃} → (s₁ ♯ s₂) × (s₁ ♯ s₃) → s₁ ♯ (s₂ ∪ s₃)

    -- associativity
    ∪-assocʳ : ∀ {s₁ s₂ s₃} → s₁ ∪ (s₂ ∪ s₃) ≈ (s₁ ∪ s₂) ∪ s₃
    ∪≡-assocʳ : ∀ {s₁}{s₂}{s₃}{s} → s₂ ♯ s₃ → ⟨ s₁ ⊎ (s₂ ∪ s₃) ⟩≡ s → ⟨ (s₁ ∪ s₂) ⊎ s₃ ⟩≡ s


  _≈?ᵐ_ : Decidable² (Rel₀ Map ∋ _≈_)
  m ≈?ᵐ m′ = dec

  module _ (_∸_ : Op₂ V) where

    _-ᵐ_ : Map → Map → Maybe Map
    m -ᵐ m′ = let m″ = normalize m′ in
      if ⌊ m″ ≤?ᵐ m ⌋ then
        just $ normalize $ unionWith (flip _∸_) m m′
      else
        nothing

-- ** list conversion
instance
  ToList-Map : ToList Map (K × V)
  ToList-Map .toList = toList ∘ kvs

  FromList-Map : FromList (K × V) Map
  FromList-Map .fromList xs = fromList (nubBy proj₁ xs)
                            ⊣ Unique-map∘nub∘nubBy proj₁ xs

private
  open import Prelude.General
  open import Prelude.Nary

  postulate
    k k′ : K
    v v′ v″ : V
    k≢k′ : k ≢ k′

  _ = singleton (k , v) ≡ fromList [ k , v ]
    ∋ refl

  k↦v   = singleton (k  , v)
  k↦v′  = singleton (k  , v′)
  k↦v″  = singleton (k  , v″)
  k′↦v′ = singleton (k′ , v′)

  -- _ : List (K × V)
  -- _ = ⟦ (k , v) , (k′ , v′) ⟧

  _ : (k↦v ∪ k′↦v′) ≡ fromList ((k , v) ∷ (k′ , v′) ∷ [])
  _ = refl

  -- ex : (k↦v ∪ k↦v′) ≡ singleton (k , v)
  -- ex = {!refl!}
  -- rewrite ≟-refl k | toWitnessFalse {Q = k ≟ k′} k≢k′

  m₁ = Map ∋ singleton (k , v) ∪ singleton (k , v)

instance
  Measurable-Map : Measurable Map
  Measurable-Map = record {∣_∣ = ∣_∣ ∘ kvs}

Map⁺ = ∃ λ (m : Map) → ∣ m ∣ > 0
syntax Map⁺ {K = K} {V = V} = Map⁺⟨ K ↦ V ⟩

mkMap⁺ : (m : Map) ⦃ _ : True (∣ m ∣ >? 0) ⦄ → Map⁺
mkMap⁺ m ⦃ pr ⦄ = m , toWitness pr

fromList⁺ : (xs : List (K × V)) ⦃ _ : True (length (nub $ nubBy proj₁ xs) >? 0) ⦄ → Map⁺
fromList⁺ = mkMap⁺ ∘ fromList
