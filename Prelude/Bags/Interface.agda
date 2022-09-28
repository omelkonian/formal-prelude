module Prelude.Bags.Interface where

open import Prelude.Init
open import Prelude.General
open import Prelude.Membership
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Semigroup
open import Prelude.Applicative
open import Prelude.Measurable
open import Prelude.Apartness

import Relation.Binary.Reasoning.Setoid as BinSetoid

record Bagᴵ (A : Set) (σ : Level) : Set (lsuc σ) where
  constructor mkSetᴵ
  field
    Bag' : Set σ
    ∅ : Bag'
    singleton : A → Bag'
    _∈ˢ_ : A → Bag' → Set
    _─_ _∪_ _∩_ : Op₂ Bag'

  syntax Bag' {A = A} = Bag⟨ A ⟩
  infixr 8 _─_
  infixr 7 _∩_
  infixr 6 _∪_
  infix  4 _∈ˢ_ _∉ˢ_ _⊆ˢ_ _⊇ˢ_ _⊈ˢ_ _⊉ˢ_

  _∉ˢ_ : A → Bag' → Set _
  x ∉ˢ s = ¬ (x ∈ˢ s)

  -- ** relational properties
  field
    singleton∈ˢ : ∀ {x x′} → x′ ∈ˢ singleton x ↔ x′ ≡ x
    -- congruences
    -- ♯-cong : ∀ {s₁}{s₂}{s₃} → s₁ ≈ˢ s₂ → s₁ ♯ s₃ → s₂ ♯ s₃
    -- ∪-cong : ∀ {s₁}{s₂}{s₃} → s₁ ≈ˢ s₂ → (s₁ ∪ s₃) ≈ˢ (s₂ ∪ s₃)

    ∈-∪⁻ : ∀ x xs ys → x ∈ˢ (xs ∪ ys) → x ∈ˢ xs ⊎ x ∈ˢ ys
    ∈-∪⁺ˡ : ∀ x xs ys → x ∈ˢ xs → x ∈ˢ (xs ∪ ys)
    ∈-∪⁺ʳ : ∀ x xs ys → x ∈ˢ ys → x ∈ˢ (xs ∪ ys)
    ∈-∩⁺ : ∀ x xs ys → x ∈ˢ xs → x ∈ˢ ys → x ∈ˢ (xs ∩ ys)
    ∈-∩⁻ : ∀ x xs ys → x ∈ˢ (xs ∩ ys) → (x ∈ˢ xs) × (x ∈ˢ ys)
    ∈-─⁻ : ∀ x xs ys → x ∈ˢ (xs ─ ys) → x ∈ˢ xs
    ∈-─⁺ : ∀ x xs ys → x ∈ˢ xs → x ∉ˢ ys → x ∈ˢ (xs ─ ys)
    ∉∅ : ∀ x → x ∉ˢ ∅

  _♯ˢ_ : Rel₀ Bag'
  s ♯ˢ s′ = ∀ {k} → ¬ (k ∈ˢ s × k ∈ˢ s′)

  instance
    Apart-Bag' : Bag' // Bag'
    Apart-Bag' ._♯_ = _♯ˢ_

  -- ♯-comm : Symmetric _♯_
  ♯-comm : ∀ (x y : Bag') → x ♯ y → y ♯ x
  ♯-comm x y x♯y = x♯y ∘ Product.swap

  ∈-∩⇒¬♯ : ∀ x xs ys → x ∈ˢ (xs ∩ ys) → ¬ (xs ♯ ys)
  ∈-∩⇒¬♯ x xs ys x∈ xs♯ys = xs♯ys $ ∈-∩⁻ _ xs ys x∈

  ♯-skipˡ : ∀ xs ys (zs : Bag') → (xs ∪ ys) ♯ zs → ys ♯ zs
  ♯-skipˡ xs ys _ p (x∈ys , x∈zs) = p (∈-∪⁺ʳ _ xs ys x∈ys , x∈zs)

  _⊆ˢ_ _⊇ˢ_ _⊈ˢ_ _⊉ˢ_ : Rel Bag' _
  s ⊆ˢ s′ = ∀ {x} → x ∈ˢ s → x ∈ˢ s′
  s ⊈ˢ s′ = ¬ s ⊆ˢ s′
  s ⊇ˢ s′ = s′ ⊆ˢ s
  s ⊉ˢ s′ = ¬ s ⊇ˢ s′

  ⊆ˢ-trans : Transitive _⊆ˢ_
  ⊆ˢ-trans ij ji = ji ∘ ij

  _≈ˢ_ : Rel₀ Bag'
  s ≈ˢ s′ = (s ⊆ˢ s′) × (s′ ⊆ˢ s)

  ≈ˢ-refl : Reflexive _≈ˢ_
  ≈ˢ-refl = (id , id)

  ≈ˢ-sym : Symmetric _≈ˢ_
  ≈ˢ-sym = Product.swap

  ≈ˢ-trans : Transitive _≈ˢ_
  ≈ˢ-trans = λ{ (ij , ji) (jk , kj) → ⊆ˢ-trans ij jk , ⊆ˢ-trans kj ji }

  ≈ˢ-equiv : IsEquivalence _≈ˢ_
  ≈ˢ-equiv = record { refl = ≈ˢ-refl; sym = ≈ˢ-sym; trans = ≈ˢ-trans }

  ≈ˢ-setoid : Setoid σ 0ℓ
  ≈ˢ-setoid = record { Carrier = Bag'; _≈_ = _≈ˢ_; isEquivalence = ≈ˢ-equiv }

  module ≈ˢ-Reasoning = BinSetoid ≈ˢ-setoid

  open Alg _≈ˢ_

  ∅─-identityʳ : RightIdentity ∅ _─_
  ∅─-identityʳ xs = (∈-─⁻ _ _ _) , (λ x∈ → ∈-─⁺ _ _ _ x∈ (∉∅ _))

  ∅∪-identityˡ : LeftIdentity ∅ _∪_
  ∅∪-identityˡ xs = (λ x∈ → case ∈-∪⁻ _ ∅ xs x∈ of λ{ (inj₁ x∈∅) → ⊥-elim (∉∅ _ x∈∅); (inj₂ x∈xs) → x∈xs} )
                  , ∈-∪⁺ʳ _ ∅ xs

  ∅∪-identityʳ : RightIdentity ∅ _∪_
  ∅∪-identityʳ xs = (λ x∈ → case ∈-∪⁻ _ xs ∅ x∈ of λ{ (inj₁ x∈xs) → x∈xs; (inj₂ x∈∅) → ⊥-elim (∉∅ _ x∈∅)} )
                  , ∈-∪⁺ˡ _ xs ∅

  ∩-comm : Commutative _∩_
  ∩-comm xs ys
    = (λ x∈ → let (x∈xs , x∈ys) = ∈-∩⁻ _ xs ys x∈ in ∈-∩⁺ _ ys xs x∈ys x∈xs)
    , (λ x∈ → let (x∈ys , x∈xs) = ∈-∩⁻ _ ys xs x∈ in ∈-∩⁺ _ xs ys x∈xs x∈ys)

  ∪-comm : Commutative _∪_
  ∪-comm xs ys
    = (λ x∈ → case ∈-∪⁻ _ xs ys x∈ of λ{ (inj₁ x∈xs) → ∈-∪⁺ʳ _ ys xs x∈xs; (inj₂ x∈ys) → ∈-∪⁺ˡ _ ys xs x∈ys})
    , (λ x∈ → case ∈-∪⁻ _ ys xs x∈ of λ{ (inj₁ x∈ys) → ∈-∪⁺ʳ _ xs ys x∈ys; (inj₂ x∈xs) → ∈-∪⁺ˡ _ xs ys x∈xs})

record DecBagᴵ (A : Set) (σ : Level) ⦃ _ : Bagᴵ A σ ⦄ ⦃ _ : DecEq A ⦄ : Set (lsuc σ) where
  open Bagᴵ it
  field
    -- _≈ˢ?_ : Decidable² _≈ˢ_
    _∈ˢ?_ : Decidable² _∈ˢ_
    _♯ˢ?_ : Decidable² _♯ˢ_

  infix 4 _∈ˢ?_ _∉ˢ?_

  _∉ˢ?_ : Decidable² _∉ˢ_
  x ∉ˢ? s = ¬? (x ∈ˢ? s)

  instance
    Dec-∈ˢ : ∀ {x : A} {xs : Bag'} → (x ∈ˢ xs) ⁇
    Dec-∈ˢ .dec = _ ∈ˢ? _

    Dec-♯ : _♯ˢ_ ⁇²
    Dec-♯ .dec = _ ♯ˢ? _

record ListBagᴵ (A : Set) (σ : Level) ⦃ _ : Bagᴵ A σ ⦄ : Set (lsuc σ) where
  open Bgaᴵ it
  field
    toList : Bag' → List A
    fromList : List A → Bag'
    from↔to : ∀ xs → Unique xs → toList (fromList xs) ≡ xs
    ∈ˢ-fromList : ∀ {x : A} {xs : List A} → x ∈ xs ↔ x ∈ˢ fromList xs

  ∈ˢ-fromList⁺ : ∀ {x : A} {xs : List A} → x ∈ xs → x ∈ˢ fromList xs
  ∈ˢ-fromList⁺ = proj₁ ∈ˢ-fromList

  ∈ˢ-fromList⁻ : ∀ {x : A} {xs : List A} → x ∈ˢ fromList xs → x ∈ xs
  ∈ˢ-fromList⁻ = proj₂ ∈ˢ-fromList

  instance
    Measurable-Bag : Measurable Bag'
    Measurable-Bag = record {∣_∣ = length ∘ toList}

record DecEqBagᴵ (A : Set) (σ : Level) ⦃ _ : Bagᴵ A σ ⦄ ⦃ _ : DecEq A ⦄ : Set (lsuc σ) where
  open Bagᴵ it
  field deceq : DecEq Bag'
  instance DecEq-Bag' = deceq
