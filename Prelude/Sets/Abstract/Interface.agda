{-# OPTIONS --safe #-}
open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.InferenceRules
open import Prelude.Membership
open import Prelude.DecEq.Core
open import Prelude.Decidable
open import Prelude.Semigroup
open import Prelude.Applicative
open import Prelude.Measurable
open import Prelude.Apartness
open import Prelude.Setoid
open import Prelude.ToList; open import Prelude.FromList
open import Prelude.Null

module Prelude.Sets.Abstract.Interface (A : Type) (σ : Level) where

record Setᴵ : Type (lsuc σ) where
  constructor mkSetᴵ
  field
    Set' : Type σ
    ∅ : Set'
    singleton : A → Set'
    _∈ˢ_ : A → Set' → Set
    _─_ _∪_ _∩_ : Op₂ Set'

  syntax Set' {A = A} = Set⟨ A ⟩
  infixr 8 _─_
  infixr 7 _∩_
  infixr 6 _∪_
  infix  4 _∈ˢ_ _∉ˢ_

  _∉ˢ_ : A → Set' → Type _
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

  open Derive-⊆-from-∈ _∈ˢ_ public renaming
    ( _⊆_ to _⊆ˢ_; _⊈_ to _⊈ˢ_; ⊆-trans to ⊆ˢ-trans
    ; _⊇_ to _⊇ˢ_; _⊉_ to _⊉ˢ_; ⊇-trans to ⊇ˢ-trans
    )

  instance
    Setoid-Set : ISetoid Set'
    Setoid-Set = λ where
      .relℓ → 0ℓ
      ._≈_ s s′ → (s ⊆ˢ s′) × (s′ ⊆ˢ s)

    SetoidLaws-Set : SetoidLaws Set'
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

  module _ {s s′ : Set'} where
    ≈⇒⊆ˢ : s ≈ s′ → s ⊆ˢ s′
    ≈⇒⊆ˢ = proj₁

    ≈⇒⊆ˢ˘ : s ≈ s′ → s′ ⊆ˢ s
    ≈⇒⊆ˢ˘ = proj₂

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

  private variable xs ys zs : Set'

  ∪-∅ : (xs ∪ ys) ≈ ∅ → (xs ≈ ∅) × (ys ≈ ∅)
  ∪-∅ {xs}{ys} p = (≈⇒⊆ˢ {xs ∪ ys}{∅} p ∘ ∈-∪⁺ˡ _ xs ys , (⊥-elim ∘ ∉∅ _))
                 , (≈⇒⊆ˢ {xs ∪ ys}{∅} p ∘ ∈-∪⁺ʳ _ xs ys , (⊥-elim ∘ ∉∅ _))

  ∪-∅ˡ : (xs ∪ ys) ≈ ∅ → xs ≈ ∅
  ∪-∅ˡ {xs}{ys} = proj₁ ∘ ∪-∅ {xs}{ys}

  ∪-∅ʳ : (xs ∪ ys) ≈ ∅ → ys ≈ ∅
  ∪-∅ʳ {xs}{ys} = proj₂ ∘ ∪-∅ {xs}{ys}

  ∪-∩ : ((xs ∪ ys) ∩ zs) ≈ ((xs ∩ zs) ∪ (ys ∩ zs))
  ∪-∩ {xs}{ys}{zs} =
    (λ x∈ →
    let x∈∪ , x∈zs = ∈-∩⁻ _ (xs ∪ ys) zs x∈
    in  case ∈-∪⁻ _ xs ys x∈∪ of λ where
          (inj₁ x∈xs) → ∈-∪⁺ˡ _ (xs ∩ zs) (ys ∩ zs)
                                (∈-∩⁺ _ xs zs x∈xs x∈zs)
          (inj₂ x∈ys) → ∈-∪⁺ʳ _ (xs ∩ zs) (ys ∩ zs)
                                (∈-∩⁺ _ ys zs x∈ys x∈zs))
    , (∈-∪⁻ _ (xs ∩ zs) (ys ∩ zs) >≡> λ where
        (inj₁ x∈) → let x∈xs , x∈zs = ∈-∩⁻ _ xs zs x∈
                    in ∈-∩⁺ _ (xs ∪ ys) zs (∈-∪⁺ˡ _ xs ys x∈xs) x∈zs
        (inj₂ x∈) → let x∈ys , x∈zs = ∈-∩⁻ _ ys zs x∈
                    in ∈-∩⁺ _ (xs ∪ ys) zs (∈-∪⁺ʳ _ xs ys x∈ys) x∈zs)

  -- ** apartness
  instance
    Apart-Set : Set' // Set'
    Apart-Set ._♯_ s s′ = s ∩ s′ ≈ ∅

  _♯ˢ_  = Rel₀ Set' ∋ _♯_

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

-- ** augmented interface for finite sets
record FinSetᴵ ⦃ _ : DecEq A ⦄ : Type (lsuc σ) where
  field
    setᴵ : Setᴵ
  open Setᴵ setᴵ public

  -- decidable membership & apartness
  field
    _∈ˢ?_ : Decidable² _∈ˢ_
    _♯ˢ?_ : Decidable² _♯ˢ_

  -- conversion from/to lists
  field instance
    ToList-Set   : ToList Set' A
    FromList-Set : FromList A Set'
  instance _ = ToList-Set; instance _ = FromList-Set -- make instances available for subsequent fields
  field
    from↔to : ∀ xs → Unique xs → toList (fromList {B = Set'} xs) ≡ xs
    ∈ˢ-fromList : ∀ {x : A} {xs : List A} → x ∈ xs ↔ x ∈ˢ fromList xs

  -- decidable equality of sets
  field instance
    DecEq-Set : DecEq Set'

  infix 4 _∈ˢ?_ _∉ˢ?_ _♯ˢ?_

  _∉ˢ?_ : Decidable² _∉ˢ_
  x ∉ˢ? s = ¬? (x ∈ˢ? s)

  ∈ˢ-fromList⁺ : ∀ {x : A} {xs : List A} → x ∈ xs → x ∈ˢ fromList xs
  ∈ˢ-fromList⁺ = proj₁ ∈ˢ-fromList

  ∈ˢ-fromList⁻ : ∀ {x : A} {xs : List A} → x ∈ˢ fromList xs → x ∈ xs
  ∈ˢ-fromList⁻ = proj₂ ∈ˢ-fromList

  instance
    Dec-∈ˢ : ∀ {x : A} {xs : Set'} → (x ∈ˢ xs) ⁇
    Dec-∈ˢ .dec = _ ∈ˢ? _

    Dec-♯ : _♯ˢ_ ⁇²
    Dec-♯ .dec = _ ♯ˢ? _

    Measurable-Set : Measurable Set'
    Measurable-Set = record {∣_∣ = length ∘ toList}

  -- ** lifting from list predicates/relations to set predicates/relations
  private
    record Lift (F : ∀ {ℓ} → Type ℓ → Type (1ℓ ⊔ₗ ℓ)) : Type (1ℓ ⊔ₗ σ) where
      field ↑ : F (List A) → F Set'
    open Lift ⦃...⦄

    instance
      Lift-Pred : Lift Pred₀
      Lift-Pred .↑ P = P ∘ toList

      Lift-Rel : Lift Rel₀
      Lift-Rel .↑ _~_ = _~_ on toList

  -- e.g. All/Any predicates for sets
  Allˢ Anyˢ : Pred₀ A → Pred₀ Set'
  Allˢ = ↑ ∘ All
  Anyˢ = ↑ ∘ Any

  private variable P : Pred A 0ℓ

  allˢ? : Decidable¹ P → Decidable¹ (Allˢ P)
  allˢ? P? = all? P? ∘ toList

  anyˢ? : Decidable¹ P → Decidable¹ (Anyˢ P)
  anyˢ? P? = any? P? ∘ toList
