module Prelude.Maps.Abstract.Interface where

import Relation.Binary.Reasoning.Setoid as BinSetoid

open import Prelude.Init
open SetAsType
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Applicative
open import Prelude.Semigroup
open import Prelude.Monoid
open import Prelude.InferenceRules
open import Prelude.Functor
open import Prelude.Apartness renaming (_♯_ to _♯₀_)
open import Prelude.Setoid    renaming (_≈_ to _≈₀_)

record Mapᴵ (K V : Type) (σ : Level) : Type (lsuc σ) where
  constructor mkMapᴵ
  field
    Map : Type σ

    ∅ : Map
    _∪_ : Op₂ Map -- left-biased

    _⁉_ : Map → K → Maybe V
    _∈ᵈ_ : K → Map → Type

    ⦃ Apart-Map ⦄ : Map //^⦅ 0ℓ ⦆ Map

  -- syntactic sugar
  syntax Map {K = K} {V = V} = Map⟨ K ↦ V ⟩

  -- operator precedence
  infix  6 _⁉_
  infixr 5 _∪_
  infix  4 _∈ᵈ_ _∉ᵈ_

  _∉ᵈ_ : K → Map → Type
  k ∉ᵈ m = ¬ (k ∈ᵈ m)

  -- equivalence
  instance
    Setoid-Map : ISetoid Map
    Setoid-Map = record
      { relℓ  = 0ℓ
      ; _≈_ = λ m m′ → ∀ k → m ⁉ k ≡ m′ ⁉ k
      }

  private infix 4 _≈_; _≈_ = Rel₀ Map ∋ _≈₀_ {A = Map}
  open Alg _≈_

  instance
    SetoidLaws-Map : Setoid-Laws Map
    SetoidLaws-Map = record {isEquivalence = record
      { refl = λ _ → refl
      ; sym = λ p k → sym (p k)
      ; trans = λ p q k → trans (p k) (q k)
      }}

  -- derived relations
  private infix 4 _♯_; _♯_ = Rel₀ Map ∋ _♯₀_ {A = Map}

  ⟨_⊎_⟩≡_ : Map → Map → Map → Type
  ⟨ m ⊎ m′ ⟩≡ m″ = (m ♯ m′) × ((m ∪ m′) ≈ m″)

  _[_↦_] : Map → K → V → Type
  m [ k ↦ v ] = m ⁉ k ≡ just v

  _[_↦_]∅ : Map → K → V → Type
  m [ k ↦ v ]∅ = m [ k ↦ v ] × ∀ k′ → k′ ≢ k → k′ ∉ᵈ m

  field
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

    -- introduction/elimination of union
    ∈ᵈ-∪⁻ : ∀ k s₁ s₂ → k ∈ᵈ (s₁ ∪ s₂) → (k ∈ᵈ s₁) ⊎ (k ∈ᵈ s₂)
    ∈ᵈ-∪⁺ : ∀ k s₁ s₂ → (k ∈ᵈ s₁) ⊎ (k ∈ᵈ s₂) → k ∈ᵈ (s₁ ∪ s₂)
    ∪-chooseₗ : ∀ {s₁ s₂} → s₁ ♯ s₂ → (∀ {k} → k ∉ᵈ s₂ → (s₁ ∪ s₂) ⁉ k ≡ s₁ ⁉ k)
    ∪-chooseᵣ : ∀ {s₁ s₂} → s₁ ♯ s₂ → (∀ {k} → k ∈ᵈ s₂ → (s₁ ∪ s₂) ⁉ k ≡ s₂ ⁉ k)

    ♯-∪⁻ʳ : ∀ {s₁}{s₂}{s₃} → s₁ ♯ (s₂ ∪ s₃) → (s₁ ♯ s₂) × (s₁ ♯ s₃)
    ♯-∪⁻ˡ : ∀ {s₁}{s₂}{s₃} → (s₁ ∪ s₂) ♯ s₃ → (s₁ ♯ s₃) × (s₂ ♯ s₃)
    ♯-∪⁺ˡ : ∀ {s₁}{s₂}{s₃} → (s₁ ♯ s₃) × (s₂ ♯ s₃) → (s₁ ∪ s₂) ♯ s₃
    ♯-∪⁺ʳ : ∀ {s₁}{s₂}{s₃} → (s₁ ♯ s₂) × (s₁ ♯ s₃) → s₁ ♯ (s₂ ∪ s₃)

    -- associativity
    ∪-assocʳ : ∀ {s₁ s₂ s₃} → s₁ ∪ (s₂ ∪ s₃) ≈ (s₁ ∪ s₂) ∪ s₃
    ∪≡-assocʳ : ∀ {s₁}{s₂}{s₃}{s} → s₂ ♯ s₃ → ⟨ s₁ ⊎ (s₂ ∪ s₃) ⟩≡ s → ⟨ (s₁ ∪ s₂) ⊎ s₃ ⟩≡ s

  private variable
    s s₁ s₂ s₃ s₁₂ s₂₃ m m′ m₁ m₂ m₃ m₁₂ m₂₃ : Map
    k k′ : K
    v v′ : V
    f g : Map → Map

  module _ {s k} where
    ⁉⇒∉ᵈ : Is-nothing (s ⁉ k) → k ∉ᵈ s
    ⁉⇒∉ᵈ p k∈ with s ⁉ k | p | ∈ᵈ⇒⁉ k∈
    ... | just _ | M.All.just () | _

    ∉ᵈ⇒⁉ : k ∉ᵈ s → Is-nothing (s ⁉ k)
    ∉ᵈ⇒⁉ k∉ with s ⁉ k | ⁉⇒∈ᵈ {s}{k}
    ... | just _  | p = ⊥-elim $ k∉ (p auto)
    ... | nothing | _ = auto

  module _ {s k v} where
    ⁉⇒↦ : s ⁉ k ≡ just v → s [ k ↦ v ]
    ⁉⇒↦ = id

    ↦⇒⁉ : s [ k ↦ v ] → s ⁉ k ≡ just v
    ↦⇒⁉ = id

  ∉ᵈ-cong : ∀ {k s₁ s₂} → s₁ ≈ s₂ → k ∉ᵈ s₁ → k ∉ᵈ s₂
  ∉ᵈ-cong s≈ k∉ = k∉ ∘ ∈ᵈ-cong (≈-sym s≈)

  ↦-∪⁺ʳ′ : ∀ {s₁ s₂ k v} → k ∉ᵈ s₁ → s₂ [ k ↦ v ] → (s₁ ∪ s₂) [ k ↦ v ]
  ↦-∪⁺ʳ′ {s₁}{s₂}{k}{v} k∉ sk≡ = trans (sym (↦-∪⁺ʳ k∉)) sk≡

  ∪-congʳ : ∀ {s₁}{s₂}{s₃} → s₁ ♯ s₂ → s₂ ≈ s₃ → (s₁ ∪ s₂) ≈ (s₁ ∪ s₃)
  ∪-congʳ {s₁}{s₂}{s₃} s₁♯s₂ s₂≈s₃ =
    begin s₁ ∪ s₂ ≈⟨ ∪-comm s₁♯s₂ ⟩
          s₂ ∪ s₁ ≈⟨ ∪-cong s₂≈s₃ ⟩
          s₃ ∪ s₁ ≈⟨ ∪-comm (♯-cong s₂≈s₃ $ ♯-comm s₁♯s₂) ⟩
          s₁ ∪ s₃ ∎
    where open ≈-Reasoning

  ∈ᵈ-∪⁺ˡ : ∀ k s₁ s₂ → k ∈ᵈ s₁ → k ∈ᵈ (s₁ ∪ s₂)
  ∈ᵈ-∪⁺ˡ _ _ _ = ∈ᵈ-∪⁺ _ _ _ ∘ inj₁
  ∈ᵈ-∪⁺ʳ : ∀ k s₁ s₂ → k ∈ᵈ s₂ → k ∈ᵈ (s₁ ∪ s₂)
  ∈ᵈ-∪⁺ʳ _ _ _ = ∈ᵈ-∪⁺ _ _ _ ∘ inj₂

  ∉ᵈ-∪⁻ : k ∉ᵈ (s₁ ∪ s₂) → (k ∉ᵈ s₁) × (k ∉ᵈ s₂)
  ∉ᵈ-∪⁻ {k}{s₁}{s₂} k∉ = (k∉ ∘ ∈ᵈ-∪⁺ k s₁ s₂ ∘ inj₁) , (k∉ ∘ ∈ᵈ-∪⁺ k s₁ s₂ ∘ inj₂)

  ∉ᵈ-∪⁺ : (k ∉ᵈ s₁) × (k ∉ᵈ s₂) → k ∉ᵈ (s₁ ∪ s₂)
  ∉ᵈ-∪⁺ {k}{s₁}{s₂} (k∉₁ , k∉₂) k∈ = case ∈ᵈ-∪⁻ k s₁ s₂ k∈ of λ where
    (inj₁ k∈₁) → k∉₁ k∈₁
    (inj₂ k∈₂) → k∉₂ k∈₂

  ∈ᵈ-∪≡ : ⟨ s₁ ⊎ s₂ ⟩≡ s → k ∈ᵈ s → k ∈ᵈ s₁ ⊎ k ∈ᵈ s₂
  ∈ᵈ-∪≡ (_ , p) = ∈ᵈ-∪⁻ _ _ _ ∘ ∈ᵈ-cong (≈-sym p)

  ∉ᵈ-∪≡ : ⟨ s₁ ⊎ s₂ ⟩≡ s → k ∉ᵈ s₁ → k ∉ᵈ s₂ → k ∉ᵈ s
  ∉ᵈ-∪≡ (_ , p) k∉₁ k∉₂ k∈
    with ∈ᵈ-∪⁻ _ _ _ (∈ᵈ-cong (≈-sym p) k∈)
  ... | inj₁ k∈₁ = ⊥-elim $ k∉₁ k∈₁
  ... | inj₂ k∈₂ = ⊥-elim $ k∉₂ k∈₂

  record DecMapᴵ : Type (lsuc σ) where
    field _∈ᵈ?_ : Decidable² _∈ᵈ_
    infix 4 _∈ᵈ?_ _∉ᵈ?_
    _∉ᵈ?_ : Decidable² _∉ᵈ_
    k ∉ᵈ? m = ¬? (k ∈ᵈ? m)

    instance
      Dec-∈ᵈ : ∀ {k : K} {m : Map} → (k ∈ᵈ m) ⁇
      Dec-∈ᵈ .dec = _∈ᵈ?_ _ _

  infix 4 _⊆ᵈ_ _⊈ᵈ_
  _⊆ᵈ_ _⊈ᵈ_ : Rel₀ Map
  m ⊆ᵈ m′ = ∀ k → k ∈ᵈ m → k ∈ᵈ m′
  k ⊈ᵈ m = ¬ (k ⊆ᵈ m)

  KeyMonotonic KeyPreserving : (Map → Map) → Type σ
  KeyMonotonic  f = ∀ s → s   ⊆ᵈ f s
  KeyPreserving f = ∀ s → f s ⊆ᵈ s

  ≈-cong : ∀ {P : K → Maybe V → Type}
    → s₁ ≈ s₂
    → (∀ k → P k (s₁ ⁉ k))
    → (∀ k → P k (s₂ ⁉ k))
  ≈-cong {P = P} eq p k = subst (P k) (eq k) (p k)

  ∪≡-comm : Symmetric (⟨_⊎_⟩≡ s)
  ∪≡-comm (s₁♯s₂ , ≡s) = ♯-comm s₁♯s₂ , ≈-trans (≈-sym $ ∪-comm s₁♯s₂) ≡s

  ∪≡-cong : s₁ ≈ s₂ → ⟨ s₁ ⊎ s₃ ⟩≡ s → ⟨ s₂ ⊎ s₃ ⟩≡ s
  ∪≡-cong eq (s₁♯s₃ , ≡s) = ♯-cong eq s₁♯s₃ , ≈-trans (≈-sym (∪-cong eq)) ≡s

  ∪-assocˡ : (s₁ ∪ s₂) ∪ s₃ ≈ s₁ ∪ (s₂ ∪ s₃)
  ∪-assocˡ = ≈-sym ∪-assocʳ

  ⊎≈-assocʳ :
    ∙ ⟨ s₁ ⊎ s₂₃ ⟩≡ s
    ∙ ⟨ s₂ ⊎ s₃  ⟩≡ s₂₃
      ───────────────────
      ⟨ (s₁ ∪ s₂) ⊎ s₃ ⟩≡ s
    × (s₁ ♯ s₂)
  ⊎≈-assocʳ {s₁}{s₂₃}{s}{s₂}{s₃} (s₁♯s₂₃ , ≡s) (s₂♯s₃ , ≡s₂₃) =
    ∪≡-assocʳ s₂♯s₃ ≡ss , proj₁ (♯-∪⁻ʳ s₁♯s₂₃′)
    where
      s₁♯s₂₃′ : s₁ ♯ (s₂ ∪ s₃)
      s₁♯s₂₃′ = ♯-comm $ ♯-cong (≈-sym ≡s₂₃) $ ♯-comm s₁♯s₂₃

      ≡ss : ⟨ s₁ ⊎ (s₂ ∪ s₃) ⟩≡ s
      ≡ss = s₁♯s₂₃′ , ≈-trans (≈-trans (∪-comm s₁♯s₂₃′) (≈-trans (∪-cong ≡s₂₃) (≈-sym $ ∪-comm s₁♯s₂₃))) ≡s

  ∪≡-assocˡ : ∀ {s₁ s₂ s₃ s} → s₁ ♯ s₂ → ⟨ (s₁ ∪ s₂) ⊎ s₃ ⟩≡ s → ⟨ s₁ ⊎ (s₂ ∪ s₃)  ⟩≡ s
  ∪≡-assocˡ {s₁}{s₂}{s₃}{s} s₁♯s₂ p@(s₁₂♯s₃ , _) =
      ∪≡-comm ∘ ∪≡-assocʳ (♯-comm $ proj₁ $ ♯-∪⁻ˡ s₁₂♯s₃)
    $ ∪≡-comm ∘ ∪≡-assocʳ s₁♯s₂
    $ ∪≡-comm p

  ⊎≈-assocˡ :
    ∙ ⟨ s₁₂ ⊎ s₃ ⟩≡ s
    ∙ ⟨ s₁ ⊎ s₂  ⟩≡ s₁₂
      ───────────────────
      ⟨ s₁ ⊎ (s₂ ∪ s₃) ⟩≡ s
    × (s₂ ♯ s₃)
  ⊎≈-assocˡ {s₁₂}{s₃}{s}{s₁}{s₂} (s₁₂♯s₃ , ≡s) (s₁♯s₂ , ≡s₁₂) =
    ∪≡-assocˡ s₁♯s₂ ≡ss , proj₂ (♯-∪⁻ˡ {s₁ = s₁} s₁₂♯s₃′)
    where
      s₁₂♯s₃′ : (s₁ ∪ s₂) ♯ s₃
      s₁₂♯s₃′ = ♯-cong (≈-sym ≡s₁₂) s₁₂♯s₃

      ≡ss : ⟨ (s₁ ∪ s₂) ⊎ s₃ ⟩≡ s
      ≡ss = s₁₂♯s₃′ , ≈-trans (∪-cong ≡s₁₂) ≡s

  record WithBuildᴵ : Type (lsuc σ) where
    field
      buildMap : (K → Maybe V) → Map
      buildMap-sound : ∀ (f : K → Maybe V) → ∀ k → buildMap f ⁉ k ≡ f k

    module _ ⦃ mᵥ : Monoid V ⦄ ⦃ _ : SemigroupLaws≡ V ⦄ ⦃ _ : MonoidLaws≡ V ⦄ where
      infix 6 _⁉ε_
      _⁉ε_ : Map → K → V
      m ⁉ε k = fromMaybe ε (m ⁉ k)

      instance
        Semigroup-Map : Semigroup Map
        Semigroup-Map ._◇_ m m′ = buildMap λ k → (m ⁉ k) ◇ (m′ ⁉ k)

      ◇-⁉ : ∀ m m′ → (m ◇ m′) ⁉ k ≡ (m ⁉ k) ◇ (m′ ⁉ k)
      ◇-⁉ {k} m m′ = buildMap-sound (λ k → (m ⁉ k) ◇ (m′ ⁉ k)) k

      ⟨_◇_⟩≡_ : 3Rel Map 0ℓ
      ⟨ m₁ ◇ m₂ ⟩≡ m = m₁ ◇ m₂ ≈ m

      private
        ◇ᵐ-comm : Commutative (_◇_ {A = Map})
        ◇ᵐ-comm m m′ k =
            begin
              (buildMap λ k → (m ⁉ k) ◇ (m′ ⁉ k)) ⁉ k
            ≡⟨ buildMap-sound _ _ ⟩
              (m ⁉ k) ◇ (m′ ⁉ k)
            ≡⟨ ◇-comm (m ⁉ k) (m′ ⁉ k) ⟩
              (m′ ⁉ k) ◇ (m ⁉ k)
            ≡⟨ sym $ buildMap-sound _ _ ⟩
              (buildMap λ k → (m′ ⁉ k) ◇ (m ⁉ k)) ⁉ k
            ∎ where open ≡-Reasoning

        ◇ᵐ-assocʳ : Associative (_◇_ {A = Map})
        ◇ᵐ-assocʳ m₁ m₂ m₃ k =
          begin
            ((m₁ ◇ m₂) ◇ m₃) ⁉ k
          ≡⟨ ◇-⁉ _ _ ⟩
            ((m₁ ◇ m₂) ⁉ k) ◇ (m₃ ⁉ k)
          ≡⟨ go ⟩
            (m₁ ⁉ k) ◇ ((m₂ ◇ m₃) ⁉ k)
          ≡⟨ sym $ ◇-⁉ _ _ ⟩
            (m₁ ◇ m₂ ◇ m₃) ⁉ k
          ∎ where
            open ≡-Reasoning

            go : ((m₁ ◇ m₂) ⁉ k) ◇ (m₃ ⁉ k)
                ≡ (m₁ ⁉ k) ◇ ((m₂ ◇ m₃) ⁉ k)
            go
              rewrite ◇-⁉ {k} (m₁ ◇ m₂) m₃
                    | ◇-⁉ {k} m₁ m₂
                    | ◇-⁉ {k} m₁ (m₂ ◇ m₃)
                    | ◇-⁉ {k} m₂ m₃
              = ◇-assocʳ (m₁ ⁉ k) _ _
      instance
        SemigroupLaws-Map : SemigroupLaws Map _≈_
        SemigroupLaws-Map = record {◇-comm = ◇ᵐ-comm; ◇-assocʳ = ◇ᵐ-assocʳ}

      ◇≡-comm : Symmetric (⟨_◇_⟩≡ m)
      ◇≡-comm ≈m = ≈-trans (◇ᵐ-comm _ _) ≈m

      ◇-congˡ :
        m₁ ≈ m₂
        ───────────────────
        (m₁ ◇ m₃) ≈ (m₂ ◇ m₃)
      ◇-congˡ {m₁}{m₂}{m₃} m₁≈m₂ k =
        begin
          (m₁ ◇ m₃) ⁉ k
        ≡⟨ buildMap-sound _ _ ⟩
          (m₁ ⁉ k) ◇ (m₃ ⁉ k)
        ≡⟨  cong (_◇ (m₃ ⁉ k)) (m₁≈m₂ k) ⟩
          (m₂ ⁉ k) ◇ (m₃ ⁉ k)
        ≡⟨ sym $ buildMap-sound _ _ ⟩
          (m₂ ◇ m₃) ⁉ k
        ∎ where open ≡-Reasoning

      ◇-congʳ : m₂ ≈ m₃ → (m₁ ◇ m₂) ≈ (m₁ ◇ m₃)
      ◇-congʳ {m₂}{m₃}{m₁} m₂≈m₃ =
        begin m₁ ◇ m₂ ≈⟨ ◇ᵐ-comm _ _ ⟩
              m₂ ◇ m₁ ≈⟨ ◇-congˡ m₂≈m₃ ⟩
              m₃ ◇ m₁ ≈⟨ ◇ᵐ-comm _ _ ⟩
              m₁ ◇ m₃ ∎ where open ≈-Reasoning

      ◇≈-assocˡ :
        ∙ ⟨ m₁₂ ◇ m₃ ⟩≡ m
        ∙ ⟨ m₁ ◇ m₂  ⟩≡ m₁₂
          ───────────────────
          ⟨ m₁ ◇ (m₂ ◇ m₃) ⟩≡ m
      ◇≈-assocˡ ≡m ≡m₁₂ = ≈-trans (≈-trans (≈-sym (◇-assocʳ _ _ _)) (◇-congˡ ≡m₁₂)) ≡m
        -- begin m₁ ◇ (m₂ ◇ m₃) ≈⟨ ≈-sym $ ◇-assocʳ _ _ _ ⟩
        --       (m₁ ◇ m₂) ◇ m₃ ≈⟨ ◇-congˡ ≡m₁₂ ⟩
        --       m₁₂ ◇ m₃       ≈⟨ ≡m ⟩
        --       m              ∎ where open ≈-Reasoning

      ◇≈-assocʳ :
        ∙ ⟨ m₁ ◇ m₂₃ ⟩≡ m
        ∙ ⟨ m₂ ◇ m₃  ⟩≡ m₂₃
          ───────────────────
          ⟨ (m₁ ◇ m₂) ◇ m₃ ⟩≡ m
      ◇≈-assocʳ ≡m ≡m₂₃ = ≈-trans (≈-trans (◇-assocʳ _ _ _) (◇-congʳ ≡m₂₃)) ≡m
        -- begin (m₁ ◇ m₂) ◇ m₃ ≈⟨ ◇-assocʳ _ _ _ ⟩
        --       m₁ ◇ (m₂ ◇ m₃) ≈⟨ ◇-congʳ ≡m₂₃ ⟩
        --       m₁ ◇ m₂₃       ≈⟨ ≡m ⟩
        --       m              ∎ where open ≈-Reasoning

      Is-just-◇⁻ : ∀ (m m′ : Maybe V) → Is-just (m ◇ m′) → Is-just m ⊎ Is-just m′
      Is-just-◇⁻ (just _) _       _ = inj₁ auto
      Is-just-◇⁻ nothing (just _) _ = inj₂ auto

      Is-just-◇⁺ : ∀ (m m′ : Maybe V) → Is-just m ⊎ Is-just m′ → Is-just (m ◇ m′)
      Is-just-◇⁺ (just _) (just _) _        = auto
      Is-just-◇⁺ (just _) nothing  (inj₁ _) = auto
      Is-just-◇⁺ nothing  (just _) (inj₂ _) = auto

      ∈ᵈ-◇⁻ : ∀ k s₁ s₂ → k ∈ᵈ (s₁ ◇ s₂) → (k ∈ᵈ s₁) ⊎ (k ∈ᵈ s₂)
      ∈ᵈ-◇⁻ k s₁ s₂ k∈ = k∈′
        where
          p : Is-just ((s₁ ⁉ k) ◇ (s₂ ⁉ k))
          p = subst Is-just (buildMap-sound _ k) (∈ᵈ⇒⁉ k∈)

          k∈′ : (k ∈ᵈ s₁) ⊎ (k ∈ᵈ s₂)
          k∈′ = case Is-just-◇⁻ (s₁ ⁉ k) (s₂ ⁉ k) p of λ where
            (inj₁ x) → inj₁ (⁉⇒∈ᵈ x)
            (inj₂ x) → inj₂ (⁉⇒∈ᵈ x)

      ∈ᵈ-◇⁺ : ∀ k s₁ s₂ → (k ∈ᵈ s₁) ⊎ (k ∈ᵈ s₂) → k ∈ᵈ (s₁ ◇ s₂)
      ∈ᵈ-◇⁺ k s₁ s₂ k∈ = ⁉⇒∈ᵈ k∈′
        where
          p : Is-just (s₁ ⁉ k) ⊎ Is-just (s₂ ⁉ k)
          p = case k∈ of λ where
            (inj₁ x) → inj₁ (∈ᵈ⇒⁉ x)
            (inj₂ x) → inj₂ (∈ᵈ⇒⁉ x)

          k∈′ : Is-just ((s₁ ◇ s₂) ⁉ k)
          k∈′ = subst Is-just (sym $ buildMap-sound _ k) $′ Is-just-◇⁺ (s₁ ⁉ k) (s₂ ⁉ k) p

      ↦-◇⁺ˡ : k ∉ᵈ s₂ → s₁ ⁉ k ≡ (s₁ ◇ s₂) ⁉ k
      ↦-◇⁺ˡ {k = k}{s₂}{s₁} k∉ =
        begin
          s₁ ⁉ k
        ≡⟨ sym $ ε-identity .proj₂ (s₁ ⁉ k) ⟩
          (s₁ ⁉ k) ◇ nothing
        ≡⟨ cong ((s₁ ⁉ k) ◇_) (sym (Is-nothing≡ (∉ᵈ⇒⁉ k∉))) ⟩
          (s₁ ⁉ k) ◇ (s₂ ⁉ k)
        ≡⟨ sym $ ◇-⁉ _ _  ⟩
          (s₁ ◇ s₂) ⁉ k
        ∎ where open ≡-Reasoning

      ↦-◇⁺ʳ : k ∉ᵈ s₁ → s₂ ⁉ k ≡ (s₁ ◇ s₂) ⁉ k
      ↦-◇⁺ʳ {k = k}{s₁}{s₂} k∉ =
        begin
          s₂ ⁉ k
        ≡⟨ sym $ ε-identity .proj₁ (s₂ ⁉ k) ⟩
          nothing ◇ (s₂ ⁉ k)
        ≡⟨ cong (_◇ (s₂ ⁉ k)) (sym (Is-nothing≡ (∉ᵈ⇒⁉ k∉))) ⟩
          (s₁ ⁉ k) ◇ (s₂ ⁉ k)
        ≡⟨ sym $ ◇-⁉ _ _  ⟩
          (s₁ ◇ s₂) ⁉ k
        ∎ where open ≡-Reasoning

  module _ ⦃ _ : DecEq K ⦄ where

    -- record DecEqMapᴵ : Type (lsuc σ) where
    --   field deceq : DecEq Map
    --   instance DecEq-Map = deceq

    record WithSingletonᴵ : Type (lsuc σ) where
      field
        singleton : K × V → Map
        singleton-law : ∀ {k v} → singleton (k , v) [ k ↦ v ]∅
        singleton∈ : ∀ {A v k} → k ∈ᵈ singleton (A , v) → k ≡ A
        singleton♯ : ∀ {k v k′ v′} → k ≢ k′ → singleton (k , v) ♯ singleton (k′ , v′)
        singleton-collapse : ∀ {k v v′} → singleton (k , v) ∪ singleton (k , v′) ≈ singleton (k , v)

      singleton-law′ : ∀ {k v} → singleton (k , v) [ k ↦ v ]
      singleton-law′ {k}{v} = singleton-law {k}{v} .proj₁

      -- overwriting update
      update : K × V → Map → Map
      update entry = singleton entry ∪_

      update-mon : ∀ {k v} → KeyMonotonic (update (k , v))
      update-mon s _ = ∈ᵈ-∪⁺ʳ _ _ _

      field
        ≡-cong-update : s₁ ⁉ k′ ≡ s₂ ⁉ k′ → update (k , v) s₁ ⁉ k′ ≡ update (k , v) s₂ ⁉ k′
        ♯-cong-pre : KeyPreserving f → s₁ ♯ s₂ → f s₁ ♯ s₂

      ≈-cong-update : s₁ ≈ s₂ → update (k , v) s₁ ≈ update (k , v) s₂
      ≈-cong-update s₁≈s₂ = ≡-cong-update ∘ s₁≈s₂

      update-other : k ≢ k′ → update (k , v) s ⁉ k′ ≡ s ⁉ k′
      update-other {k}{k′}{v}{s} k≢ =
        begin
          update (k , v) s ⁉ k′
        ≡⟨⟩
          (singleton (k , v) ∪ s) ⁉ k′
        ≡⟨ sym $ ↦-∪⁺ʳ {singleton (k , v)} {s} {k′} (≢-sym k≢ ∘ singleton∈) ⟩
          s ⁉ k′
        ∎ where open ≡-Reasoning

      update-update : update (k , v′) (update (k , v) s) ≈ update (k , v′) s
      update-update {k}{v′}{v}{s} =
        begin
          update (k , v′) (update (k , v) s)
        ≡⟨⟩
          singleton (k , v′) ∪ (singleton (k , v) ∪ s)
        ≈⟨ ∪-assocʳ ⟩
          (singleton (k , v′) ∪ singleton (k , v)) ∪ s
        ≈⟨ ∪-cong singleton-collapse ⟩
          singleton (k , v′) ∪ s
        ≡⟨⟩
          update (k , v′) s
        ∎ where open ≈-Reasoning

      singleton≈ : m [ k ↦ v ]∅ → m ≈ singleton (k , v)
      singleton≈ {m}{k}{v} (eq , p) k′
        with k′ ≟ k
      ... | yes refl = trans eq (sym singleton-law′)
      ... | no  ≢k
        with m ⁉ k′ | ⁉⇒∈ᵈ {s = m} {k = k′}
      ... | just _  | q = ⊥-elim $ p k′ ≢k (q auto)
      ... | nothing | _
        with singleton (k , v) ⁉ k′ | ⁉⇒∈ᵈ {s = singleton (k , v)} {k = k′}
      ... | just _  | q = ⊥-elim $ ≢k (singleton∈ (q auto))
      ... | nothing | _ = refl

      singleton-accept : (singleton (k , v) ∪ s) ⁉ k ≡ just v
      singleton-accept {k}{v}{s} rewrite ↦-∪⁺ˡ {s₂ = s}{k}{v} singleton-law′ = refl

      singleton-reject : k′ ≢ k → (singleton (k , v) ∪ s) ⁉ k′ ≡ s ⁉ k′
      singleton-reject {s = s} k≢ rewrite ↦-∪⁺ʳ {s₂ = s} (k≢ ∘ singleton∈) = refl

      -- ** Command DSL for defining map transformations.
      module CommandDSL (wb : WithBuildᴵ) where
        open WithBuildᴵ wb

        modify : K → (V → V) → (Map → Map)
        modify k f m with m ⁉ k
        ... | nothing = m
        ... | just v  = update (k , f v) m

        modify-mon : ∀ {f} → KeyMonotonic (modify k f)
        modify-mon {k = k} {f = f} s with s ⁉ k
        ... | nothing = λ _ → id
        ... | just v  = update-mon s

        modify-pre : ∀ {f} → KeyPreserving (modify k f)
        modify-pre {k = k} {f = f} s k′ k∈
          with s ⁉ k in sk≡
        ... | nothing = k∈
        ... | just v
          with ∈ᵈ-∪⁻ k′ (singleton (k , f v)) s k∈
        ... | inj₁ k∈′ rewrite singleton∈ k∈′ = ⁉⇒∈ᵈ $ subst Is-just (sym sk≡) (M.Any.just tt)
        ... | inj₂ k∈s = k∈s

        modify-other : ∀ {f} → k ≢ k′ → modify k f s ⁉ k′ ≡ s ⁉ k′
        modify-other {k = k} {s = s} k≢ with s ⁉ k
        ... | nothing = refl
        ... | just _  = update-other k≢

        ≡-cong-modify : ∀ {f} → s₁ ⁉ k′ ≡ s₂ ⁉ k′ → modify k f s₁ ⁉ k′ ≡ modify k f s₂ ⁉ k′
        ≡-cong-modify {k′ = k′} {k = k} s≡
          with k ≟ k′
        ≡-cong-modify {s₁ = s₁} {s₂ = s₂} {k = k} s≡ | yes refl
          with s₁ ⁉ k | s₂ ⁉ k | s≡
        ... | nothing | nothing | _ = s≡
        ... | just _  | just _  | eq
          rewrite M.just-injective eq = ≡-cong-update s≡
        ≡-cong-modify {s₁ = s₁} {s₂ = s₂} {k = k} {f = f} s≡ | no k≢
          with s₁ ⁉ k | s₂ ⁉ k
        ... | nothing | nothing
          = s≡
        ... | just x | nothing
          rewrite update-other {k = k} {v = f x} {s = s₁} k≢ = s≡
        ... | nothing | just y
          rewrite update-other {k = k} {v = f y} {s = s₂} k≢ = s≡
        ... | just x | just y
          rewrite update-other {k = k} {v = f x} {s = s₁} k≢
                | update-other {k = k} {v = f y} {s = s₂} k≢ = s≡

        ≈-cong-modify : ∀ {f} → s₁ ≈ s₂ → modify k f s₁ ≈ modify k f s₂
        ≈-cong-modify {k = k} s₁≈s₂ = ≡-cong-modify ∘ s₁≈s₂

        modify-this : ∀ {f} → (modify k f s ⁉ k) ≡ (f <$> (s ⁉ k))
        modify-this {k}{s}{f} with s ⁉ k in s≡
        ... | nothing rewrite s≡ = refl
        ... | just v  rewrite ↦-∪⁺ˡ {s₂ = s} $ singleton-law′ {k = k}{f v} = refl

        modify∘modify : ∀ {f g} → modify k f (modify k g s) ≈ modify k (f ∘ g) s
        modify∘modify {k}{s}{f}{g} k′
          with k ≟ k′
        ... | no k≢ =
          begin
            modify k f (modify k g s) ⁉ k′
          ≡⟨ modify-other k≢ ⟩
            modify k g s ⁉ k′
          ≡⟨ modify-other k≢ ⟩
            s ⁉ k′
          ≡⟨ sym $ modify-other k≢ ⟩
            modify k (f ∘ g) s ⁉ k′
          ∎ where open ≡-Reasoning
        ... | yes refl =
          begin
            modify k f (modify k g s) ⁉ k
          ≡⟨ modify-this ⟩
            f <$> (modify k g s ⁉ k)
          ≡⟨ cong (fmap f) modify-this ⟩
            f <$> (g <$> (s ⁉ k))
          ≡⟨ sym $ M.map-compose (s ⁉ k) ⟩
            (f ∘ g) <$> (s ⁉ k)
          ≡⟨ sym $ modify-this ⟩
            modify k (f ∘ g) s ⁉ k
          ∎ where open ≡-Reasoning

        modify-id : ∀ {f} → (∀ x → f x ≡ x) → modify k f s ≈ s
        modify-id {k}{s}{f} f≗id k′
          with k ≟ k′
        ... | no k≢ rewrite modify-other {k = k}{k′}{s}{f} k≢ = refl
        ... | yes refl
          =
          begin
            modify k f s ⁉ k
          ≡⟨ modify-this ⟩
            f <$> (s ⁉ k)
          ≡⟨ IdFun-fmap f≗id (s ⁉ k) ⟩
            s ⁉ k′
          ∎ where open ≡-Reasoning

        module _ ⦃ mᵥ : Monoid V ⦄ ⦃ _ : SemigroupLaws≡ V ⦄ ⦃ _ : MonoidLaws≡ V ⦄ where
          singleton-accept◇ : k ∉ᵈ s → (singleton (k , v) ◇ s) ⁉ k ≡ just v
          singleton-accept◇ {k}{s}{v} k∉ =
            begin (singleton (k , v) ◇ s) ⁉ k ≡⟨ sym $ ↦-◇⁺ˡ k∉ ⟩
                  singleton (k , v) ⁉ k       ≡⟨ singleton-law′ {k}{v} ⟩
                  just v                      ∎ where open ≡-Reasoning

          singleton-reject◇ : k′ ≢ k → (singleton (k , v) ◇ s) ⁉ k′ ≡ s ⁉ k′
          singleton-reject◇ {s = s} k≢ rewrite ↦-◇⁺ʳ {s₂ = s} (k≢ ∘ singleton∈) = refl

          singleton◇ : singleton (k , v) ◇ singleton (k , v′) ≈ singleton (k , v ◇ v′)
          singleton◇ {A}{v}{v′} k
            with k ≟ A
          ... | yes refl =
            begin
              (singleton (A , v) ◇ singleton (A , v′)) ⁉ A
            ≡⟨ ◇-⁉ _ _ ⟩
              (singleton (A , v) ⁉ A) ◇ (singleton (A , v′) ⁉ A)
            ≡⟨ cong (_◇ (singleton (A , v′) ⁉ A)) singleton-law′ ⟩
              just v ◇ (singleton (A , v′) ⁉ A)
            ≡⟨ cong (just v ◇_) singleton-law′ ⟩
              just v ◇ just v′
            ≡⟨⟩
              just (v ◇ v′)
            ≡⟨ sym $ singleton-law′ ⟩
              singleton (A , v ◇ v′) ⁉ A
            ∎ where open ≡-Reasoning
          ... | no k≢A =
            begin
              (singleton (A , v) ◇ singleton (A , v′)) ⁉ k
            ≡⟨ ◇-⁉ _ _ ⟩
              (singleton (A , v) ⁉ k) ◇ (singleton (A , v′) ⁉ k)
            ≡⟨ cong (_◇ (singleton (A , v′) ⁉ k)) (Is-nothing≡ $ ∉ᵈ⇒⁉ k∉) ⟩
              nothing ◇ (singleton (A , v′) ⁉ k)
            ≡⟨ cong (nothing ◇_) (Is-nothing≡ $ ∉ᵈ⇒⁉ k∉) ⟩
              nothing
            ≡⟨ sym $ Is-nothing≡ $ ∉ᵈ⇒⁉ k∉ ⟩
              singleton (A , v ◇ v′) ⁉ k
            ∎ where open ≡-Reasoning
                    k∉ : ∀ {v} → k ∉ᵈ singleton (A , v)
                    k∉ = singleton-law .proj₂ k k≢A

          modify-thisˡ : ∀ {f} → k ∉ᵈ s → modify k f (singleton (k , v) ◇ s) ≈ (singleton (k , f v) ◇ s)
          modify-thisˡ {k = k} {s = s} {v = v} {f = f} k∉ k′
            with k ≟ k′
          ... | yes refl
            = qed
            where
              p : (singleton (k , v) ◇ s) ⁉ k ≡ just v
              p rewrite sym $ ↦-◇⁺ˡ {s₁ = singleton (k , v)} k∉ = singleton-law′

              q : (singleton (k , f v) ◇ s) ⁉ k ≡ just (f v)
              q rewrite sym $ ↦-◇⁺ˡ {s₁ = singleton (k , f v)} k∉ = singleton-law′

              qed : modify k f (singleton (k , v) ◇ s) ⁉ k ≡ (singleton (k , f v) ◇ s) ⁉ k
              qed rewrite p | q | p = singleton-accept {k}{f v}
          ... | no  k≢
            = begin
              modify k f (singleton (k , v) ◇ s) ⁉ k′
            ≡⟨ modify-other k≢ ⟩
              (singleton (k , v) ◇ s) ⁉ k′
            ≡⟨ singleton-reject◇ (≢-sym k≢) ⟩
              s ⁉ k′
            ≡⟨ (sym $ singleton-reject◇ (≢-sym k≢)) ⟩
              (singleton (k , f v) ◇ s) ⁉ k′
            ∎ where open ≡-Reasoning

        data Cmd : Type₁ where
          _∶_ : Cmd → Cmd → Cmd
          iff⦅_⦆_ : ∀ {P : Type} → Dec P → Cmd → Cmd
          just? : K → (V → Cmd) → Cmd
          _≔_ : K → V → Cmd
          [_←_] : (V → V) → K → Cmd

        iff¿_¿_ : (P : Type) → ⦃ P ⁇ ⦄ → Cmd → Cmd
        iff¿ P ¿ c = iff⦅ ¿ P ¿ ⦆ c

        infix 5 _≔_

        run : Cmd → (Map → Map)
        run (k ≔ v) = update (k , v)
        run [ f ← k ] = modify k f
        run (cmd₁ ∶ cmd₂) = run cmd₂ ∘ run cmd₁
        run (iff⦅ b ⦆ cmd) with b
        ... | yes _ = run cmd
        ... | no  _ = id
        run (just? k go) s with s ⁉ k
        ... | just v  = run (go v) s
        ... | nothing = s

        ≈-cong-cmd : ∀ {s₁ s₂} cmd → s₁ ≈ s₂ → run cmd s₁ ≈ run cmd s₂
        ≈-cong-cmd {s₁} {s₂} (cmd₁ ∶ cmd₂) s₁≈s₂ k = ≈-cong-cmd cmd₂ (≈-cong-cmd cmd₁ s₁≈s₂) k
        ≈-cong-cmd {s₁} {s₂} (_ ≔ _) s₁≈s₂ k = ≈-cong-update s₁≈s₂ k
        ≈-cong-cmd {s₁} {s₂} [ _ ← _ ] s₁≈s₂ k = ≈-cong-modify s₁≈s₂ k
        ≈-cong-cmd {s₁} {s₂} (iff⦅ b ⦆ cmd) s₁≈s₂ k
          with b
        ... | yes _ = ≈-cong-cmd cmd s₁≈s₂ k
        ... | no  _ = s₁≈s₂ k
        ≈-cong-cmd {s₁} {s₂} (just? k′ go) s₁≈s₂ k
          with s₁ ⁉ k′ | s₂ ⁉ k′ | s₁≈s₂ k′
        ... | nothing | .nothing  | refl = s₁≈s₂ k
        ... | just v  | .(just v) | refl = ≈-cong-cmd (go v) s₁≈s₂ k

        cmd-mon : ∀ cmd → KeyMonotonic (run cmd)
        cmd-mon (cmd₁ ∶ cmd₂) s k = cmd-mon cmd₂ (run cmd₁ s) k ∘ cmd-mon cmd₁ s k
        cmd-mon (iff⦅ b ⦆ cmd) with b
        ... | yes _ = cmd-mon cmd
        ... | no  _ = λ _ _ → id
        cmd-mon (just? k′ go) s with s ⁉ k′
        ... | just v  = cmd-mon (go v) s
        ... | nothing = λ _ → id
        cmd-mon [ _ ← _ ] = modify-mon
        cmd-mon (_ ≔ _) = update-mon

        module _ {s k v go} where
          just?-accept : s [ k ↦ v ] → run (just? k go) s ≈ run (go v) s
          just?-accept eq _ with s ⁉ k | eq
          ... | just v | refl = refl

          just?-reject : k ∉ᵈ s → run (just? k go) s ≈ s
          just?-reject k∉ _ with s ⁉ k | ⁉⇒∈ᵈ {s = s} {k = k}
          ... | just _  | p = ⊥-elim $ k∉ (p auto)
          ... | nothing | _ = refl

        module _ {s cmd} {P : Type} {b : Dec P} where
          iff-accept : True b → run (iff⦅ b ⦆ cmd) s ≈ run cmd s
          iff-accept _ _ with ⟫ yes _ ← ⟫ b = refl

          iff-reject : False b → run (iff⦅ b ⦆ cmd) s ≈ s
          iff-reject _ _ with ⟫ no _ ← ⟫ b = refl
