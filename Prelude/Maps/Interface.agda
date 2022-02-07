module Prelude.Maps.Interface where

open import Prelude.Init
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Applicative
open import Prelude.Semigroup
open import Prelude.Monoid

import Relation.Binary.Reasoning.Setoid as BinSetoid

record Mapᴵ (K V : Set) (σ : Level) : Set (lsuc σ) where
  constructor mkMapᴵ
  field
    Map : Set σ

    ∅ : Map
    _∪_ : Op₂ Map -- left-biased

    _⁉_ : Map → K → Maybe V
    _∈ᵈ_ : K → Map → Set

    _♯_ : Rel₀ Map -- T0D0: use Prelude.Apartness

  -- syntactic sugar
  syntax Map {K = K} {V = V} = Map⟨ K ↦ V ⟩

  -- operator precedence
  infix  5 _⁉_
  infixr 4 _∪_
  infix  3 _≈_ _∈ᵈ_ _∉ᵈ_

  _∉ᵈ_ : K → Map → Set
  k ∉ᵈ m = ¬ (k ∈ᵈ m)

  -- equivalence
  _≈_ : Rel₀ Map
  m ≈ m′ = ∀ k → m ⁉ k ≡ m′ ⁉ k

  ≈-refl : Reflexive _≈_
  ≈-refl _ = refl

  ≈-sym : Symmetric _≈_
  ≈-sym p k = sym (p k)

  ≈-trans : Transitive _≈_
  ≈-trans p q k = trans (p k) (q k)

  ≈-equiv : IsEquivalence _≈_
  ≈-equiv = record {refl = ≈-refl; sym = ≈-sym; trans = ≈-trans}

  ≈-setoid : Setoid σ 0ℓ
  ≈-setoid = record {Carrier = Map; _≈_ = _≈_; isEquivalence = ≈-equiv}

  module ≈-Reasoning = BinSetoid ≈-setoid

  -- derived relations
  ⟨_⊎_⟩≡_ : Map → Map → Map → Set
  ⟨ m ⊎ m′ ⟩≡ m″ = (m ♯ m′) × ((m ∪ m′) ≈ m″)

  _[_↦_] : Map → K → V → Set
  m [ k ↦ v ] = m ⁉ k ≡ just v

  _[_↦_]∅ : Map → K → V → Set
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

    -- ⊎≈-assocʳ : ∀ {s₁}{s₂₃}{s}{s₂}{s₃} → ⟨ s₁ ⊎ s₂₃ ⟩≡ s → ⟨ s₂ ⊎ s₃  ⟩≡ s₂₃ → ⟨ (s₁ ∪ s₂) ⊎ s₃ ⟩≡ s × (s₁ ♯ s₂)
    -- ⊎≈-assocˡ : ∀ {s₁₂}{s₃}{s}{s₁}{s₂} → ⟨ s₁₂ ⊎ s₃ ⟩≡ s → ⟨ s₁ ⊎ s₂  ⟩≡ s₁₂ → ⟨ s₁ ⊎ (s₂ ∪ s₃) ⟩≡ s × (s₂ ♯ s₃)

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

  infix 3 _⊆ᵈ_ _⊈ᵈ_
  _⊆ᵈ_ _⊈ᵈ_ : Rel₀ Map
  m ⊆ᵈ m′ = ∀ k → k ∈ᵈ m → k ∈ᵈ m′
  k ⊈ᵈ m = ¬ (k ⊆ᵈ m)

  private variable
    s s₁ s₂ s₃ s₁₂ s₂₃ : Map
    k : K
    v : V

  ≈-cong : ∀ {P : K → Maybe V → Set}
    → s₁ ≈ s₂
    → (∀ k → P k (s₁ ⁉ k))
    → (∀ k → P k (s₂ ⁉ k))
  ≈-cong {P = P} eq p k = subst (P k) (eq k) (p k)

  ∉ᵈ-∪⁻ : k ∉ᵈ (s₁ ∪ s₂) → (k ∉ᵈ s₁) × (k ∉ᵈ s₂)
  ∉ᵈ-∪⁻ {k}{s₁}{s₂} k∉ = (k∉ ∘ ∈ᵈ-∪⁺ k s₁ s₂ ∘ inj₁) , (k∉ ∘ ∈ᵈ-∪⁺ k s₁ s₂ ∘ inj₂)

  ∉ᵈ-∪⁺ : (k ∉ᵈ s₁) × (k ∉ᵈ s₂) → k ∉ᵈ (s₁ ∪ s₂)
  ∉ᵈ-∪⁺ {k}{s₁}{s₂} (k∉₁ , k∉₂) k∈ = case ∈ᵈ-∪⁻ k s₁ s₂ k∈ of λ where
    (inj₁ k∈₁) → k∉₁ k∈₁
    (inj₂ k∈₂) → k∉₂ k∈₂

  ∪≡-comm : Symmetric (⟨_⊎_⟩≡ s)
  ∪≡-comm (s₁♯s₂ , ≡s) = ♯-comm s₁♯s₂ , ≈-trans (≈-sym $ ∪-comm s₁♯s₂) ≡s

  ∪≡-cong : s₁ ≈ s₂ → ⟨ s₁ ⊎ s₃ ⟩≡ s → ⟨ s₂ ⊎ s₃ ⟩≡ s
  ∪≡-cong eq (s₁♯s₃ , ≡s) = ♯-cong eq s₁♯s₃ , ≈-trans (≈-sym (∪-cong eq)) ≡s

  ∪-assocˡ : (s₁ ∪ s₂) ∪ s₃ ≈ s₁ ∪ (s₂ ∪ s₃)
  ∪-assocˡ = ≈-sym ∪-assocʳ

  ⊎≈-assocʳ :
      ⟨ s₁ ⊎ s₂₃ ⟩≡ s
    → ⟨ s₂ ⊎ s₃  ⟩≡ s₂₃
      ---------------------
    → ⟨ (s₁ ∪ s₂) ⊎ s₃ ⟩≡ s
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
      ⟨ s₁₂ ⊎ s₃ ⟩≡ s
    → ⟨ s₁ ⊎ s₂  ⟩≡ s₁₂
      ---------------------
    → ⟨ s₁ ⊎ (s₂ ∪ s₃) ⟩≡ s
    × (s₂ ♯ s₃)
  ⊎≈-assocˡ {s₁₂}{s₃}{s}{s₁}{s₂} (s₁₂♯s₃ , ≡s) (s₁♯s₂ , ≡s₁₂) =
    ∪≡-assocˡ s₁♯s₂ ≡ss , proj₂ (♯-∪⁻ˡ {s₁ = s₁} s₁₂♯s₃′)
    where
      s₁₂♯s₃′ : (s₁ ∪ s₂) ♯ s₃
      s₁₂♯s₃′ = ♯-cong (≈-sym ≡s₁₂) s₁₂♯s₃

      ≡ss : ⟨ (s₁ ∪ s₂) ⊎ s₃ ⟩≡ s
      ≡ss = s₁₂♯s₃′ , ≈-trans (∪-cong ≡s₁₂) ≡s

record BuildMapᴵ (K V : Set) (σ : Level) ⦃ _ : Mapᴵ K V σ ⦄ : Set (lsuc σ) where
  open Mapᴵ it
  field
    buildMap : (K → Maybe V) → Map
    buildMap-sound : ∀ (f : K → Maybe V) → ∀ k → buildMap f ⁉ k ≡ f k

  module _ ⦃ _ : SemigroupLaws V _≡_ ⦄ ⦃ _ : MonoidLaws V _≡_ ⦄ where
    infix 5 _⁉ε_
    _⁉ε_ : Map → K → V
    m ⁉ε k = fromMaybe ε (m ⁉ k)

    instance
      Semigroup-Map : Semigroup Map
      Semigroup-Map ._◇_ m m′ = buildMap λ k → just $ (m ⁉ε k) ◇ (m′ ⁉ε k)

    open Alg (Rel₀ Map ∋ _≈_)

    private variable
      m m′ m₁ m₂ m₃ m₁₂ m₂₃ : Map
      k k′ : K
      v v′ : V

    ◇-⁉ : ∀ m m′ → (m ◇ m′) ⁉ k ≡ just ((m ⁉ε k) ◇ (m′ ⁉ε k))
    ◇-⁉  {k} m m′ = buildMap-sound (λ k → just $ (m ⁉ε k) ◇ (m′ ⁉ε k)) k

    ⟨_◇_⟩≡_ : 3Rel Map 0ℓ
    ⟨ m₁ ◇ m₂ ⟩≡ m = m₁ ◇ m₂ ≈ m

    -- instance
    --   CommutativeSemigroup-Map : CommutativeSemigroup Map _≈_
    --   CommutativeSemigroup-Map = record {◇-comm = λ m m′ k →
    --     let open ≡-Reasoning in
    private
      ◇ᵐ-comm : Commutative (_◇_ {A = Map})
      ◇ᵐ-comm m m′ k =
          begin
            (buildMap λ k → just $ (m ⁉ε k) ◇ (m′ ⁉ε k)) ⁉ k
          ≡⟨ buildMap-sound _ _ ⟩
            just ((m ⁉ε k) ◇ (m′ ⁉ε k))
          ≡⟨  cong just (◇-comm (m ⁉ε k) (m′ ⁉ε k)) ⟩
            just ((m′ ⁉ε k) ◇ (m ⁉ε k))
          ≡⟨ sym $ buildMap-sound _ _ ⟩
            (buildMap λ k → just $ (m′ ⁉ε k) ◇ (m ⁉ε k)) ⁉ k
          ∎ where open ≡-Reasoning
    -- instance
    --   CommutativeSemigroup-Map : CommutativeSemigroup Map _≈_
    --   CommutativeSemigroup-Map = record {◇-comm = ◇ᵐ-comm}

    ◇≡-comm : Symmetric (⟨_◇_⟩≡ m)
    ◇≡-comm ≈m = ≈-trans (◇ᵐ-comm _ _) ≈m

    ◇-cong : m₁ ≈ m₂ → (m₁ ◇ m₃) ≈ (m₂ ◇ m₃)
    ◇-cong {m₁}{m₂}{m₃} m₁≈m₂ k =
      begin
        (m₁ ◇ m₃) ⁉ k
      ≡⟨ buildMap-sound _ _ ⟩
        just ((m₁ ⁉ε k) ◇ (m₃ ⁉ε k))
      ≡⟨  cong (just ∘ (_◇ (m₃ ⁉ε k))) (cong (fromMaybe ε) (m₁≈m₂ k)) ⟩
        just ((m₂ ⁉ε k) ◇ (m₃ ⁉ε k))
      ≡⟨ sym $ buildMap-sound _ _ ⟩
        (m₂ ◇ m₃) ⁉ k
      ∎ where open ≡-Reasoning

    ◇-congʳ : m₂ ≈ m₃ → (m₁ ◇ m₂) ≈ (m₁ ◇ m₃)
    ◇-congʳ {m₂}{m₃}{m₁} m₂≈m₃ =
      begin m₁ ◇ m₂ ≈⟨ ◇ᵐ-comm _ _ ⟩
            m₂ ◇ m₁ ≈⟨ ◇-cong m₂≈m₃ ⟩
            m₃ ◇ m₁ ≈⟨ ◇ᵐ-comm _ _ ⟩
            m₁ ◇ m₃ ∎
      where open ≈-Reasoning

    private
      ◇ᵐ-assocʳ : Associative (_◇_ {A = Map})
      ◇ᵐ-assocʳ m₁ m₂ m₃ k =
        begin
          ((m₁ ◇ m₂) ◇ m₃) ⁉ k
        ≡⟨ ◇-⁉ _ _ ⟩
          just (((m₁ ◇ m₂) ⁉ε k) ◇ (m₃ ⁉ε k))
        ≡⟨ cong just go ⟩
          just ((m₁ ⁉ε k) ◇ ((m₂ ◇ m₃) ⁉ε k))
        ≡⟨ sym $ ◇-⁉ _ _ ⟩
          (m₁ ◇ m₂ ◇ m₃) ⁉ k
        ∎ where
          open ≡-Reasoning

          go : ((m₁ ◇ m₂) ⁉ε k) ◇ (m₃ ⁉ε k)
              ≡ (m₁ ⁉ε k) ◇ ((m₂ ◇ m₃) ⁉ε k)
          go
            rewrite ◇-⁉ {k} (m₁ ◇ m₂) m₃
                  | ◇-⁉ {k} m₁ m₂
                  | ◇-⁉ {k} m₁ (m₂ ◇ m₃)
                  | ◇-⁉ {k} m₂ m₃
            = ◇-assocʳ _ _ _
    instance
      AssociativeSemigroup-Map : SemigroupLaws Map _≈_
      AssociativeSemigroup-Map = record {◇-comm = ◇ᵐ-comm; ◇-assocʳ = ◇ᵐ-assocʳ}

    ◇≈-assocˡ :
        ⟨ m₁₂ ◇ m₃ ⟩≡ m
      → ⟨ m₁ ◇ m₂  ⟩≡ m₁₂
        ---------------------
      → ⟨ (m₁ ◇ m₂) ◇ m₃ ⟩≡ m
    ◇≈-assocˡ ≡m ≡m₁₂ = ≈-trans (◇-cong ≡m₁₂) ≡m

    ◇≈-assocʳ :
        ⟨ m₁ ◇ m₂₃ ⟩≡ m
      → ⟨ m₂ ◇ m₃  ⟩≡ m₂₃
        ---------------------
      → ⟨ (m₁ ◇ m₂) ◇ m₃ ⟩≡ m
    ◇≈-assocʳ ≡m ≡m₂₃ = ≈-trans (≈-trans (◇-assocʳ _ _ _) (◇-congʳ ≡m₂₃)) ≡m

record DecMapᴵ (K V : Set) (σ : Level) ⦃ _ : Mapᴵ K V σ ⦄ ⦃ _ : DecEq K ⦄ : Set (lsuc σ) where
  open Mapᴵ it
  field
    _∈ᵈ?_ : Decidable² _∈ᵈ_

    singleton : K × V → Map
    singleton-law : ∀ {k v} → singleton (k , v) [ k ↦ v ]∅
    singleton∈ : ∀ {A v k} → k ∈ᵈ singleton (A , v) → k ≡ A
    singleton♯ : ∀ {k v k′ v′} → k ≢ k′ → singleton (k , v) ♯ singleton (k′ , v′)
    singleton-collapse : ∀ {k v v′} → singleton (k , v) ∪ singleton (k , v′) ≈ singleton (k , v)

  update : K × V → Map → Map
  update entry = singleton entry ∪_

  KeyMonotonic : (Map → Map) → Set σ
  KeyMonotonic f = ∀ s → s ⊆ᵈ f s

  KeyPreserving : (Map → Map) → Set σ
  KeyPreserving f = ∀ s → f s ⊆ᵈ s

  update-mon : ∀ {k v} → KeyMonotonic (update (k , v))
  update-mon s _ = ∈ᵈ-∪⁺ʳ _ _ _

  singleton-law′ : ∀ {k v} → singleton (k , v) [ k ↦ v ]
  singleton-law′ {k}{v} = proj₁ $ singleton-law {k}{v}

  field
    ≡-cong-update : ∀ {k′ k : K} {v} {s₁ s₂ : Map}
      → s₁ ⁉ k′ ≡ s₂ ⁉ k′ → update (k , v) s₁ ⁉ k′ ≡ update (k , v) s₂ ⁉ k′
    ♯-cong-pre : ∀ {s₁ s₂ : Map} {f : Map → Map} → KeyPreserving f → s₁ ♯ s₂ → f s₁ ♯ s₂

  ≈-cong-update : ∀ {k v s₁ s₂} → s₁ ≈ s₂ → update (k , v) s₁ ≈ update (k , v) s₂
  ≈-cong-update {k = k} s₁≈s₂ = ≡-cong-update ∘ s₁≈s₂

  infix 3 _∈ᵈ?_ _∉ᵈ?_
  _∉ᵈ?_ : Decidable² _∉ᵈ_
  k ∉ᵈ? m = ¬? (k ∈ᵈ? m)

  instance
    Dec-∈ᵈ : ∀ {k : K} {m : Map} → (k ∈ᵈ m) ⁇
    Dec-∈ᵈ .dec = _∈ᵈ?_ _ _

  singleton≈ : ∀ {m : Map} {k v} → m [ k ↦ v ]∅ → m ≈ singleton (k , v)
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

  update-update : ∀ {k v v′} {s : Map} → update (k , v′) (update (k , v) s) ≈ update (k , v′) s
  update-update {k}{v}{v′}{s} =
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

  singleton-accept : ∀ {k v} {s : Map} → (singleton (k , v) ∪ s) ⁉ k ≡ just v
  singleton-accept {k}{v}{s} rewrite ↦-∪⁺ˡ {s₂ = s}{k}{v} singleton-law′ = refl

  singleton-reject : ∀ {k k′ v} {s : Map} → k′ ≢ k → (singleton (k , v) ∪ s) ⁉ k′ ≡ s ⁉ k′
  singleton-reject {k}{k′}{v}{s} k≢
    with ¿ k′ ∈ᵈ singleton (k , v) ¿
  ... | yes k∈ = ⊥-elim $ k≢ (singleton∈ k∈)
  ... | no k∉ rewrite ↦-∪⁺ʳ {s₂ = s} k∉ = refl

  data Cmd : Set₁ where
    _∶_ : Cmd → Cmd → Cmd
    _≔_ : K → V → Cmd
    iff⦅_⦆_ : ∀ {P : Set} → Dec P → Cmd → Cmd
    just? : K → (V → Cmd) → Cmd

  infix 4 _≔_

  iff¿_¿_ : (P : Set) → ⦃ P ⁇ ⦄ → Cmd → Cmd
  iff¿ P ¿ c = iff⦅ ¿ P ¿ ⦆ c

  run : Cmd → (Map → Map)
  run (k ≔ v) = update (k , v)
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
  cmd-mon (k′ ≔ v) = update-mon
  cmd-mon (iff⦅ b ⦆ cmd) with b
  ... | yes _ = cmd-mon cmd
  ... | no  _ = λ _ _ → id
  cmd-mon (just? k′ go) s with s ⁉ k′
  ... | just v  = cmd-mon (go v) s
  ... | nothing = λ _ → id

  just?-accept : ∀ {s k v go}
    → s [ k ↦ v ]
    → run (just? k go) s ≈ run (go v) s
  just?-accept {s}{k}{v} eq _ with s ⁉ k | eq
  ... | just v | refl = refl

  just?-reject : ∀ {s : Map} {k} {v : V} {go}
    → k ∉ᵈ s
    → run (just? k go) s ≈ s
  just?-reject {s}{k}{v} k∉ _ with s ⁉ k | ⁉⇒∈ᵈ {s = s} {k = k}
  ... | just _  | p = ⊥-elim $ k∉ (p auto)
  ... | nothing | _ = refl

  iff-accept : ∀ {s cmd} {P : Set} {b : Dec P}
    → True b
    → run (iff⦅ b ⦆ cmd) s ≈ run cmd s
  iff-accept {b = b} ≡yes _ with b | ≡yes
  ... | yes _ | _ = refl

record DecEqMapᴵ (K V : Set) (σ : Level) ⦃ _ : Mapᴵ K V σ ⦄ ⦃ _ : DecEq K ⦄ : Set (lsuc σ) where
  open Mapᴵ it
  field deceq : DecEq Map
  instance DecEq-Map = deceq
