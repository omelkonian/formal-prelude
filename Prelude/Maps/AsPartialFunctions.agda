------------------------------------------------------------------------
-- Maps as (partial) functions to Maybe.
--   * Membership using Is-just (_∉_ as negation)
--   * Disjointness with ¬ (_×_)
------------------------------------------------------------------------
open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Functor
open import Prelude.Applicative
open import Prelude.Apartness
open import Prelude.Setoid

module Prelude.Maps.AsPartialFunctions {K V : Type} where

Map : Type
Map = K → Maybe V

syntax Map {K = K} {V = V} = Map⟨ K ↦ V ⟩

private variable
  s s₁ s₂ s₃ s₁₂ s₁₃ s₂₃ : Map
  k : K
  v : V

∅ : Map
∅ = const nothing

infix  6 _⁉_
infixr 5 _∪_
infix  4 _∈ᵈ_ _∉ᵈ_ _♯ᵐ_ _≈ᵐ_

_∪_ : Op₂ Map
(m ∪ m′) k = m k <|> m′ k

_⁉_ : Map → K → Maybe V
m ⁉ k = m k

_∈ᵈ_ _∉ᵈ_ : K → Map → Type
k ∈ᵈ m = Is-just (m k)
k ∉ᵈ m = ¬ k ∈ᵈ m

open Derive-⊆-from-∈ _∈ᵈ_ public renaming
  ( _⊆_ to _⊆ᵈ_; _⊈_ to _⊈ᵈ_; ⊆-trans to ⊆ᵈ-trans
  ; _⊇_ to _⊇ᵈ_; _⊉_ to _⊉ᵈ_; ⊇-trans to ⊇ᵈ-trans
  )

instance
  Apart-Map : Map // Map
  Apart-Map ._♯_ m m′ = ∀ k → ¬ ((k ∈ᵈ m) × (k ∈ᵈ m′))

  Setoid-Map : ISetoid Map
  Setoid-Map = λ where
    .relℓ → _
    ._≈_ m m′ → ∀ k → m ⁉ k ≡ m′ ⁉ k

  SetoidLaws-Map : SetoidLaws Map
  SetoidLaws-Map .isEquivalence = record
    { refl = λ _ → refl
    ; sym = λ p k → sym (p k)
    ; trans = λ p q k → trans (p k) (q k)
    }

_♯ᵐ_ = Rel₀ Map ∋ _♯_

_≈ᵐ_ = Rel₀ Map ∋ _≈_
module ≈ᵐ-Reasoning = ≈-Reasoning {A = Map}
open Alg _≈ᵐ_

⟨_⊎_⟩≡_ : Map → Map → Map → Type
⟨ m ⊎ m′ ⟩≡ m″ = (m ♯ m′) × ((m ∪ m′) ≈ m″)

_[_↦_] : Map → K → V → Type
m [ k ↦ v ] = m ⁉ k ≡ just v

_[_↦_]∅ : Map → K → V → Type
m [ k ↦ v ]∅ = m [ k ↦ v ] × ∀ k′ → k′ ≢ k → k′ ∉ᵈ m

⁉⇒∈ᵈ : ∀ s {k} → Is-just (s ⁉ k) → k ∈ᵈ s
⁉⇒∈ᵈ s {k} p with s ⁉ k | p
... | just _  | _ = auto

∈ᵈ⇒⁉ : ∀ s {k} → k ∈ᵈ s → Is-just (s ⁉ k)
∈ᵈ⇒⁉ s {k} k∈ with s ⁉ k | k∈
... | just _ | _ = auto

↦-∪⁺ˡ : ∀ s₁ s₂ {k v} → s₁ [ k ↦ v ] → (s₁ ∪ s₂) [ k ↦ v ]
↦-∪⁺ˡ s₁ _ {k} p with s₁ ⁉ k | p
... | just _ | refl = refl

↦-∪⁺ʳ : ∀ s₁ s₂ {k} → k ∉ᵈ s₁ → s₂ ⁉ k ≡ (s₁ ∪ s₂) ⁉ k
↦-∪⁺ʳ s₁ s₂ {k} k∉ with s₁ ⁉ k | k∉
... | just _  | k∉′ = ⊥-elim $ k∉′ auto
... | nothing | _ = refl

-- commutativity
♯-comm : Symmetric _♯ᵐ_
♯-comm s₁♯s₂ k = s₁♯s₂ k ∘ Product.swap

∪-comm : ∀ s₁ s₂ → s₁ ♯ s₂ → (s₁ ∪ s₂) ≈ (s₂ ∪ s₁)
∪-comm s₁ s₂ s₁♯s₂ k
    with s₁ k | s₂ k | s₁♯s₂ k
... | nothing | nothing  | _ = refl
... | nothing | just _   | _ = refl
... | just _  | nothing  | _ = refl
... | just _  | just _   | p = ⊥-elim $ p (auto , auto)

-- congruences
♯-cong : ∀ (s₁ s₂ s₃ : Map) → s₁ ≈ s₂ → s₁ ♯ s₃ → s₂ ♯ s₃
♯-cong _ _ _ eq s₁♯s₃ k
  with p ← s₁♯s₃ k
  rewrite eq k = p

∪-cong : ∀ s₁ s₂ s₃ → s₁ ≈ s₂ → (s₁ ∪ s₃) ≈ (s₂ ∪ s₃)
∪-cong s₁ s₂ s₃ eq k
  with s₁ k | s₂ k | eq k
... | nothing | .nothing  | refl = refl
... | just x  | .(just x) | refl = refl

∈ᵈ-cong : ∀ k s₁ s₂ → s₁ ≈ s₂ → k ∈ᵈ s₁ → k ∈ᵈ s₂
∈ᵈ-cong k s₁ s₂ s₁≈s₂ k∈ = subst Is-just (s₁≈s₂ k) k∈

-- introduction/elimination of union
∈ᵈ-∪⁻ : ∀ k s₁ s₂ → k ∈ᵈ (s₁ ∪ s₂) → (k ∈ᵈ s₁) ⊎ (k ∈ᵈ s₂)
∈ᵈ-∪⁻ k s₁ s₂ k∈
  with s₁ k
... | just _  = inj₁ auto
... | nothing
  with s₂ k | k∈
... | just _  | _ = inj₂ auto

∈ᵈ-∪⁺ : ∀ k s₁ s₂ → (k ∈ᵈ s₁) ⊎ (k ∈ᵈ s₂) → k ∈ᵈ (s₁ ∪ s₂)
∈ᵈ-∪⁺ k s₁ s₂ (inj₁ _)
  with just _ ← s₁ k = auto
∈ᵈ-∪⁺ k s₁ s₂ (inj₂ k∈)
  with s₁ k
... | just _  = auto
... | nothing = k∈

∪-chooseₗ : ∀ s₁ s₂ → s₁ ♯ s₂ → (∀ {k} → k ∉ᵈ s₂ → (s₁ ∪ s₂) ⁉ k ≡ s₁ ⁉ k)
∪-chooseₗ s₁ s₂ _ {k} k∉ with s₁ k
... | just _ = refl
... | nothing with s₂ k | k∉
... | just _  | p = ⊥-elim $ p auto
... | nothing | _ = refl

∪-chooseᵣ : ∀ s₁ s₂ → s₁ ♯ s₂ → (∀ {k} → k ∈ᵈ s₂ → (s₁ ∪ s₂) ⁉ k ≡ s₂ ⁉ k)
∪-chooseᵣ s₁ s₂ p {k} k∈ with s₁ k | p k
... | nothing | _  = refl
... | just _  | pk = ⊥-elim $ pk (auto , k∈)

♯-∪⁻ʳ : ∀ (s₁ s₂ s₃ : Map) → s₁ ♯ (s₂ ∪ s₃) → (s₁ ♯ s₂) × (s₁ ♯ s₃)
♯-∪⁻ʳ s₁ s₂ s₃ s₁♯s₂₃ = s₁♯s₂ , s₁♯s₃
  where
    s₁♯s₂ : s₁ ♯ s₂
    s₁♯s₂ k (k∈₁ , k∈₂) = s₁♯s₂₃ k (k∈₁ , ∈ᵈ-∪⁺ k s₂ s₃ (inj₁ k∈₂))

    s₁♯s₃ : s₁ ♯ s₃
    s₁♯s₃ k (k∈₁ , k∈₃) = s₁♯s₂₃ k (k∈₁ , ∈ᵈ-∪⁺ k s₂ s₃ (inj₂ k∈₃))

♯-∪⁻ˡ : ∀ (s₁ s₂ s₃ : Map) → (s₁ ∪ s₂) ♯ s₃ → (s₁ ♯ s₃) × (s₂ ♯ s₃)
♯-∪⁻ˡ _ _ _ p = let l , r = ♯-∪⁻ʳ _ _ _ (♯-comm p)
                in  ♯-comm l , ♯-comm r

♯-∪⁺ˡ : ∀ (s₁ s₂ s₃ : Map) → (s₁ ♯ s₃) × (s₂ ♯ s₃) → (s₁ ∪ s₂) ♯ s₃
♯-∪⁺ˡ s₁ s₂ s₃ (s₁♯s₃ , s₂♯s₃) k (k∈₁₂ , k∈₃)
  with ∈ᵈ-∪⁻ k s₁ s₂ k∈₁₂
... | inj₁ k∈₁ = s₁♯s₃ k (k∈₁ , k∈₃)
... | inj₂ k∈₂ = s₂♯s₃ k (k∈₂ , k∈₃)

♯-∪⁺ʳ : ∀ (s₁ s₂ s₃ : Map) → (s₁ ♯ s₂) × (s₁ ♯ s₃) → s₁ ♯ (s₂ ∪ s₃)
♯-∪⁺ʳ s₁ s₂ s₃ (s₁♯s₂ , s₁♯s₃) k (k∈₁ , k∈₂₃)
  with ∈ᵈ-∪⁻ k s₂ s₃ k∈₂₃
... | inj₁ k∈₂ = s₁♯s₂ k (k∈₁ , k∈₂)
... | inj₂ k∈₃ = s₁♯s₃ k (k∈₁ , k∈₃)

-- associativity
∪-assocʳ : ∀ s₁ s₂ s₃ → s₁ ∪ (s₂ ∪ s₃) ≈ (s₁ ∪ s₂) ∪ s₃
∪-assocʳ s₁ s₂ s₃ k with s₁ ⁉ k
... | just _  = refl
... | nothing = refl

∪≡-assocʳ : ∀ s₁ s₂ s₃ s → s₂ ♯ s₃ → ⟨ s₁ ⊎ (s₂ ∪ s₃) ⟩≡ s → ⟨ (s₁ ∪ s₂) ⊎ s₃ ⟩≡ s
∪≡-assocʳ s₁ s₂ s₃ s s₂♯s₃ (s₁♯s₂₃ , ≡s) = s₁₂♯s₃ , ≡s′
  where
    s₁₂♯s₃ : (s₁ ∪ s₂) ♯ s₃
    s₁₂♯s₃ = ♯-∪⁺ˡ _ _ _ (proj₂ (♯-∪⁻ʳ _ s₂ _ s₁♯s₂₃) , s₂♯s₃)

    p : (s₁ ∪ (s₂ ∪ s₃)) ≈ ((s₁ ∪ s₂) ∪ s₃)
    p k with s₁ k | s₂ k  | s₃ k
    ... | just _  | _       | _       = refl
    ... | nothing | nothing | nothing = refl
    ... | nothing | just _  | _       = refl
    ... | nothing | nothing | just _  = refl

    ≡s′ : ((s₁ ∪ s₂) ∪ s₃) ≈ s
    ≡s′ = ≈-trans (≈-sym p) ≡s

_∈ᵈ?_ : Decidable² _∈ᵈ_
k ∈ᵈ? m with m k
... | just _  = yes auto
... | nothing = no  auto

module _ ⦃ _ : DecEq K ⦄ where
  singleton : K × V → Map
  singleton (k , v) k′ = if k′ == k then just v else nothing

  singleton-law : ∀ {k v} → singleton (k , v) [ k ↦ v ]∅
  singleton-law {k}{v} = p₁ , p₂
    where
      p₁ : singleton (k , v) [ k ↦ v ]
      p₁ rewrite ≟-refl k = refl

      p₂ : ∀ k′ → k′ ≢ k → k′ ∉ᵈ singleton (k , v)
      p₂ k′ k′≢ with k′ ≟ k
      ... | yes refl = ⊥-elim $ k′≢ refl
      ... | no  _    = λ ()

  singleton∈ : ∀ {A v k} → k ∈ᵈ singleton (A , v) → k ≡ A
  singleton∈ {A}{v}{k} k∈ with k ≟ A | k∈
  ... | yes k≡A | _ = k≡A

  singleton♯ : ∀ {k v k′ v′} → k ≢ k′ → singleton (k , v) ♯ singleton (k′ , v′)
  singleton♯ {k}{v}{k′}{v′} k≢ _ (k∈₁ , k∈₂) = k≢ (trans (sym $ singleton∈ k∈₁) (singleton∈ k∈₂))

  singleton-collapse : ∀ {k v v′} → singleton (k , v) ∪ singleton (k , v′) ≈ singleton (k , v)
  singleton-collapse {k}{v}{v′} k′
    with k′ ≟ k
  ... | yes refl = refl
  ... | no  ≢k
    with k′ ≟ k
  ... | yes ≡k = ⊥-elim (≢k ≡k)
  ... | no  _ = refl

  {- COPIED from Maps.Interface.DecMapᴵ -}
  update : K × V → Map → Map
  update entry = singleton entry ∪_

  KeyPreserving : (Map → Map) → Type
  KeyPreserving f = ∀ s → f s ⊆ᵈ s
  {--------------------------------------}

  ≡-cong-update : ∀ s₁ s₂ {k k′ v}
    → s₁ ⁉ k′ ≡ s₂ ⁉ k′
    → update (k , v) s₁ ⁉ k′ ≡ update (k , v) s₂ ⁉ k′
  ≡-cong-update _ _ {k}{k′} s₁≡s₂ with k′ ≟ k
  ... | yes _ = refl
  ... | no  _ = s₁≡s₂

  ♯-cong-pre : ∀ (f : Map → Map) (s₁ s₂ : Map)
    → KeyPreserving f
    → s₁ ♯ s₂
    → f s₁ ♯ s₂
  ♯-cong-pre f s₁ s₂ pre s₁♯s₂ _ (k∈₁ , k∈₂) = s₁♯s₂ _ (pre _ k∈₁ , k∈₂)

{-
    ≈-cong-⟦⟧ : ∀ {}
      → s₁ ≈ s₂
      → ⟦ t ⟧ s₁ ≈ ⟦ t ⟧ s₂

    help :
        s₁ [ A ↦ v  ]∅
      → s₂ [ B ↦ v′ ]∅
      -- f ∼ ⟦ A —→⟨ v ⟩ B ⟧ ~ update (A , 0) ∘ update (B , v′ + v)
      → (s₁′ ∪ s₂′) ≈ f (s₁ ∪ s₂)
-}

buildMap : (K → Maybe V) → Map
buildMap = id

buildMap-sound : ∀ (f : K → Maybe V) → ∀ k → buildMap f ⁉ k ≡ f k
buildMap-sound _ _ = refl
