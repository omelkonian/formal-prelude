------------------------------------------------------------------------
-- Maps as (partial) functions to Maybe.
--   * Membership using Is-just (_∉_ as negation)
--   * Disjointness with (¬_ × ¬_)
------------------------------------------------------------------------
{-# OPTIONS --allow-unsolved-metas #-}
open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Listable
open import Prelude.Functor

module Prelude.AsPartialFunctions3 {K V : Set} where

Map : Set
Map = K → Maybe V
syntax Map {K} {V} = Map⟨ K ↦ V ⟩

private
  variable
    s s₁ s₂ s₃ s₁₂ s₁₃ s₂₃ : Map
    k : K
    v : V

∅′ : Map
∅′ = const nothing

infix 3 _∈ᵈ_ _∉ᵈ_
_∈ᵈ_ : K → Map → Set
k ∈ᵈ m = Is-just (m k)

_∉ᵈ_ : K → Map → Set
k ∉ᵈ m = ¬ (k ∈ᵈ m)

_⊆ᵈ_ : Rel₀ Map
m ⊆ᵈ m′ = ∀ k → k ∈ᵈ m → k ∈ᵈ m′

_⊈ᵈ_ : Rel₀ Map
m ⊈ᵈ m′ = ¬ m ⊆ᵈ m′

_[_↦_] : Map → K → V → Set
m [ k ↦ v ] = m k ≡ just v

-- Equivalence

_≈_ : Rel₀ Map
m ≈ m′ = ∀ k → m k ≡ m′ k

≈-refl : s ≈ s
≈-refl _ = refl

≈-trans : s₁ ≈ s₂ → s₂ ≈ s₃ → s₁ ≈ s₃
≈-trans p q k = trans (p k) (q k)

≈-sym : s₁ ≈ s₂ → s₂ ≈ s₁
≈-sym p k = sym (p k)

≈-cong : ∀ {P : K → Maybe V → Set}
  → s₁ ≈ s₂
  → (∀ k → P k (s₁ k))
  → (∀ k → P k (s₂ k))
≈-cong {P = P} eq p k = subst (P k) (eq k) (p k)

-- Separation

_♯_ : Rel₀ Map
m ♯ m′ = ∀ k → (k ∈ᵈ m → k ∉ᵈ m′) × (k ∈ᵈ m′ → k ∉ᵈ m)

♯-comm : Symmetric _♯_
♯-comm s₁♯s₂ = swap ∘ s₁♯s₂

♯-cong : s₁ ≈ s₂ → s₁ ♯ s₃ → s₂ ♯ s₃
♯-cong eq s₁♯s₃ k
  with p ← s₁♯s₃ k
  rewrite eq k = p

infixr 4 _∪_
_∪_ : Op₂ Map
(m ∪ m′) k with m k
... | nothing = m′ k
... | just v  = just v

∪-comm : s₁ ♯ s₂ → (s₁ ∪ s₂) ≈ (s₂ ∪ s₁)
∪-comm {s₁}{s₂} s₁♯s₂ k
  with s₁ k | inspect s₁ k | s₂ k | inspect s₂ k | proj₁ (s₁♯s₂ k)
... | nothing | ≡[ s₁≡ ] | nothing  | ≡[ s₂≡ ] | _ = trans s₂≡ (sym s₁≡)
... | nothing | ≡[ _   ] | just y   | ≡[ s₂≡ ] | _ = s₂≡
... | just x  | ≡[ s₁≡ ] | nothing  | ≡[ _   ] | _ = sym s₁≡
... | just x  | ≡[ _   ] | just y   | ≡[ _   ] | p = ⊥-elim (p auto auto)

∪-cong : s₁ ≈ s₂ → (s₁ ∪ s₃) ≈ (s₂ ∪ s₃)
∪-cong {s₁}{s₂}{s₃} eq k
  with s₁ k | s₂ k | eq k
... | nothing | .nothing  | refl = refl
... | just x  | .(just x) | refl = refl

⟨_⊎_⟩≡_ : Map → Map → Map → Set
⟨ m ⊎ m′ ⟩≡ m″ = (m ♯ m′) × ((m ∪ m′) ≈ m″)

∪≡-comm : Symmetric (⟨_⊎_⟩≡ s)
∪≡-comm (s₁♯s₂ , ≡s) = ♯-comm s₁♯s₂ , ≈-trans (≈-sym $ ∪-comm s₁♯s₂) ≡s

∪≡-cong : s₁ ≈ s₂ → ⟨ s₁ ⊎ s₃ ⟩≡ s → ⟨ s₂ ⊎ s₃ ⟩≡ s
∪≡-cong eq (s₁♯s₃ , ≡s) = ♯-cong eq s₁♯s₃ , ≈-trans (≈-sym (∪-cong eq)) ≡s

-- Lemmas

∈ᵈ-∪⁻ : k ∈ᵈ (s₁ ∪ s₂) → (k ∈ᵈ s₁) ⊎ (k ∈ᵈ s₂)
∈ᵈ-∪⁻ {k}{s₁}{s₂} k∈
  with s₁ k
... | just _  = inj₁ auto
... | nothing
  with s₂ k | k∈
... | just _  | _ = inj₂ auto

∈ᵈ-∪⁺ : (k ∈ᵈ s₁) ⊎ (k ∈ᵈ s₂) → k ∈ᵈ (s₁ ∪ s₂)
∈ᵈ-∪⁺ {k}{s₁}{s₂} (inj₁ _)
  with just _ ← s₁ k = auto
∈ᵈ-∪⁺ {k}{s₁}{s₂} (inj₂ k∈)
  with s₁ k
... | just _  = auto
... | nothing = k∈

∉ᵈ-∪⁻ : k ∉ᵈ (s₁ ∪ s₂) → (k ∉ᵈ s₁) × (k ∉ᵈ s₂)
∉ᵈ-∪⁻ {k}{s₁}{s₂} k∉ = (k∉ ∘ ∈ᵈ-∪⁺ {k}{s₁}{s₂} ∘ inj₁) , (k∉ ∘ ∈ᵈ-∪⁺ {k}{s₁}{s₂} ∘ inj₂)

∉ᵈ-∪⁺ : (k ∉ᵈ s₁) × (k ∉ᵈ s₂) → k ∉ᵈ (s₁ ∪ s₂)
∉ᵈ-∪⁺ {k}{s₁}{s₂} (k∉₁ , k∉₂) k∈ = case ∈ᵈ-∪⁻ {k}{s₁}{s₂} k∈ of λ where
  (inj₁ k∈₁) → k∉₁ k∈₁
  (inj₂ k∈₂) → k∉₂ k∈₂

♯-∪⁻ʳ : s₁ ♯ (s₂ ∪ s₃) → (s₁ ♯ s₂) × (s₁ ♯ s₃)
♯-∪⁻ʳ {s₁}{s₂}{s₃} s₁♯s₂₃ = s₁♯s₂ , s₁♯s₃
  where
    s₁♯s₂ : s₁ ♯ s₂
    s₁♯s₂ k = proj₁ ∘ ∉ᵈ-∪⁻ {k}{s₂}{s₃} ∘ proj₁ (s₁♯s₂₃ k)
            , proj₂ (s₁♯s₂₃ k) ∘ ∈ᵈ-∪⁺ {k}{s₂}{s₃} ∘ inj₁

    s₁♯s₃ : s₁ ♯ s₃
    s₁♯s₃ k = proj₂ ∘ ∉ᵈ-∪⁻ {k}{s₂}{s₃} ∘ proj₁ (s₁♯s₂₃ k)
            , proj₂ (s₁♯s₂₃ k) ∘ ∈ᵈ-∪⁺ {k}{s₂}{s₃} ∘ inj₂

♯-∪⁻ˡ : (s₁ ∪ s₂) ♯ s₃ → (s₁ ♯ s₃) × (s₂ ♯ s₃)
♯-∪⁻ˡ p = let l , r = ♯-∪⁻ʳ (♯-comm p)
          in  ♯-comm l , ♯-comm r

♯-∪⁺ˡ : (s₁ ♯ s₃) × (s₂ ♯ s₃) → (s₁ ∪ s₂) ♯ s₃
♯-∪⁺ˡ {s₁}{s₃}{s₂} (s₁♯s₃ , s₂♯s₃) k = f , g
  where
    f : k ∈ᵈ s₁ ∪ s₂ → k ∉ᵈ s₃
    f k∈ with ∈ᵈ-∪⁻ {k}{s₁}{s₂} k∈
    ... | inj₁ k∈₁ = proj₁ (s₁♯s₃ k) k∈₁
    ... | inj₂ k∈₂ = proj₁ (s₂♯s₃ k) k∈₂

    g : k ∈ᵈ s₃ → k ∉ᵈ s₁ ∪ s₂
    g k∈ = ∉ᵈ-∪⁺ {k}{s₁}{s₂} (proj₂ (s₁♯s₃ k) k∈ , proj₂ (s₂♯s₃ k) k∈)

♯-∪⁺ʳ : (s₁ ♯ s₂) × (s₁ ♯ s₃) → s₁ ♯ (s₂ ∪ s₃)
♯-∪⁺ʳ {s₁}{s₂}{s₃} (s₁♯s₂ , s₁♯s₃) k = f , g
  where
    f : k ∈ᵈ s₁ → k ∉ᵈ s₂ ∪ s₃
    f k∈ = ∉ᵈ-∪⁺ {k}{s₂}{s₃} (proj₁ (s₁♯s₂ k) k∈ , proj₁ (s₁♯s₃ k) k∈)

    g : k ∈ᵈ s₂ ∪ s₃ → k ∉ᵈ s₁
    g k∈ with ∈ᵈ-∪⁻ {k}{s₂}{s₃} k∈
    ... | inj₁ k∈₂ = proj₂ (s₁♯s₂ k) k∈₂
    ... | inj₂ k∈₃ = proj₂ (s₁♯s₃ k) k∈₃

∪≡-assocʳ : s₂ ♯ s₃ → ⟨ s₁ ⊎ (s₂ ∪ s₃) ⟩≡ s → ⟨ (s₁ ∪ s₂) ⊎ s₃ ⟩≡ s
∪≡-assocʳ {s₂}{s₃}{s₁}{s} s₂♯s₃ (s₁♯s₂₃ , ≡s) = s₁₂♯s₃ , ≡s′
  where
    s₁₂♯s₃ : (s₁ ∪ s₂) ♯ s₃
    s₁₂♯s₃ = ♯-∪⁺ˡ (proj₂ (♯-∪⁻ʳ {s₂ = s₂} s₁♯s₂₃) , s₂♯s₃)

    p : (s₁ ∪ (s₂ ∪ s₃)) ≈ ((s₁ ∪ s₂) ∪ s₃)
    p k with s₁ k | s₂ k  | s₃ k
    ... | just _  | _       | _       = refl
    ... | nothing | nothing | nothing = refl
    ... | nothing | just _  | _       = refl
    ... | nothing | nothing | just _  = refl

    ≡s′ : ((s₁ ∪ s₂) ∪ s₃) ≈ s
    ≡s′ = ≈-trans (≈-sym p) ≡s

∪≡-assocˡ : s₁ ♯ s₂ → ⟨ (s₁ ∪ s₂) ⊎ s₃ ⟩≡ s → ⟨ s₁ ⊎ (s₂ ∪ s₃)  ⟩≡ s
∪≡-assocˡ {s₁}{s₂}{s₃}{s} s₁♯s₂ p@(s₁₂♯s₃ , _) =
    ∪≡-comm ∘ ∪≡-assocʳ (♯-comm $ proj₁ $ ♯-∪⁻ˡ s₁₂♯s₃)
  $ ∪≡-comm ∘ ∪≡-assocʳ s₁♯s₂
  $ ∪≡-comm p

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
