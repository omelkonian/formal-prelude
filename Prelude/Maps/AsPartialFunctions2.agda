------------------------------------------------------------------------
-- Maps as (partial) functions to Maybe.
--   * Membership using propositional equality
------------------------------------------------------------------------
{-# OPTIONS --allow-unsolved-metas #-}
open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Listable
open import Prelude.Functor

module Prelude.AsPartialFunctions2 {K V : Set} where

Map : Set
Map = K → Maybe V
syntax Map {K} {V} = Map⟨ K ↦ V ⟩

private
  variable
    s s₁ s₂ s₃ : Map
    k : K
    v : V

∅′ : Map
∅′ = const nothing

_∈ᵈ_ : K → Map → Set
k ∈ᵈ m = ∃[ x ] (m k ≡ just x)

_∉ᵈ_ : K → Map → Set
k ∉ᵈ m = m k ≡ nothing

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

♯-comm : s₁ ♯ s₂ → s₂ ♯ s₁
♯-comm s₁♯s₂ = swap ∘ s₁♯s₂

♯-cong : s₁ ≈ s₂ → s₁ ♯ s₃ → s₂ ♯ s₃
♯-cong eq s₁♯s₃ k
  with p ← s₁♯s₃ k
  rewrite eq k = p

_∪_∶-_ : ∀ m m′ → m ♯ m′ → Map
(m ∪ m′ ∶- m♯m′) k
  with m k
... | nothing = m′ k
... | just v  = just v

∪-comm : (p : s₁ ♯ s₂) → (s₁ ∪ s₂ ∶- p) ≈ (s₂ ∪ s₁ ∶- ♯-comm p)
∪-comm {s₁}{s₂} s₁♯s₂ k
  with s₁ k | inspect s₁ k | s₂ k | inspect s₂ k | proj₁ (s₁♯s₂ k)
... | nothing | ≡[ s₁≡ ] | nothing  | ≡[ s₂≡ ] | _ = trans s₂≡ (sym s₁≡)
... | nothing | ≡[ _   ] | just y   | ≡[ s₂≡ ] | _ = s₂≡
... | just x  | ≡[ s₁≡ ] | nothing  | ≡[ _   ] | _ = sym s₁≡
... | just x  | ≡[ _   ] | just y   | ≡[ _   ] | p = case p (-, refl) of λ ()

∪-cong : (p : s₁ ♯ s₃) (eq : s₁ ≈ s₂) → (s₁ ∪ s₃ ∶- p) ≈ (s₂ ∪ s₃ ∶- ♯-cong eq p)
∪-cong {s₁}{s₃}{s₂} s₁♯s₃ eq k
  with s₁ k | s₂ k | eq k
... | nothing | .nothing  | refl = refl
... | just x  | .(just x) | refl = refl

_∪_≡_ : Map → Map → Map → Set
m ∪ m′ ≡ m″ = Σ[ p ∈ m ♯ m′ ] ((m ∪ m′ ∶- p) ≈ m″)

∪≡-comm : s₁ ∪ s₂ ≡ s → s₂ ∪ s₁ ≡ s
∪≡-comm (s₁♯s₂ , ≡s) = ♯-comm s₁♯s₂ , ≈-trans (≈-sym $ ∪-comm s₁♯s₂) ≡s

∪≡-cong : s₁ ≈ s₂ → s₁ ∪ s₃ ≡ s → s₂ ∪ s₃ ≡ s
∪≡-cong eq (s₁♯s₃ , ≡s) = ♯-cong eq s₁♯s₃ , ≈-trans (≈-sym (∪-cong s₁♯s₃ eq)) ≡s

-- Lemmas

∈ᵈ-∪⁻ :
    (p : s₁ ♯ s₂)
  → k ∈ᵈ (s₁ ∪ s₂ ∶- p)
  → (k ∈ᵈ s₁) ⊎ (k ∈ᵈ s₂)
∈ᵈ-∪⁻ {s₁}{s₂}{k} s₁♯s₂ k∈
  with s₁ k
... | just _  = inj₁ (-, refl)
... | nothing
  with s₂ k | k∈
... | just _  | _ = inj₂ (-, refl)

∈ᵈ-∪⁺ :
    (p : s₁ ♯ s₂)
  → (k ∈ᵈ s₁) ⊎ (k ∈ᵈ s₂)
  → k ∈ᵈ (s₁ ∪ s₂ ∶- p)
∈ᵈ-∪⁺ {s₁}{s₂}{k} s₁♯s₂ (inj₁ k∈)
  with s₁ k | k∈
... | just _  | _ = -, refl
∈ᵈ-∪⁺ {s₁}{s₂}{k} s₁♯s₂ (inj₂ k∈)
  with s₁ k | proj₂ (s₁♯s₂ k) k∈
... | nothing | _ = k∈

∉ᵈ-∪⁻ :
    (p : s₁ ♯ s₂)
  → k ∉ᵈ (s₁ ∪ s₂ ∶- p)
  → (k ∉ᵈ s₁) × (k ∉ᵈ s₂)
∉ᵈ-∪⁻ {s₁}{s₂}{k} s₁♯s₂ k∉
  with s₁ k | k∉
... | nothing | k∉′
  with s₂ k | k∉′
... | nothing | _ = refl , refl

∉ᵈ-∪⁺ :
    (p : s₁ ♯ s₂)
  → (k ∉ᵈ s₁) × (k ∉ᵈ s₂)
  → k ∉ᵈ (s₁ ∪ s₂ ∶- p)
∉ᵈ-∪⁺ {s₁}{s₂}{k} p (k∉₁ , k∉₂)
  with s₁ k | k∉₁
... | nothing | _
  with s₂ k | k∉₂
... | nothing | _ = refl

♯-∪⁻ʳ :
    (p : s₂ ♯ s₃)
  → s₁ ♯ (s₂ ∪ s₃ ∶- p)
  → (s₁ ♯ s₂) × (s₁ ♯ s₃)
♯-∪⁻ʳ {s₂}{s₃}{s₁} s₂♯s₃ s₁♯s₂₃ = s₁♯s₂ , s₁♯s₃
  where
    s₁♯s₂ : s₁ ♯ s₂
    s₁♯s₂ k = proj₁ ∘ ∉ᵈ-∪⁻ s₂♯s₃ ∘ proj₁ (s₁♯s₂₃ k)
            , proj₂ (s₁♯s₂₃ k) ∘ ∈ᵈ-∪⁺ s₂♯s₃ ∘ inj₁

    s₁♯s₃ : s₁ ♯ s₃
    s₁♯s₃ k = proj₂ ∘ ∉ᵈ-∪⁻ s₂♯s₃ ∘ proj₁ (s₁♯s₂₃ k)
            , proj₂ (s₁♯s₂₃ k) ∘ ∈ᵈ-∪⁺ s₂♯s₃ ∘ inj₂

♯-∪⁻ˡ :
    (p : s₁ ♯ s₂)
  → (s₁ ∪ s₂ ∶- p) ♯ s₃
  → (s₁ ♯ s₃) × (s₂ ♯ s₃)
♯-∪⁻ˡ p q = let l , r = ♯-∪⁻ʳ p (♯-comm q)
            in  ♯-comm l , ♯-comm r

♯-∪⁺ˡ :
    (p : s₁ ♯ s₂)
  → (s₁ ♯ s₃) × (s₂ ♯ s₃)
  → (s₁ ∪ s₂ ∶- p) ♯ s₃
♯-∪⁺ˡ {s₁}{s₂}{s₃} s₁♯s₂ (s₁♯s₃ , s₂♯s₃) k = f , g
  where
    s₁₂ = s₁ ∪ s₂ ∶- s₁♯s₂

    f : k ∈ᵈ s₁₂ → k ∉ᵈ s₃
    f k∈ with ∈ᵈ-∪⁻ s₁♯s₂ k∈
    ... | inj₁ k∈₁ = proj₁ (s₁♯s₃ k) k∈₁
    ... | inj₂ k∈₂ = proj₁ (s₂♯s₃ k) k∈₂

    g : k ∈ᵈ s₃ → k ∉ᵈ s₁₂
    g k∈ = ∉ᵈ-∪⁺ s₁♯s₂ (proj₂ (s₁♯s₃ k) k∈ , proj₂ (s₂♯s₃ k) k∈)

♯-∪⁺ʳ :
    (p : s₂ ♯ s₃)
  → (s₁ ♯ s₂) × (s₁ ♯ s₃)
  → s₁ ♯ (s₂ ∪ s₃ ∶- p)
♯-∪⁺ʳ {s₂}{s₃}{s₁} s₂♯s₃ (s₁♯s₂ , s₁♯s₃) k = f , g
  where
    s₂₃ = s₂ ∪ s₃ ∶- s₂♯s₃

    f : k ∈ᵈ s₁ → k ∉ᵈ s₂₃
    f k∈ = ∉ᵈ-∪⁺ s₂♯s₃ (proj₁ (s₁♯s₂ k) k∈ , proj₁ (s₁♯s₃ k) k∈)

    g : k ∈ᵈ s₂₃ → k ∉ᵈ s₁
    g k∈ with ∈ᵈ-∪⁻ s₂♯s₃ k∈
    ... | inj₁ k∈₂ = proj₂ (s₁♯s₂ k) k∈₂
    ... | inj₂ k∈₃ = proj₂ (s₁♯s₃ k) k∈₃

∪≡-assocʳ :
    (s₁♯s₂ : s₁ ♯ s₂) (s₁♯s₃ : s₁ ♯ s₃) (s₂♯s₃ : s₂ ♯ s₃)
  → let s₁₂ = s₁ ∪ s₂ ∶- s₁♯s₂
        s₂₃ = s₂ ∪ s₃ ∶- s₂♯s₃
    in s₁ ∪ s₂₃ ≡ s → s₁₂ ∪ s₃ ≡ s
∪≡-assocʳ {s₁}{s₂}{s₃}{s} s₁♯s₂ s₁♯s₃ s₂♯s₃ (s₁♯s₂₃ , ≡s) = s₁₂♯s₃ , ≡s′
  where
    s₁₂ = s₁ ∪ s₂ ∶- s₁♯s₂
    s₂₃ = s₂ ∪ s₃ ∶- s₂♯s₃

    s₁₂♯s₃ : s₁₂ ♯ s₃
    s₁₂♯s₃ = ♯-∪⁺ˡ s₁♯s₂ (s₁♯s₃ , s₂♯s₃)

    p : (s₁ ∪ s₂₃ ∶- s₁♯s₂₃) ≈ (s₁₂ ∪ s₃ ∶- s₁₂♯s₃)
    p k with s₁ k | s₂ k  | s₃ k
    ... | just _  | _       | _       = refl
    ... | nothing | nothing | nothing = refl
    ... | nothing | just _  | _       = refl
    ... | nothing | nothing | just _  = refl

    ≡s′ : (s₁₂ ∪ s₃ ∶- s₁₂♯s₃) ≈ s
    ≡s′ = ≈-trans (≈-sym p) ≡s

∪≡-assocˡ :
    (s₁♯s₂ : s₁ ♯ s₂) (s₁♯s₃ : s₁ ♯ s₃) (s₂♯s₃ : s₂ ♯ s₃)
  → let s₁₂ = s₁ ∪ s₂ ∶- s₁♯s₂
        s₂₃ = s₂ ∪ s₃ ∶- s₂♯s₃
    in s₁₂ ∪ s₃ ≡ s → s₁ ∪ s₂₃ ≡ s
∪≡-assocˡ {s₁}{s₂}{s₃}{s} s₁♯s₂ s₁♯s₃ s₂♯s₃ =
    ∪≡-comm ∘ ∪≡-assocʳ s₂♯s₃ (♯-comm s₁♯s₂) (♯-comm s₁♯s₃)
  ∘ ∪≡-comm ∘ ∪≡-assocʳ (♯-comm s₁♯s₃) (♯-comm s₂♯s₃) s₁♯s₂
  ∘ ∪≡-comm
