------------------------------------------------------------------------
-- Maps with set witness, paired with a total function.
--   * Equivalence using set equality `_~[ set ]_`
------------------------------------------------------------------------
{-# OPTIONS --allow-unsolved-metas #-}
open import Prelude.Init
open L.Any using (index)
open import Prelude.DecEq
open import Prelude.Lists hiding (_⁉_)
open import Prelude.Functor
open import Prelude.Bifunctor
open import Prelude.Applicative
open import Prelude.Monoid
open import Prelude.Nary

open import Prelude.Sets as S using
  (_∈′_; _∈′?_; _∉′_; _∉′?_; _⊆′_; _⊈′_; ∈-∪⁺ˡ; ∈-∪⁺ʳ; ∈-∪⁻; ∅; singleton; ∈′-irr)

open import Data.List.Relation.Binary.BagAndSetEquality
open import Function.Related using (≡⇒)
import Data.List.Relation.Binary.Disjoint.Setoid.Properties as Disjoint
open import Data.List.Relation.Binary.BagAndSetEquality using (_∼[_]_; set)
import Function.Equivalence as Equiv

module Prelude.Maps.AsTotalFunctions3 {K V : Set} {{_ : DecEq K}} where

record Map : Set where
  constructor ⟨_⟩∶-_
  field
    keys   : S.Set⟨ K ⟩
    lookup : S.toList keys ↦ V
open Map public

syntax Map {K} {V} = Map⟨ K ↦ V ⟩

_⁉_ : Map → K → Maybe V
(⟨ ks ⟩∶- f) ⁉ k with k ∈′? ks
... | yes k∈ = just (f k∈)
... | no  _  = nothing

∅′ : Map
∅′ = ⟨ ∅ ⟩∶- λ ()

singleton′ : K → V → Map
singleton′ k v = ⟨ singleton k ⟩∶- λ{ (here _) → v; (there ()) }

_[_↦_] : Map → K → V → Set
m [ k ↦ v ] = (m ⁉ k) ≡ just v

infix 3 _∈ᵈ_ _∉ᵈ_ _∈ᵈ?_ _∉ᵈ?_
_∈ᵈ_ _∉ᵈ_ : K → Map → Set
k ∈ᵈ m = k ∈′ keys m
k ∉ᵈ m = k ∉′ keys m

_∈ᵈ?_ : Decidable² _∈ᵈ_
k ∈ᵈ? m = k ∈′? keys m

_∉ᵈ?_ : Decidable² _∉ᵈ_
k ∉ᵈ? m = k ∉′? keys m

postulate toList : Map → List (K × V)

_⊆ᵈ_ _⊈ᵈ_ _♯_ _≈_ : Rel₀ Map
_⊆ᵈ_ = _⊆′_ on keys
_⊈ᵈ_ = _⊈′_ on keys
_♯_ = S._♯_ on keys
m ≈ m′ = toList m ∼[ set ] toList m′

infixr 4 _∪_
_∪_ : Op₂ Map
m ∪ m′ = ⟨ keys m S.∪ keys m′ ⟩∶- λ p → case ∈-∪⁻ {xs = keys m}{ys = keys m′} p of λ where
  (inj₁ k∈) → lookup m k∈
  (inj₂ k∈) → lookup m′ k∈

⟨_⊎_⟩≡_ : Map → Map → Map → Set
⟨ m₁ ⊎ m₂ ⟩≡ m = (m₁ ♯ m₂) × ((m₁ ∪ m₂) ≈ m)

-- lemmas
private
  variable
    s s₁ s₂ s₃ : Map
    k : K
    v : V

≈-refl : s ≈ s
≈-refl {s} = {!!} -- cong (lookup s) ∘ ∈′-irr {Xs = keys s}

≈-trans : s₁ ≈ s₂ → s₂ ≈ s₃ → s₁ ≈ s₃
≈-trans x y = y Equiv.∘ x

≈-sym : s₁ ≈ s₂ → s₂ ≈ s₁
≈-sym p = Equiv.sym p

-- ≈-cong : ∀ {P : K → Maybe V → Set}
--   → s₁ ≈ s₂
--   → (∀ k → P k (s₁ k))
--   → (∀ k → P k (s₂ k))
-- ≈-cong {P = P} eq p = ? -- subst (P k) (eq k) (p k)

♯-comm : Symmetric _♯_
♯-comm = Disjoint.sym (setoid K)

-- ♯-cong : s₁ ≈ s₂ → s₁ ♯ s₃ → s₂ ♯ s₃
-- ♯-cong eq s₁♯s₃ k
--   with p ← s₁♯s₃ k
--   rewrite eq k = p

-- ∪-comm : s₁ ♯ s₂ → (s₁ ∪ s₂) ≈ (s₂ ∪ s₁)
-- ∪-comm {s₁}{s₂} s₁♯s₂ k
--   with k ∈ᵈ? s₁ ∪ s₂ | k ∈ᵈ? s₂ ∪ s₁
-- ... | no _ | no _ = refl
-- ... | no k∉ | yes k∈′ = ⊥-elim $ k∉ $ case ∈-∪⁻ {xs = keys s₂}{keys s₁} k∈′ of λ where
--   (inj₁ k∈) → ∈-∪⁺ʳ {xs = keys s₁}{keys s₂} k∈
--   (inj₂ k∈) → ∈-∪⁺ˡ {xs = keys s₁}{keys s₂} k∈
-- ... | yes k∈ | no k∉ = ⊥-elim $ k∉ $ case ∈-∪⁻ {xs = keys s₁}{keys s₂} k∈ of λ where
--   (inj₁ k∈) → ∈-∪⁺ʳ {xs = keys s₂}{keys s₁} k∈
--   (inj₂ k∈) → ∈-∪⁺ˡ {xs = keys s₂}{keys s₁} k∈
-- ... | yes k∈ | yes k∈′
--   with ∈-∪⁻ {xs = keys s₁}{keys s₂} k∈ | ∈-∪⁻ {xs = keys s₂}{keys s₁} k∈′
-- ... | inj₁ k∈₁ | inj₁ k∈₂  = ⊥-elim $ s₁♯s₂ (k∈₁ , k∈₂)
-- ... | inj₁ k∈₁ | inj₂ k∈₁′ = cong (just ∘ lookup s₁) (∈′-irr {Xs = keys s₁} _ _)
-- ... | inj₂ k∈₂ | inj₁ k∈₂′ = cong (just ∘ lookup s₂) (∈′-irr {Xs = keys s₂} _ _)
-- ... | inj₂ k∈₂ | inj₂ k∈₁  = ⊥-elim $ s₁♯s₂ (k∈₁ , k∈₂)

-- -- ∪-cong : (p : s₁ ♯ s₃) (eq : s₁ ≈ s₂) → (s₁ ∪ s₃ ∶- p) ≈ (s₂ ∪ s₃ ∶- ♯-cong eq p)
-- -- ∪-cong {s₁}{s₃}{s₂} s₁♯s₃ eq k
-- --   with s₁ k | s₂ k | eq k
-- -- ... | nothing | .nothing  | refl = refl
-- -- ... | just x  | .(just x) | refl = refl

-- ∪≡-comm : Symmetric (⟨_⊎_⟩≡ s)
-- ∪≡-comm {s}{s₁}{s₂} (s₁♯s₂ , ≡s) = ♯-comm {s₁}{s₂} s₁♯s₂ , ≈-trans (≈-sym $ ∪-comm s₁♯s₂) ≡s

-- -- ∪≡-cong : s₁ ≈ s₂ → s₁ ∪ s₃ ≡ s → s₂ ∪ s₃ ≡ s
-- -- ∪≡-cong eq (s₁♯s₃ , ≡s) = ♯-cong eq s₁♯s₃ , ≈-trans (≈-sym (∪-cong s₁♯s₃ eq)) ≡s

-- ∈ᵈ-∪⁻ : k ∈ᵈ (s₁ ∪ s₂) → (k ∈ᵈ s₁) ⊎ (k ∈ᵈ s₂)
-- ∈ᵈ-∪⁻ {k}{s₁}{s₂} = ∈-∪⁻ {xs = keys s₁}{keys s₂}

-- ∈ᵈ-∪⁺ : (k ∈ᵈ s₁) ⊎ (k ∈ᵈ s₂) → k ∈ᵈ (s₁ ∪ s₂)
-- ∈ᵈ-∪⁺ {k}{s₁}{s₂} = case_of λ where
--   (inj₁ k∈) → ∈-∪⁺ˡ {xs = keys s₁}{keys s₂} k∈
--   (inj₂ k∈) → ∈-∪⁺ʳ {xs = keys s₁}{keys s₂} k∈

-- ∉ᵈ-∪⁻ : k ∉ᵈ (s₁ ∪ s₂) → (k ∉ᵈ s₁) × (k ∉ᵈ s₂)
-- ∉ᵈ-∪⁻ {s₁ = ⟨ ks₁ ⟩∶- _} {s₂ = ⟨ ks₂ ⟩∶- _} k∉ = (⊥-elim ∘ k∉ ∘ ∈-∪⁺ˡ {xs = ks₁}{ks₂})
--                                                , (⊥-elim ∘ k∉ ∘ ∈-∪⁺ʳ {xs = ks₁}{ks₂})

-- ∉ᵈ-∪⁺ : (k ∉ᵈ s₁) × (k ∉ᵈ s₂) → k ∉ᵈ (s₁ ∪ s₂)
-- ∉ᵈ-∪⁺ {s₁ = s₁}{s₂} (k∉₁ , k∉₂) k∈ = case ∈-∪⁻ {xs = keys s₁}{keys s₂} k∈ of λ where
--   (inj₁ k∈₁) → ⊥-elim $ k∉₁ k∈₁
--   (inj₂ k∈₂) → ⊥-elim $ k∉₂ k∈₂

-- ♯-∪⁻ʳ : s₁ ♯ (s₂ ∪ s₃) → (s₁ ♯ s₂) × (s₁ ♯ s₃)
-- ♯-∪⁻ʳ {s₁}{s₂}{s₃} s₁♯s₂₃ = (s₁♯s₂₃ ∘ map₂ (∈-∪⁺ˡ {xs = keys s₂}{keys s₃}))
--                           , (s₁♯s₂₃ ∘ map₂ (∈-∪⁺ʳ {xs = keys s₂}{keys s₃}))

-- ♯-∪⁻ˡ : (s₁ ∪ s₂) ♯ s₃ → (s₁ ♯ s₃) × (s₂ ♯ s₃)
-- ♯-∪⁻ˡ {s₁}{s₂}{s₃} p =
--   let l , r = ♯-∪⁻ʳ {s₃}{s₁}{s₂} (♯-comm {s₁ ∪ s₂}{s₃} p)
--   in  ♯-comm {s₃}{s₁} l , ♯-comm {s₃}{s₂} r

-- ♯-∪⁺ˡ : (s₁ ♯ s₃) × (s₂ ♯ s₃) → (s₁ ∪ s₂) ♯ s₃
-- ♯-∪⁺ˡ {s₁}{s₃}{s₂} (s₁♯s₃ , s₂♯s₃) (k∈₁₂ , k∈₃)
--   with ∈ᵈ-∪⁻ {s₁ = s₁}{s₂} k∈₁₂
-- ... | inj₁ k∈₁ = s₁♯s₃ (k∈₁ , k∈₃)
-- ... | inj₂ k∈₂ = s₂♯s₃ (k∈₂ , k∈₃)

-- ♯-∪⁺ʳ : (s₁ ♯ s₂) × (s₁ ♯ s₃) → s₁ ♯ (s₂ ∪ s₃)
-- ♯-∪⁺ʳ {s₁}{s₂}{s₃} (s₁♯s₂ , s₁♯s₃) = ♯-comm {s₂ ∪ s₃}{s₁} $ ♯-∪⁺ˡ {s₂}{s₁}{s₃} (♯-comm {s₁}{s₂} s₁♯s₂ , ♯-comm {s₁}{s₃} s₁♯s₃)

-- ∪≡-assocʳ : s₁ ♯ s₂ → s₁ ♯ s₃ → s₂ ♯ s₃
--   → ⟨ s₁ ⊎ (s₂ ∪ s₃) ⟩≡ s → ⟨ (s₁ ∪ s₂) ⊎ s₃ ⟩≡ s
-- ∪≡-assocʳ {s₁}{s₂}{s₃}{s} s₁♯s₂ s₁♯s₃ s₂♯s₃ (s₁♯s₂₃ , ≡s) = s₁₂♯s₃ , ≡s′
--   where
--     s₁₂♯s₃ : (s₁ ∪ s₂) ♯ s₃
--     s₁₂♯s₃ = ♯-∪⁺ˡ {s₁}{s₃}{s₂} (s₁♯s₃ , s₂♯s₃)

--     p : (s₁ ∪ (s₂ ∪ s₃)) ≈ ((s₁ ∪ s₂) ∪ s₃)
--     p k
--       with k ∈ᵈ? s₁ ∪ (s₂ ∪ s₃) | k ∈ᵈ? (s₁ ∪ s₂) ∪ s₃
--     ... | no _ | no _ = refl
--     ... | no k∉ | yes k∈′ = ⊥-elim $ k∉ $ case ∈-∪⁻ {xs = keys (s₁ ∪ s₂)}{keys s₃} k∈′ of λ where
--       (inj₁ k∈₁₂) → case ∈-∪⁻ {xs = keys s₁}{keys s₂} k∈₁₂ of λ where
--         (inj₁ k∈₁) → ∈-∪⁺ˡ {xs = keys s₁}{keys (s₂ ∪ s₃)} k∈₁
--         (inj₂ k∈₂) → ∈-∪⁺ʳ {xs = keys s₁}{keys (s₂ ∪ s₃)} (∈-∪⁺ˡ {xs = keys s₂}{keys s₃} k∈₂)
--       (inj₂ k∈₃) → ∈-∪⁺ʳ {xs = keys s₁}{keys (s₂ ∪ s₃)} (∈-∪⁺ʳ {xs = keys s₂}{keys s₃} k∈₃)
--     ... | yes k∈ | no k∉ = ⊥-elim $ k∉ $ case ∈-∪⁻ {xs = keys s₁}{keys (s₂ ∪ s₃)} k∈ of λ where
--       (inj₁ k∈₁)  → ∈-∪⁺ˡ {xs = keys (s₁ ∪ s₂)}{keys s₃} $ ∈-∪⁺ˡ {xs = keys s₁}{keys s₂} k∈₁
--       (inj₂ k∈₂₃) → case ∈-∪⁻ {xs = keys s₂}{keys s₃} k∈₂₃ of λ where
--         (inj₁ k∈₂) → ∈-∪⁺ˡ {xs = keys (s₁ ∪ s₂)}{keys s₃} $ ∈-∪⁺ʳ {xs = keys s₁}{keys s₂} k∈₂
--         (inj₂ k∈₃) → ∈-∪⁺ʳ {xs = keys (s₁ ∪ s₂)}{keys s₃} k∈₃
--     ... | yes k∈ | yes k∈′



--        with ∈-∪⁻ {xs = keys s₁}{keys (s₂ ∪ s₃)} k∈
--     ... | inj₁ k∈₁ = case ∈-∪⁻ {xs = keys (s₁ ∪ s₂)}{keys s₃} k∈′ of λ where
--         (inj₁ k∈₁₂) → case ∈-∪⁻ {xs = keys s₁}{keys s₂} k∈₁₂ of λ where
--           (inj₁ k∈₁) → {!refl!}
--           (inj₂ k∈₂) → {!!}
--         (inj₂ k∈₃) → {!!}
--     ... | inj₂ k∈₂₃
--       with ∈-∪⁻ {xs = keys s₂}{keys s₃} k∈₂₃
--     ... | inj₁ k∈₂ = {!refl!}
--     ... | inj₂ k∈₃

--       with ∈-∪⁻ {xs = keys (s₁ ∪ s₂)}{keys s₃} k∈′
--     ... | inj₂ k∈₃′ = cong (just ∘ lookup s₃) (∈′-irr {Xs = keys s₃} _ _)
--     ... | inj₁ k∈₁₂
--       with ∈-∪⁻ {xs = keys s₁}{keys s₂} k∈₁₂
--     ... | inj₁ k∈₁′ = ⊥-elim $ s₁♯s₃ (k∈₁′ , k∈₃)
--     ... | inj₂ k∈₂′ = ⊥-elim $ s₂♯s₃ (k∈₂′ , k∈₃)


--     ≡s′ : ((s₁ ∪ s₂) ∪ s₃) ≈ s
--     ≡s′ = ≈-trans (≈-sym p) ≡s

-- ∪≡-assocˡ : s₁ ♯ s₂ → s₁ ♯ s₃ → s₂ ♯ s₃
--   → ⟨ (s₁ ∪ s₂) ⊎ s₃ ⟩≡ s → ⟨ s₁ ⊎ (s₂ ∪ s₃) ⟩≡ s
-- ∪≡-assocˡ {s₁}{s₂}{s₃}{s} s₁♯s₂ s₁♯s₃ s₂♯s₃ =
--     ∪≡-comm {x = s₂ ∪ s₃}{s₁} ∘ ∪≡-assocʳ s₂♯s₃ (♯-comm {s₁}{s₂} s₁♯s₂) (♯-comm {s₁}{s₃} s₁♯s₃)
--   ∘ ∪≡-comm ∘ ∪≡-assocʳ (♯-comm {s₁}{s₃} s₁♯s₃) (♯-comm {s₂}{s₃} s₂♯s₃) s₁♯s₂
--   ∘ ∪≡-comm




-- -- -- instance
-- -- --   Functor-Map : Functor λ V → Map⟨ K ↦ V ⟩
-- -- --   Functor-Map ._<$>_ f (⟨ ks ⟩∶- g) = ⟨ ks ⟩∶- (f ∘ g)

-- -- --   Semigroup-Map : Semigroup (Map)
-- -- --   Semigroup-Map ._◇_ = unionWith (λ _ v → v)

-- -- --   Monoid-Map : Monoid (Map)
-- -- --   Monoid-Map .ε = ∅

-- -- -- t : Map⟨ ℕ ↦ String ⟩
-- -- -- t = singleton 42 "nope" ◇ singleton 42 "yep"

-- -- {-
-- --   DecEq-↦ : ∀ {xs : List K} → DecEq (xs ↦ V)
-- --   DecEq-↦ {xs = []} ._≟_ f f′ = {!!}
-- --   DecEq-↦ {xs = x ∷ xs} ._≟_ f f′ = {!!}

-- --   DecEq-Map : DecEq (Map)
-- --   DecEq-Map ._≟_ m m′
-- --     with keys m ≟ keys m′
-- --   ... | no ¬p    = no λ{ refl → ¬p refl }
-- --   ... | yes refl
-- --     with lookup m ≟ lookup m′
-- --   ... | no ¬p    = no λ{ refl → ¬p refl }
-- --   ... | yes refl = yes refl
-- -- -}
