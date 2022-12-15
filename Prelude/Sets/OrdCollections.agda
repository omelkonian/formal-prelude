{-# OPTIONS --with-K #-}
module Prelude.Sets.OrdCollections where

open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Sets.AsSortedUniqueLists
open import Prelude.ToList
open import Prelude.Setoid
open import Prelude.Apartness
open import Prelude.Ord

record _has_ (A B : Type) ⦃ _ : Ord⁺⁺ B ⦄ ⦃ _ : DecEq B ⦄ : Type where
  field collect : A → Set⟨ B ⟩
  syntax collect {A = A} = collect[ A ]

  collectList : A → List B
  collectList = toList ∘ collect
open _has_ ⦃...⦄ public

-- NB: do not expose list/pair instances, let user decide

-- module _ {X Y : Type} ⦃ _ : DecEq X ⦄ ⦃ _ : DecEq Y ⦄ where
--   collectFromSet : (X → Set⟨ Y ⟩) → (Set⟨ X ⟩ → Set⟨ Y ⟩)
--   collectFromSet f s = concatMapˢ f s

--   collectFromSet≈ : ∀ (f : X → Set⟨ Y ⟩) {xs ys : Set⟨ X ⟩}
--     → xs ≈ ys
--     → collectFromSet f xs ≈ collectFromSet f ys
--   collectFromSet≈ f {xs}{ys} = ≈ˢ-concatMap⁺ f {xs}{ys}

-- module _ {X Y Z : Type} ⦃ _ : DecEq Z ⦄ where
--   collectFromPairˡ : (X → Set⟨ Z ⟩) → X × Y → Set⟨ Z ⟩
--   collectFromPairˡ = _∘ proj₁

--   collectFromPairʳ : (Y → Set⟨ Z ⟩) → X × Y → Set⟨ Z ⟩
--   collectFromPairʳ = _∘ proj₂

--   collectFromPairˡʳ : (X → Set⟨ Z ⟩) → (Y → Set⟨ Z ⟩) → X × Y → Set⟨ Z ⟩
--   collectFromPairˡʳ f g (x , y) = f x ∪ g y

-- --

-- relateOn : ∀ {Z A B : Type} {Z′ : Type ℓ}
--   → ⦃ _ : DecEq Z ⦄ ⦃ _ : A has Z ⦄ ⦃ _ : B has Z ⦄
--   → Rel Z′ ℓ′
--   → A
--   → (∀ {X} → ⦃ X has Z ⦄ → X → Z′)
--   → B
--   → Type _
-- relateOn _~_ a f b = f a ~ f b
-- syntax relateOn _~_ a f b = a ⦅ _~_ on f ⦆ b

-- module _ {Z}{A}{B}⦃ dz ⦄ ⦃ ia ⦄ ⦃ ib ⦄ where
--   _→⦅_⦆_ = relateOn {Z = Z}{A}{B}{Type}⦃ dz ⦄ ⦃ ia ⦄ ⦃ ib ⦄ _`→`_
--   _⊆⦅_⦆_ = relateOn {ℓ′ = 0ℓ}{Z = Z}{A}{B}{Set⟨ Z ⟩}⦃ dz ⦄ ⦃ ia ⦄ ⦃ ib ⦄ _⊆ˢ_
--   module _ {Z′} where
--     _≡⦅_⦆_ = relateOn {ℓ′ = 0ℓ}{Z = Z}{A}{B}{Z′}⦃ dz ⦄ ⦃ ia ⦄ ⦃ ib ⦄ _≡_
--     module _ ⦃ _ : ISetoid Z′ ⦄ where
--       _≈⦅_⦆_ = relateOn {Z = Z}{A}{B}{Z′}⦃ dz ⦄ ⦃ ia ⦄ ⦃ ib ⦄ _≈_
--     module _ ⦃ _ : Z′ // Z′ ⦄ where
--       _♯⦅_⦆_ = relateOn {ℓ′ = 0ℓ}{Z = Z}{A}{B}{Z′}⦃ dz ⦄ ⦃ ia ⦄ ⦃ ib ⦄ _♯_
