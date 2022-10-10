module Prelude.SetCollections where

open import Prelude.Init; open SetAsType
open import Prelude.DecEq
open import Prelude.Sets.Concrete
open import Prelude.ToList

open import Prelude.General
open import Prelude.Setoid

record _has_ (A B : Type) ⦃ _ : DecEq B ⦄ : Type where
  field collect : A → Set⟨ B ⟩
  syntax collect {A = A} = collect[ A ]

  collectList : A → List B
  collectList = toList ∘ collect
open _has_ ⦃...⦄ public

-- NB: do not expose list/pair instances, let user decide

module _ {X Y : Type} ⦃ _ : DecEq X ⦄ ⦃ _ : DecEq Y ⦄ where
  collectFromList : (X → Set⟨ Y ⟩) → (Set⟨ X ⟩ → Set⟨ Y ⟩)
  collectFromList f s = concatMapˢ f s

module _ {X Y Z : Type} ⦃ _ : DecEq Z ⦄ where
  collectFromPairˡ : (X → Set⟨ Z ⟩) → X × Y → Set⟨ Z ⟩
  collectFromPairˡ = _∘ proj₁

  collectFromPairʳ : (Y → Set⟨ Z ⟩) → X × Y → Set⟨ Z ⟩
  collectFromPairʳ = _∘ proj₂

  collectFromPairˡʳ : (X → Set⟨ Z ⟩) → (Y → Set⟨ Z ⟩) → X × Y → Set⟨ Z ⟩
  collectFromPairˡʳ f g (x , y) = f x ∪ g y

--

relateOn : ∀ {Z A B : Type} {Z′ : Type ℓ}
  → ⦃ _ : DecEq Z ⦄ ⦃ _ : A has Z ⦄ ⦃ _ : B has Z ⦄
  → Rel Z′ ℓ′
  → A
  → (∀ {X} → ⦃ X has Z ⦄ → X → Z′)
  → B
  → Type _
relateOn _~_ a f b = f a ~ f b
syntax relateOn _~_ a f b = a ⦅ _~_ on f ⦆ b

module _ {Z}{A}{B}⦃ dz ⦄ ⦃ ia ⦄ ⦃ ib ⦄ where
  _→⦅_⦆_ = relateOn {Z = Z}{A}{B}{Type}⦃ dz ⦄ ⦃ ia ⦄ ⦃ ib ⦄ _`→`_
  module _ {Z′} where
    _≡⦅_⦆_ = relateOn {ℓ′ = 0ℓ} {Z = Z}{A}{B}{Z′}⦃ dz ⦄ ⦃ ia ⦄ ⦃ ib ⦄ _≡_
    module _ ⦃ _ : ISetoid Z′ ⦄ where
      _≈⦅_⦆_ = relateOn {Z = Z}{A}{B}{Z′}⦃ dz ⦄ ⦃ ia ⦄ ⦃ ib ⦄ _≈_
