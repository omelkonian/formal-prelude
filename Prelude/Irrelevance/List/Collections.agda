{-# OPTIONS --with-K #-}
module Prelude.Irrelevance.List.Collections where

open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Irrelevance.List.Permutation

record _has_ (A : Type) (B : Type) : Type where
  field collect : A → List B
  syntax collect {A = A} = collect[ A ]
open _has_ ⦃...⦄ public

-- NB: do not expose list/pair instances, let user decide
private variable X Y Z : Type

collectFromList : (X → List Y) → (List X → List Y)
collectFromList = concatMap

collectFromPairˡ : (X → List Z) → (X × Y) → List Z
collectFromPairˡ = _∘ proj₁

collectFromPairʳ : (Y → List Z) → (X × Y) → List Z
collectFromPairʳ = _∘ proj₂

--

relateOn : ∀ {ℓ} {Z A B : Type} {Z′ : Type ℓ} → ⦃ A has Z ⦄ → ⦃ B has Z ⦄
  → Rel₀ Z′
  → A
  → (∀ {X} → ⦃ X has Z ⦄ → X → Z′)
  → B → Type
relateOn _~_ a f b = f a ~ f b
syntax relateOn _~_ a f b = a ⦅ _~_ on f ⦆ b

module _ {Z}{A}{B}⦃ ia ⦄ ⦃ ib ⦄ where
  _→⦅_⦆_ = relateOn {Z = Z}{A}{B}{Type}⦃ ia ⦄ ⦃ ib ⦄ _`→`_
  module _ {Z′} where
    _≡⦅_⦆_ = relateOn {Z = Z}{A}{B}{Z′}⦃ ia ⦄ ⦃ ib ⦄ _≡_
    _↭⦅_⦆_ = relateOn {Z = Z}{A}{B}{List Z′}⦃ ia ⦄ ⦃ ib ⦄ _↭_
    _⊆⦅_⦆_ = relateOn {Z = Z}{A}{B}{List Z′}⦃ ia ⦄ ⦃ ib ⦄ _⊆_

collectFromList↭ : ∀ ⦃ _ : DecEq Y ⦄ {xs ys : List X}
  → (f : X → List Y)
  → xs ·↭ ys
  → collectFromList f xs ·↭ collectFromList f ys
collectFromList↭ f p = ·↭-concatMap⁺ f p
