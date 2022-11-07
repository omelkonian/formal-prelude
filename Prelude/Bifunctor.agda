module Prelude.Bifunctor where

open import Prelude.Init; open SetAsType

private
  variable
    a a′ a″ b c : Level
    A  : Type a
    A′ : Type a′
    A″ : Type a″
    B  : A  → Type b
    B′ : A → Type b
    C  : A′ → Type c

record BifunctorI (F : (A : Type a) → (B : A → Type b) → Type (a ⊔ₗ b)) : Type (lsuc a ⊔ₗ lsuc b) where
  field
    bimap′ : (f : A → A′) → (∀ {x} → B x → C (f x)) → F A B → F A′ C

  map₁′ : (A → A′) → F A (const A″) → F A′ (const A″)
  map₁′ f = bimap′ f id
  _<$>₁′_ = map₁′

  map₂′ : (∀ {x} → B x → B′ x) → F A B → F A B′
  map₂′ g = bimap′ id g
  _<$>₂′_ = map₂′

open BifunctorI ⦃...⦄ public

instance
  Bifunctor-Σ : BifunctorI {a}{b} Σ
  Bifunctor-Σ .bimap′ = Product.map

record Bifunctor (F : Type a → Type b → Type (a ⊔ₗ b)) : Type (lsuc a ⊔ₗ lsuc b) where
  field
    bimap : ∀ {A A′ : Type a} {B B′ : Type b}
          → (A → A′) → (B → B′) → F A B → F A′ B′

  map₁ : ∀ {A A′ : Type a} {B : Type b} → (A → A′) → F A B → F A′ B
  map₁ f = bimap f id
  _<$>₁_ = map₁

  map₂ : ∀ {A : Type a} {B B′ : Type b} → (B → B′) → F A B → F A B′
  map₂ g = bimap id g
  _<$>₂_ = map₂

open Bifunctor ⦃...⦄ public

map₁₂ : ∀ {F : Type a → Type a → Type a} {A B : Type a} → ⦃ Bifunctor F ⦄ → (A → B) → F A A → F B B
map₁₂ f = bimap f f
_<$>₁₂_ = map₁₂

instance
  Bifunctor-× : Bifunctor {a}{b} _×_
  Bifunctor-× .bimap f g = Product.map f g

  Bifunctor-⊎ : Bifunctor {a}{b} _⊎_
  Bifunctor-⊎ .bimap = Sum.map
