module Prelude.Bifunctor where

open import Function using (id)
open import Prelude.Init

private
  variable
    a a′ a″ b c : Level
    A  : Set a
    A′ : Set a′
    A″ : Set a″
    B  : A  → Set b
    B′ : A → Set b
    C  : A′ → Set c

record BifunctorI (F : (A : Set a) → (B : A → Set b) → Set (a ⊔ₗ b)) : Set (lsuc a ⊔ₗ lsuc b) where
  field
    bimap′ : (f : A → A′) → (∀ {x} → B x → C (f x)) → F A B → F A′ C

  map₁′ : (A → A′) → F A (const A″) → F A′ (const A″)
  map₁′ f = bimap′ f id

  map₂′ : (∀ {x} → B x → B′ x) → F A B → F A B′
  map₂′ g = bimap′ id g

open BifunctorI ⦃...⦄ public

instance
  Bifunctor-Σ : BifunctorI {a}{b} Σ
  Bifunctor-Σ .bimap′ = Product.map

record Bifunctor (F : Set a → Set b → Set (a ⊔ₗ b)) : Set (lsuc a ⊔ₗ lsuc b) where
  field
    bimap : ∀ {A A′ : Set a} {B B′ : Set b}
          → (A → A′) → (B → B′) → F A B → F A′ B′

  map₁ : ∀ {A A′ : Set a} {B : Set b} → (A → A′) → F A B → F A′ B
  map₁ f = bimap f id

  map₂ : ∀ {A : Set a} {B B′ : Set b} → (B → B′) → F A B → F A B′
  map₂ g = bimap id g

open Bifunctor ⦃...⦄ public

map₁₂ : ∀ {F : Set a → Set a → Set a} {A B : Set a} → ⦃ Bifunctor F ⦄ → (A → B) → F A A → F B B
map₁₂ f = bimap f f

instance
  Bifunctor-× : Bifunctor {a}{b} _×_
  Bifunctor-× .bimap f g = Product.map f g

  Bifunctor-⊎ : Bifunctor {a}{b} _⊎_
  Bifunctor-⊎ .bimap = Sum.map
