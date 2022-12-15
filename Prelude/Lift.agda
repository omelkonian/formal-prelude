{-# OPTIONS --safe #-}
module Prelude.Lift where

open import Prelude.Init; open SetAsType
open Lvl public using (Lift; lift; lower)

↑ℓ : Type ℓ → {ℓ′ : Level} → Type (ℓ ⊔ₗ ℓ′)
↑ℓ A {ℓ′} = Lvl.Lift ℓ′ A

record ↑ω_ (A : Type ℓ) : Typeω where
  constructor liftω
  field lowerω : A
open ↑ω_ public

private variable A : Type ℓ

↑ℓ-dec : Dec A → Dec (↑ℓ A {ℓ′})
↑ℓ-dec = Nullary.map′ lift lower

record _×ω_ (A B : Typeω) : Typeω where
  constructor _,ω_
  field
    projω₁ : A
    projω₂ : B
open _×ω_ public

¬ω_ : Typeω → Typeω
¬ω A = A → ⊥

_↔ω_ : Typeω → Typeω → Typeω
A ↔ω B = (A → B) ×ω (B → A)

data Decω (A : Typeω) : Typeω where
  yesω : A → Decω A
  noω  : ¬ω A → Decω A

Decω-map : ∀ {A B : Typeω} → A ↔ω B → Decω A → Decω B
Decω-map (f ,ω g) = λ where
  (yesω a) → yesω (f a)
  (noω ¬a) → noω (λ b → ¬a (g b))

↑ω-dec : ∀ {A : Type ℓ} → Dec A → Decω (↑ω A)
↑ω-dec = λ where
  (yes p) → yesω (liftω p)
  (no ¬p) → noω λ x → ¬p (lowerω x)

instance
  Lift-auto : ⦃ A ⦄ → ↑ℓ A {ℓ′}
  Lift-auto = lift it

  Liftω-auto : ⦃ A ⦄ → ↑ω A
  Liftω-auto = liftω it

private
  _ : Type 4ℓ ∋ ↑ℓ ⊤
  _ = lift tt

  -- _ : Typeω ∋ω ↑ω ⊤ -- Typeω₁ != Typeω ???
  -- _ = liftω tt

  _ : Typeω
  _ = ↑ω ⊤

  _ : ↑ω ⊤
  _ = liftω tt
