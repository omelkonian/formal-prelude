module Prelude.Lift where

open import Prelude.Init; open SetAsType
open import Prelude.General
open Lvl public using (Lift; lift; lower)

↑ℓ : Type ℓ → {ℓ′ : Level} → Type (ℓ ⊔ₗ ℓ′)
↑ℓ A {ℓ′} = Lvl.Lift ℓ′ A

record ↑ω_ (A : Type ℓ) : Typeω where
  constructor liftω
  field lowerω : A
open ↑ω_ public

private variable A : Type ℓ

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
