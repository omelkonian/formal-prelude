module Prelude.LiftOmega where

open import Prelude.Init; open SetAsType

record Liftω (A : Type ℓ) : Typeω where
  field ⦃ lower ⦄ : A
open Liftω ⦃...⦄
syntax Liftω A = ↑ A

private variable A : Type ℓ

instance
  Lift-auto : ⦃ A ⦄ → Lvl.Lift ℓ′ A
  Lift-auto = Lvl.lift it

  Liftω-auto : ⦃ A ⦄ → Liftω A
  Liftω-auto = record {}
