{-# OPTIONS --safe #-}
module Prelude.Decidable.Instances where

open import Prelude.Init; open SetAsType
open import Prelude.Decidable.Core
open import Prelude.DecEq.Core

private variable
  A : Type ℓ; B : Type ℓ′
  P¹ : Pred A ℓ″; P² : Rel A ℓ″

instance
  DecEq⇒Dec : ⦃ DecEq A ⦄ → _≡_ {A = A} ⁇²
  DecEq⇒Dec .dec = _ ≟ _

  -- Bool
  Dec-T : ∀ {t : Bool} → T t ⁇
  Dec-T .dec = T? _

  -- Maybe
  Dec-All : ⦃ P¹ ⁇¹ ⦄ → All P¹ ⁇¹
  Dec-All .dec = all? dec¹ _

  Dec-Any : ⦃ P¹ ⁇¹ ⦄ → Any P¹ ⁇¹
  Dec-Any .dec = any? dec¹ _

  Dec-AllPairs : ⦃ P² ⁇² ⦄ → AllPairs P² ⁇¹
  Dec-AllPairs .dec = allPairs? dec² _

  Dec-MAll : ⦃ _ : P¹ ⁇¹ ⦄ → M.All.All P¹ ⁇¹
  Dec-MAll .dec = M.All.dec dec¹ _

  Dec-MAny : ⦃ _ : P¹ ⁇¹ ⦄ → M.Any.Any P¹ ⁇¹
  Dec-MAny .dec = M.Any.dec dec¹ _
