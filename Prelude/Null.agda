module Prelude.Null where

open import Prelude.Init; open SetAsType
open import Prelude.Semigroup
open import Prelude.Monoid
open import Prelude.Decidable.Core

record Nullable (A : Type ℓ) {ℓ′ : Level} : Type (ℓ ⊔ₗ lsuc ℓ′) where
  field Null : Pred A ℓ′

  ¬Null : Pred A ℓ′
  ¬Null = ¬_ ∘ Null

  module _ ⦃ _ : Null ⁇¹ ⦄ where
    Null?  = Decidable¹ Null ∋ dec¹; Nullᵇ = isYes ∘ Null?
    ¬Null? = Decidable¹ ¬Null ∋ dec¹; ¬Nullᵇ = isYes ∘ ¬Null?
open Nullable ⦃...⦄ public

private variable A : Type ℓ

Monoid⇒Nullable : ⦃ _ : Semigroup A ⦄ → ⦃ Monoid A ⦄ → Nullable A
Monoid⇒Nullable = λ where .Null → _≡ ε

instance
  Nullable-List : Nullable (List A)
  Nullable-List = Monoid⇒Nullable

  Nullable-Vec : Nullable (∃ (Vec A))
  Nullable-Vec = Monoid⇒Nullable

  Nullable-String : Nullable String
  Nullable-String = Monoid⇒Nullable

  Nullable-Maybe : Nullable (Maybe A)
  Nullable-Maybe .Null = Is-nothing
