module Prelude.Null where

open import Prelude.Init
open import Prelude.Monoid
open import Prelude.Decidable.Base

record Nullable (A : Set ℓ) : Set (lsuc ℓ) where
  field Null : Pred A ℓ

  ¬Null : Pred A ℓ
  ¬Null = ¬_ ∘ Null

  Null? : ⦃ _ : Null ⁇¹ ⦄ → Decidable¹ Null
  Null? = dec¹

  ¬Null? : ⦃ _ : Null ⁇¹ ⦄ → Decidable¹ ¬Null
  ¬Null? = dec¹
open Nullable ⦃...⦄ public

private variable A : Set ℓ

Monoid⇒Nullable : ⦃ Monoid A ⦄ → Nullable A
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
