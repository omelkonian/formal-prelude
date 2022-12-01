module Prelude.Setoid.Maybe where

open import Prelude.Init; open SetAsType
open import Prelude.Setoid

private variable A : Type ℓ

instance
  Setoid-Maybe : ⦃ ISetoid A ⦄ → ISetoid (Maybe A)
  Setoid-Maybe .relℓ = _
  Setoid-Maybe ._≈_ = λ where
    nothing nothing → Lvl.Lift _ ⊤
    nothing (just _) → Lvl.Lift _ ⊥
    (just _) nothing → Lvl.Lift _ ⊥
    (just x) (just y) → x ≈ y

  SetoidLaws-Maybe : -- ⦃ _ : LawfulSetoid A ⦄
    ⦃ _ : ISetoid A ⦄ ⦃ _ : SetoidLaws A ⦄
    → SetoidLaws (Maybe A)
  SetoidLaws-Maybe .isEquivalence = record
    { refl  = λ where
      {just x}  → ≈-refl {x = x}
      {nothing} → Lvl.lift tt
    ; sym   = λ where
      {just x}  {just y}  → ≈-sym {x = x}{y}
      {just _}  {nothing} → id
      {nothing} {just _}  → id
      {nothing} {nothing} → id
    ; trans = λ where
      {just x}  {just y}  {just z}  p q → ≈-trans {i = x}{y}{z} p q
      {nothing} {nothing} {nothing} p _ → p
    }
