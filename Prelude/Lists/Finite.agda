------------------------------------------------------------------------
-- Finite sets witnessed by a bijection with natural numbers.
------------------------------------------------------------------------
{-# OPTIONS --safe #-}
open import Prelude.Init; open SetAsType

module Prelude.Lists.Finite where

private variable A : Type ℓ

Finite : Type ℓ → Type ℓ
Finite A = ∃[ n ] (A Fun.↔ Fin n)

finList : Finite A → List A
finList (n , record {f⁻¹ = Fin→A }) = map Fin→A (allFin n)

≡-findec : Finite A → Decidable² {A = A} _≡_
≡-findec (_ , record { f = toFin; f⁻¹ = fromFin; cong₂ = cong′; inverse = _ , invˡ }) x y
  with toFin x F.≟ toFin y
... | yes x≡y = yes (begin x                 ≡⟨ sym (invˡ x) ⟩
                           fromFin (toFin x) ≡⟨ cong′ x≡y ⟩
                           fromFin (toFin y) ≡⟨ invˡ y ⟩
                           y ∎)
                where open ≡-Reasoning
... | no  x≢y = no λ{ refl → x≢y refl }
