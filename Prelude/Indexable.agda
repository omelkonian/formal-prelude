module Prelude.Indexable where

open import Prelude.Init
import Prelude.Lists as L

record Indexable (A : Set ℓ) (B : Set ℓ′) {ℓ″} : Set (lsuc (ℓ ⊔ₗ ℓ′ ⊔ₗ ℓ″)) where
  field Ix  : Pred A ℓ″
        _‼_ : (a : A) → Ix a → B
open Indexable ⦃...⦄ public

private variable A : Set ℓ

instance
  Index-List : Indexable (List A) A
  Index-List = λ where
    .Ix → L.Index
    ._‼_ → L._‼_

  Index-Vec : ∀ {n} → Indexable (Vec A n) A
  Index-Vec {n = n} = λ where
    .Ix _ → Fin n
    ._‼_ → V.lookup

_ = (List ℕ ∋ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ‼ 3F ≡ 3
  ∋ refl

_ = (Vec ℕ 5 ∋ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ‼ 3F ≡ 3
  ∋ refl
