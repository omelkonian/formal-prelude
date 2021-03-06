module Prelude.Anyable where

open import Prelude.Init hiding (Any)

record Anyable (F : Set ℓ → Set ℓ) : Set (lsuc ℓ) where
  field
    Any : ∀ {A} → Pred₀ A → F A → Set ℓ

  syntax Any P xs = ∃[∈ xs ] P
  Any′ = Any
  syntax Any′ (λ x → P) xs = ∃[ x ∈ xs ] P

open Anyable ⦃ ... ⦄ public

instance
  Anyable-List : Anyable {ℓ} List
  Anyable-List .Any = L.Any.Any

private
  open import Prelude.Nary

  _ : ∃[ x ∈ ⟦ 1 ,  2 , 3 ⟧ ] (x ≡ 2)
  -- [BUG] unresolved metas...
  -- _ = there $ here refl
  -- ... but this works
  _ = there (here refl)
