module Prelude.Traces where

open import Prelude.Init
open import Prelude.Closures
open import Prelude.Decidable
open import Prelude.Setoid
open import Prelude.General
open import Prelude.Validity

-- Well-rooted traces.

record HasInitial (A : Set ℓ) : Set (1ℓ ⊔ₗ ℓ) where
  field Initial : Pred₀ A

  Initial? : ⦃ Initial ⁇¹ ⦄ → Decidable¹ Initial
  Initial? = dec¹
open HasInitial ⦃ ... ⦄ public

module _ {A : Set ℓ} ⦃ _ : HasInitial A ⦄ (_—↠_ : Rel A ℓ′) where

  record Trace : Set (ℓ ⊔ₗ ℓ′) where
    field
      start end : A
      trace : start —↠ end
      -- .init : Initial start
      init : Initial start
  open Trace public

  -- mapTrace : (A → A) → (L → L)


{-
module _ {A : Set ℓ} {L} ⦃ _ : HasInitial A ⦄ (_—[_]↠_ : LRel (A , List L) ℓ′) where

  record Trace : Set (ℓ ⊔ₗ ℓ′) where
    field
      start end : A
      labels : List L
      trace : start —[ labels ]↠ end
      .init : Initial start
  open Trace public
-}

{-
record Traceable (R : ∀ {ℓ} → Set ℓ → (ℓ′ : Level) → Set (ℓ ⊔ₗ lsuc ℓ′)) : Set ? where
  field
  --     {ℓ′} : Level
  --     Trace : Set ℓ

instance
  TRel : Traceable Rel
  TRel = ?

  TLRel : Traceable (λ A → LRel (A , L)
  TLRel = ?


module _ {A : Set ℓ} {L} ⦃ _ : HasInitial A ⦄ where

  record Trace : Set (ℓ ⊔ₗ ℓ′) where
    field
      start end : A
      labels : List L
      trace : ?
      .init : Initial start
  open Trace public
-}

{-
module ReflTrans {A : Set ℓ} ⦃ _ : HasInitial A ⦄ (_—→_ : Rel A ℓ) where

  open ReflexiveTransitiveClosure _—→_

  record Trace : Set ℓ where
    field
      start end : A
      trace : start —↠ end
      .init : Initial start

  open Trace public

module LReflTrans {A : Set ℓ} {L : Set} ⦃ _ : HasInitial A ⦄ (_—[_]→_ : LRel (A , L) ℓ) where

  open LabelledReflexiveTransitiveClosure _—[_]→_

  record Trace : Set ℓ where
    field
      start end : A
      trace : start —↠ end
      .init : Initial start

  open Trace public

module UpToLReflTrans {A : Set ℓ} {L : Set} ⦃ i : HasInitial A ⦄ (_—[_]→_ : LRel (A , L) ℓ) ⦃ _ : ISetoid A ⦄ where

  open UpToLabelledReflexiveTransitiveClosure _—[_]→_

  record Trace : Set ℓ where
    field
      start end : A
      trace : start —↠ end
      .init : Initial start
  open Trace public

  -- data Trace′ : Set ℓ where
  --     _∙     : (x : A) → Trace′
  --     _∷⟦_⟧_ : A → L → Trace′ → Trace′

  -- end′ : Trace′ → A
  -- end′ (x ∙) = x
  -- end′ (_ ∷⟦ _ ⟧ tr) = end′ tr

  -- instance
  --   𝕍Trace : Validable Trace′
  --   𝕍Trace .Valid = λ where
  --     (x ∙) → Initial x
  --     (x ∷⟦ α ⟧ tr) → {!!} × Valid tr

  -- Trace∼Trace′ : Trace ↔ Σ Trace′ Valid
  -- Trace∼Trace′ = h , {!!}
  --   where
  --     h : Trace → Σ Trace′ Valid
  --     h (record {start = s; end = e; trace = tr; init = init}) = case tr of λ where
  --       (.[]      , (.s ∎)) → (s ∙) , {!init!}
  --       (.(_ ∷ _) , (.s —→⟨ x ⟩ x₁ ⊢ snd)) → {!!}

-}
