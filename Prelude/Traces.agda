module Prelude.Traces where

open import Prelude.Init; open SetAsType
open import Prelude.Closures
open import Prelude.Decidable
open import Prelude.Setoid
open import Prelude.General
open import Prelude.Validity

-- Well-rooted traces.

record HasInitial (A : Type ℓ) : Type (1ℓ ⊔ₗ ℓ) where
  field Initial : Pred₀ A

  Initial? : ⦃ Initial ⁇¹ ⦄ → Decidable¹ Initial
  Initial? = dec¹
open HasInitial ⦃...⦄ public

module _ {A : Type ℓ} ⦃ _ : HasInitial A ⦄ (_—↠_ : Rel A ℓ′) where

  record Trace : Type (ℓ ⊔ₗ ℓ′) where
    field
      start end : A
      trace : start —↠ end
      -- .init : Initial start
      init : Initial start
  open Trace public

  -- mapTrace : (A → A) → (L → L)


{-
module _ {A : Type ℓ} {L} ⦃ _ : HasInitial A ⦄ (_—[_]↠_ : LRel (A , List L) ℓ′) where

  record Trace : Type (ℓ ⊔ₗ ℓ′) where
    field
      start end : A
      labels : List L
      trace : start —[ labels ]↠ end
      .init : Initial start
  open Trace public
-}

{-
record Traceable (R : ∀ {ℓ} → Type ℓ → (ℓ′ : Level) → Type (ℓ ⊔ₗ lsuc ℓ′)) : Type ? where
  field
  --     {ℓ′} : Level
  --     Trace : Type ℓ

instance
  TRel : Traceable Rel
  TRel = ?

  TLRel : Traceable (λ A → LRel (A , L)
  TLRel = ?


module _ {A : Type ℓ} {L} ⦃ _ : HasInitial A ⦄ where

  record Trace : Type (ℓ ⊔ₗ ℓ′) where
    field
      start end : A
      labels : List L
      trace : ?
      .init : Initial start
  open Trace public
-}

{-
module ReflTrans {A : Type ℓ} ⦃ _ : HasInitial A ⦄ (_—→_ : Rel A ℓ) where

  open ReflexiveTransitiveClosure _—→_

  record Trace : Type ℓ where
    field
      start end : A
      trace : start —↠ end
      .init : Initial start

  open Trace public

module LReflTrans {A : Type ℓ} {L : Type} ⦃ _ : HasInitial A ⦄ (_—[_]→_ : LRel (A , L) ℓ) where

  open LabelledReflexiveTransitiveClosure _—[_]→_

  record Trace : Type ℓ where
    field
      start end : A
      trace : start —↠ end
      .init : Initial start

  open Trace public

module UpToLReflTrans {A : Type ℓ} {L : Type} ⦃ i : HasInitial A ⦄ (_—[_]→_ : LRel (A , L) ℓ) ⦃ _ : ISetoid A ⦄ where

  open UpToLabelledReflexiveTransitiveClosure _—[_]→_

  record Trace : Type ℓ where
    field
      start end : A
      trace : start —↠ end
      .init : Initial start
  open Trace public

  -- data Trace′ : Type ℓ where
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
