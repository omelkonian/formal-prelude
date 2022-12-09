-- ** Emulating Haskell's newtype feature.
module Prelude.Newtype where

import Relation.Nullary.Decidable as Dec

open import Prelude.Init; open SetAsType
open Fun.Inv using (_↔_; inverse)
open import Prelude.Functor

record newtype (A : Type ℓ) : Type ℓ where
  constructor mk
  field unmk : A
open newtype public

private variable
  A : Type ℓ
  P : Pred A ℓ′
  R : Rel A ℓ′

instance
  Functor-newtype : Functor newtype
  Functor-newtype ._<$>_ f = mk ∘ f ∘ unmk

  mkNewtype : ⦃ A ⦄ → newtype A
  mkNewtype = mk it

mk-injective : ∀ (x y : A) → mk x ≡ mk y → x ≡ y
mk-injective _ _ refl = refl

newtype¹ : Pred A ℓ → Pred A ℓ
newtype¹ P x = newtype (P x)

newtype² : Rel A ℓ → Rel A ℓ
newtype² _~_ x y = newtype (x ~ y)

newtype↔ : newtype A ↔ A
newtype↔ = inverse unmk mk (λ _ → refl) (λ _ → refl)

mk? : Dec A → Dec (newtype A)
mk? = Dec.map′ mk unmk

unmk? : Dec (newtype A) → Dec A
unmk? = Dec.map′ unmk mk

mk?¹ : Decidable¹ P → Decidable¹ (newtype¹ P)
mk?¹ P? x = mk? (P? x)

unmk?¹ : Decidable¹ (newtype¹ P) → Decidable¹ P
unmk?¹ P? x = unmk? (P? x)

mk?² : Decidable² R → Decidable² (newtype² R)
mk?² R? x y = mk? (R? x y)

unmk?² : Decidable² (newtype² R) → Decidable² R
unmk?² R? x y = unmk? (R? x y)

private
  ℕ˘ = newtype ℕ

  _+˘_ : Op₂ ℕ˘
  n +˘ m = case unmk m of λ where
    0        → n
    (suc m′) → suc <$> (n +˘ mk m′)

  +˘-identityˡ : ∀ x → mk 0 +˘ x ≡ x
  +˘-identityˡ (mk 0)       = refl
  +˘-identityˡ (mk (suc n)) rewrite +˘-identityˡ (mk n) = refl

  H˘ : ∀ {n : ℕ˘} → n +˘ mk 0 ≡ n
  H˘ = refl

  H˘′ : ∀ {n : ℕ} → mk n +˘ mk 0 ≡ mk n
  H˘′ = H˘

  +↔+˘ : ∀ (x y : ℕ) → x + y ≡ (mk x +˘ mk y) .unmk
  +↔+˘ zero y rewrite +˘-identityˡ (mk y) = refl
  +↔+˘ (suc x) zero    = cong suc (Nat.+-identityʳ x)
  +↔+˘ (suc x) (suc y) = cong suc (trans (Nat.+-suc x y) (+↔+˘ (suc x) y))

  H : ∀ {n : ℕ} → n + 0 ≡ n
  H = trans (+↔+˘ _ 0) (cong unmk H˘′)

-- T0D0: tactic to automate "newtype" transports
