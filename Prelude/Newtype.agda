-- ** Emulating Haskell's newtype feature.
module Prelude.Newtype where

open import Prelude.Init; open SetAsType
open Fun.Inv using (_↔_; inverse)
open import Prelude.Functor

record newtype (A : Type ℓ) : Type ℓ where
  constructor mk
  field unmk : A
open newtype public

private variable A : Type ℓ

newtype¹ : Pred A ℓ → Pred A ℓ
newtype¹ P x = newtype (P x)

newtype² : Rel A ℓ → Rel A ℓ
newtype² _~_ x y = newtype (x ~ y)

newtype↔ : newtype A ↔ A
newtype↔ = inverse unmk mk (λ _ → refl) (λ _ → refl)

instance
  Functor-newtype : Functor newtype
  Functor-newtype ._<$>_ f = mk ∘ f ∘ unmk

mk-injective : ∀ (x y : A) → mk x ≡ mk y → x ≡ y
mk-injective _ _ refl = refl

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
