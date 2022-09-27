module Prelude.SerializableBitstring where

open import Prelude.Init
open import Prelude.Bitstring
open import Prelude.ToN
open import Prelude.FromN
open import Prelude.Applicative

open import Prelude.Serializable Bitstring public

instance
  Serializable-ℕ : Serializable ℕ
  Serializable-ℕ .encode = fromℕ
  Serializable-ℕ .encode-injective = fromℕ-injective
  Serializable-ℕ .decode = pure ∘ toℕ
  Serializable-ℕ .encode-decode m x .proj₁ refl
    = sym $ fromℕ∘toℕ m
  Serializable-ℕ .encode-decode m x .proj₂ refl
    = cong just $ toℕ∘fromℕ x

{-
open import Prelude.Semigroup
open import Prelude.Functor
open import Prelude.Measurable
open import Prelude.Monad

private variable
  a b : Level
  A : Set a
  B : Set b

instance
  Serializable-⊎ : ⦃ Serializable A ⦄ → ⦃ Serializable B ⦄ → Serializable (A ⊎ B)
  Serializable-⊎ .encode = λ where
    (inj₁ a) → fromBits $ 0b ∷ toBits (encode a)
    (inj₂ b) → fromBits $ 1b ∷ toBits (encode b)
  Serializable-⊎ .encode-injective {inj₁ x} {inj₁ x₁} eq = {!!}
  Serializable-⊎ .encode-injective {inj₁ x} {inj₂ y} eq = {!!}
  Serializable-⊎ .encode-injective {inj₂ y} {inj₁ x} eq = {!!}
  Serializable-⊎ .encode-injective {inj₂ y} {inj₂ y₁} eq = {!!}
  Serializable-⊎ .decode = toBits >≡> λ where
    [] → nothing
    (0b ∷ bs) → inj₁ <$> decode (fromBits bs)
    (1b ∷ bs) → inj₂ <$> decode (fromBits bs)
  Serializable-⊎ .encode-decode m x .proj₁ = {!!}
  Serializable-⊎ .encode-decode m x .proj₂ = {!!}

  Serializable-× : ⦃ Serializable A ⦄ → ⦃ Serializable B ⦄ → Serializable (A × B)
  Serializable-× .encode (a , b) =
    let
      𝕒 = encode a
      𝕓 = encode b
    in
      encode ∣ 𝕒 ∣ ◇ 𝕒 ◇ 𝕓
  Serializable-× .encode-injective {x} {y} eq = {!!}

  Serializable-× .decode m = {!!}
  -- Serializable-× .decode m = do
  --   let ∣a∣ , m′ = L.splitAt ? m
  --   n ← decode ∣a∣
  --   let 𝕒 , 𝕓 = L.splitAt n m′
  --   a ← decode 𝕒
  --   b ← decode 𝕓
  --   return (a , b)

  Serializable-× .encode-decode m x .proj₁ = {!!}
  Serializable-× .encode-decode m x .proj₂ = {!!}

private
  instance
    postulate Serializable-String : Serializable String

  data X : Set where
    mk₁ : ℕ → X
    mk₂ : String → X

  instance
    Serializable-X : Serializable X
    Serializable-X .encode = λ where
      (mk₁ n) → encode {A = ℕ ⊎ String} (inj₁ n)
      (mk₂ s) → encode {A = ℕ ⊎ String} (inj₂ s)
    Serializable-X .encode-injective = {!!}
    Serializable-X .decode
      = decode {A = ℕ ⊎ String} >≡> fmap (λ where (inj₁ n) → mk₁ n; (inj₂ s) → mk₂ s)
    Serializable-X .encode-decode m x = λ where
      .proj₁ → {!!}
      .proj₂ → {!!}
-}
