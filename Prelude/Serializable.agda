module Prelude.Serializable (DATA : Set) where

open import Prelude.Init
open import Prelude.InferenceRules

record Serializable (A : Set) : Set where
  field
    encode : A → DATA
    encode-injective : Injective≡ encode

    decode : DATA → Maybe A
    encode-decode : ∀ m x →
      decode m ≡ just x
      ═════════════════
      m ≡ encode x

  decode′ : ∀ m → Dec (∃ λ (x : A) → m ≡ encode x)
  decode′ m
    with decode m in m≡
  ... | just x
    = yes (x , encode-decode m x .proj₁ m≡)
  ... | nothing
    = no λ (x , x≡) → case trans (sym $ encode-decode m x .proj₂ x≡) m≡ of λ ()
open Serializable ⦃...⦄ public

decode_as_ : DATA → (A : Set) → ⦃ Serializable A ⦄ → Maybe A
decode m as A = decode {A = A} m

decode′_as_ : ∀ (m : DATA) (A : Set) ⦃ _ : Serializable A ⦄
  → Dec (∃ λ (x : A) → m ≡ encode x)
decode′ m as A = decode′ {A = A} m
