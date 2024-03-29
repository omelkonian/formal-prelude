-------------------------------------------------
-- Deriving à la Haskell
-------------------------------------------------

{-# OPTIONS --safe #-}
module Prelude.Generics.Deriving where

open import Prelude.Init; open Meta
open import Prelude.Functor
open import Prelude.Monad
open import Prelude.Lift
open import Prelude.General
open import Prelude.FromList; open import Prelude.ToList

open import Prelude.Generics.Core

Derivation : ℕ → Set
Derivation n =
  List ( Name       -- name of the type to derive an instance for
       × (Name ^ n) -- identifiers of the function/instances to generate
       )
       → TC ⊤ -- computed instance to unquote

record Derivable (F : String) (n : ℕ) : Setω where
  field derive : Derivation (Nat.pred n)
open Derivable ⦃...⦄ public

private
  isOmegaKind : Type → Bool
  isOmegaKind = λ where
    (agda-sort s) → case s of λ where
      (inf _) → true
      _ → false
    _ → false

  `ωkindOf : Term → TC Type
  `ωkindOf e = do
    ty ← inferType e
    ki ← inferType ty
    return $
      if isOmegaKind ki then ty
      else quote ↑ω_ ∙⟦ ty ⟧

  removeQualifiers : String → String
  removeQualifiers = fromList
                   ∘ L.reverse ∘ takeWhile (¬? ∘ ('.' Ch.≟_)) ∘ L.reverse
                   ∘ toList

  `toString : Name → Term
  `toString = lit ∘′ string ∘ removeQualifiers ∘ Meta.Show.showName

macro
  DERIVE : Name → Tactic
  DERIVE n hole = do
    ty ← `ωkindOf =<< getType n
    unify hole $ def (quote derive) [ hArg (`toString n) ]

  DERIVABLE : Name → Tactic
  DERIVABLE n = flip unify (quote Derivable ∙⟦ `toString n ⟧)

private
  record X₀ (A : Set) : Set where
    field x₀ : A
  open X₀ ⦃...⦄

  record X (A : Set ℓ) : Set ℓ where
    field x : A
  open X ⦃...⦄

  record Y₀ (A : Set) ⦃ _ : X₀ A ⦄ : Set where
    field eq₀ : x₀ ≡ x₀
  open Y₀ ⦃...⦄

  record Y (A : Set ℓ) ⦃ _ : X A ⦄ : Set ℓ where
    field eq : x ≡ x
  open Y ⦃...⦄

  record ∅ : Set where
  open ∅ ⦃...⦄

  _ : ∀ {ℓ} → Set ℓ → Set ℓ
  _ = X

  _ : ∀ {ℓ} → (A : Set ℓ) ⦃ _ : X A ⦄ → Set ℓ
  _ = Y

  _ : Set
  _ = ∅

  instance
    _ : DERIVABLE X 1
    _ = λ where .derive → λ where
      ((n , f) ∷ []) → do
        declareDef (vArg f) (n ∙)
        defineFun f [ clause [] [] (lit $′ nat 0) ]
      _ → return tt

  unquoteDecl X-ℕ = DERIVE X [ quote ℕ , X-ℕ ]
  _ : ℕ
  _ = X-ℕ

  module _
    ⦃ _ : DERIVABLE Y 1 ⦄
    ⦃ _ : DERIVABLE X₀ 1 ⦄
    ⦃ _ : DERIVABLE Y₀ 1 ⦄
    ⦃ _ : DERIVABLE ∅ 0 ⦄
    where
    _ : List (Derivation 0)
    _ = DERIVE X
      ∷ DERIVE Y
      ∷ DERIVE X₀
      ∷ DERIVE Y₀
      ∷ DERIVE ∅
      ∷ []
