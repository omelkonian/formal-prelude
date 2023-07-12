{-# OPTIONS -v auto:100 --with-K #-}
module Prelude.Tactics.Auto where

open import Prelude.Init
open Meta
open import Prelude.Generics
open import Prelude.Functor
open import Prelude.Monad
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Membership

open Debug ("auto" , 100)
open import Prelude.Show
open import Prelude.Semigroup

macro
  ¡_ : Term → Tactic
  (¡ f) hole = do
    ty ← normalise =<< inferType f
    let n = (length ∘ vArgs ∘ proj₁ ∘ viewTy′) ty
    f′ ← f -∗- L.replicate n (quote auto ∙)
    unify hole f′

  ‼_ : Name → Tactic
  (‼ f) hole = do
    ty ← normalise =<< getType f
    let n = length $ vArgs $ viewTy′ ty .proj₁
    let as = L.replicate n (vArg $ quote auto ∙)
    unify hole $ con f as

private

  -- ** function
  open import Prelude.Nary

  f : ∀ {x : ℕ } {xs : List ℕ}
    → xs ≡ ⟦ 1 , 2 , 3 ⟧
    → x ∈ xs
      --————————————————
    → ⊤
  f _ _ = tt

  _ : ⊤
  -- _ = f {x = 2} {xs = ⟦ 1 , 2 , 3 ⟧} auto auto
  _ = ¡ f {x = 2} {xs = ⟦ 1 , 2 , 3 ⟧}

  -- ** datatypes
  open import Prelude.InferenceRules

  data _~_ : ℕ → List ℕ → Set where
    C : ∀ {x : ℕ } {xs : List ℕ} →
      ∙ xs ≡ ⟦ 1 , 2 , 3 ⟧
      ∙ x ∈ xs
        ────────────────────
        x ~ xs

  _ : 2 ~ ⟦ 1 , 2 , 3 ⟧
  -- _ = C auto auto
  _ = ‼ C
