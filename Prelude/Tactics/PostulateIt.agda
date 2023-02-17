{-# OPTIONS --with-K #-}
module Prelude.Tactics.PostulateIt where

open import Prelude.Init
open Meta
open import Prelude.Generics
open import Prelude.Monad
open import Prelude.Semigroup
open import Prelude.Show

genPostulate : Type → TC Name
genPostulate ty = do
  n ← freshName $ "postulate[" ◇ show ty ◇ "]"
  declarePostulate (vArg n) ty
  return n

macro
  postulateIt : Hole → TC ⊤
  postulateIt hole = do
    n ← genPostulate =<< inferType hole
    unify hole (n ∙)

private
  UIP : ∀ {A : Set ℓ} {x x′ : A} (p p′ : x ≡ x′) → p ≡ p′
  UIP = postulateIt

  _ : ∀ {n m : ℕ} (p p′ : n ≡ m) → p ≡ p′
  _ = UIP {A = ℕ}
