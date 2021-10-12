{-# OPTIONS -v eta:100 #-}
module Prelude.Tactics.Eta where

open import Prelude.Init
open Meta
open import Prelude.Generics
open Debug ("eta" , 100)
open import Prelude.Functor
open import Prelude.Monad
open import Prelude.Show
open import Prelude.Semigroup
open import Prelude.ToN
open import Prelude.Lists

saturate : Term → Args Type → TC Term
saturate f as = case f of λ where
  (def c as′) → return $ def c (as′ ++ as)
  _           → error $ "cannot saturate arbitrary expressions, only definitions"

macro
  η : Term → Hole → TC ⊤
  η f hole = do
    print "*****************************"
    print $ "f: " ◇ show f
    ty ← inferType f -- =<< reduce f
    print $ "ty: " ◇ show ty
    let as , _ = viewTy′ ty
    print $ "as: " ◇ show as
    f′ ← saturate f $ map (λ{ (n , arg i _) → arg i (♯ (length as ∸ suc (toℕ n)))}) (enumerate as)
    print $ "f′: " ◇ show f′
    unify hole $ foldr (λ x t → Π[ "_" ∶ x ] t) f′ as

private
  p : Set
  p = ∀ {n} → Fin n

  ∀p : ∀ {n} → Set
  ∀p {n} = Fin n

  _ : Set
  _ = η ∀p

  ∀kp : ∀ (m : ℕ) {n} → Set
  ∀kp _ {n} = Fin n

  _ : Set
  _ = η (∀kp 0)

  ∀k2p : ∀ (m : ℕ) {k : ℕ} {n} → Set
  ∀k2p _ {n = n} = Fin n

  _ : Set
  _ = η (∀k2p 0 {1})
