{-# OPTIONS --with-K #-}
{-# OPTIONS -v mu:100 #-}
module Prelude.Tactics.Mu where

open import Prelude.Init
open Meta
open import Prelude.Generics
open Debug ("mu" , 100)
open import Prelude.Monad
open import Prelude.Show
open import Prelude.Semigroup
open import Prelude.Functor
open import Prelude.DecEq

private
  ex : ℕ → ℕ
  ex = go where go = λ where
    0 → 0
    (suc n) → 10 + go n

private
  {-# TERMINATING #-}
  replaceName : Name → Name → Op₁ Term
  replaceName n n′ = go where go = λ where
    (var x as) → var x (map (fmap go) as)
    (con c as) → con (replace c) (map (fmap go) as)
    (def f as) → def (replace f) (map (fmap go) as)
    (lam v t)  → lam v (go <$> t)
    (pat-lam cs as) → pat-lam (map goCls cs) (map (fmap go) as)
    (pi a b) → pi (go <$> a) (go <$> b)
    t → t
     where
      replace : Op₁ Name
      replace x = if x == n then n′ else x

      goCls : Op₁ Clause
      goCls = λ where
        (clause tel ps t) → clause tel ps (go t)
        c@(absurd-clause _ _) → c

macro
  μ_⇒_ : ∀ {A : Set} → Name → A → Tactic
  (μ f ⇒ `t) hole = do
    t ← quoteTC `t
    local-f ← freshName ""
    ty ← getType f
    genSimpleDef local-f ty (replaceName f local-f t)
    unify hole (local-f ∙)

private
  $ex : ℕ → ℕ
  $ex = μ $ex ⇒ λ where
    0 → 0
    (suc n) → 10 + $ex n
