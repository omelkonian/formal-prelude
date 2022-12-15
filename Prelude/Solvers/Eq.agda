{-# OPTIONS --with-K #-}
open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Functor
open import Prelude.Semigroup
open import Prelude.Applicative
open import Prelude.Monad
open import Prelude.Show
open import Prelude.Nary

open import Prelude.Generics
open Meta
open Debug ("Generics.Solvers.Eq" , 100)

open import Prelude.Solvers.Base

module Prelude.Solvers.Eq
  (newGoal : Type → TC Hole)
  (_:=_∋_ : THole → Type → TermCtx → TC ⊤)
  where

data ViewEq : Set where
  _`≡_ : Term → Term → ViewEq

viewEq : Term → Maybe ViewEq
viewEq = λ where
  (def (quote _≡_) (hArg _ ∷ hArg _ ∷ vArg x ∷ vArg y ∷ [])) → just (x `≡ y)
  _ → nothing

solveEq : THole → ViewEq → TC ⊤
solveEq (hole , _) (x `≡ y) = do
  print $ show x ◇ " =? " ◇ show y
  x ← normalise x
  y ← normalise y
  print $ " ↝ " ◇ show x ◇ " =? " ◇ show y
  tryEq (x , y) <|> decideEq (x , y)
  where
    decideEq : Term × Term → TC ⊤
    decideEq (x , y) = do
      let x≡y = quote _≡_ ∙⟦ x ∣ y ⟧
      let x≟y = quote _≟_ ∙⟦ x ∣ y ⟧
      unifyStrict (hole , x≡y) $ def (quote toWitness) (hArg? ∷ hArg x≡y ∷ hArg x≟y ∷ vArg (quote tt ◆) ∷ [])
      printLn $ "[by-dec] " ◇ show x ◇ " ≟ " ◇ show y

    tryEq : Term × Term → TC ⊤
    tryEq (x , y) =
      if x == y then (do
        printLn "[by-refl] terms are exactly equal"
        unifyStrict (hole , quote _≡_ ∙⟦ x ∣ y ⟧) (quote refl ◆)
        )
      -- else if == swap
      --   print "tryEq: terms are swapped, applying commutativity..."
      --   ...
      else error "tryEq: terms are not exactly equal, cannot apply reflexivity"

Solver-Eq : Solver
Solver-Eq = λ where
  .View → ViewEq
  .view → viewEq
  .solveView → solveEq
