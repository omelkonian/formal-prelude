{-# OPTIONS --with-K #-}
open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Functor
open import Prelude.Bifunctor
open import Prelude.Semigroup
open import Prelude.Applicative
open import Prelude.Monad
open import Prelude.Show
open import Prelude.Nary
open import Prelude.Lists
open import Prelude.ToN

open import Prelude.Generics
open Meta
open Debug ("Generics.Solvers.Any" , 100)

open import Prelude.Solvers.Base

module Prelude.Solvers.Choice
  (newGoal : Type → TC Hole)
  (_:=_∋_ : THole → Type → TermCtx → TC ⊤)
  (_:=_∣_∋_ : THole → Type → Type → TermCtx² → TC ⊤)
  where

Choice = ℕ × String × Type × Type
Choices = List Choice

toSum : Type → Maybe (Type × Type)
toSum = λ where
  (def (quote _⊎_) as) → case vArgs as of λ where
    (A ∷ B ∷ []) → just (A , B)
    _ → nothing
  _ → nothing

choicesFromContext : TC Choices
choicesFromContext
  = mapMaybe (λ{ (i , (s , arg _ ty)) → (λ x → toℕ i , s , x) <$> toSum ty })
  ∘ enumerate <$> getContext

pattern _`⇒_ A B = vΠ[ "_" ∶ A ] B

choiceSolver : Solver
choiceSolver = λ where
  .View → Term
  .view → just
  .solveView thole@(_ , ty) t → do
    choices ← choicesFromContext
    print $ "Choices: " ◇ show choices
    ⋃∗ choices <&> λ (i , s , A , B) → do
      ctx ← getContext
      hA ← extendContext s (vArg A) $ print "LEFT: " >> newGoal ty
      hB ← extendContext s (vArg B) $ print "RIGHT: " >> newGoal ty
      unifyStrict thole $ quote Sum.[_,_]′ ∙⟦ hA ∣ hB ∣ ♯ i ⟧
      -- thole := (A `⇒ C) ∣ (B `⇒ C) ∋ λ ◆ ◇ → quote Sum.[_,_]′ ∙⟦ ◆ ∣ ◇ ∣ ♯ i ⟧
