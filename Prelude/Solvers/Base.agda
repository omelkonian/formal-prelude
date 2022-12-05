module Prelude.Solvers.Base where

open import Prelude.Init
open import Prelude.Functor
open import Prelude.Semigroup
open import Prelude.Applicative
open import Prelude.Monad
open import Prelude.Show

open import Prelude.Generics
open Meta
open Debug ("Generics.Solvers" , 100)

record Solver : Set₁ where
  field
    View : Set
    view : Term → Maybe View
    solveView : THole → View → TC ⊤

  solveM : Hole → TC ⊤
  solveM hole = do
    ty ← reduce =<< normalise =<< inferType hole
    case view ty of λ where
      (just v) → solveView (hole , ty) v
      nothing  → errorP $ "View failed: " ◇ show ty

open Solver public

Hints = List Term
THints = List TTerm

hintsFromContext : TC THints
hintsFromContext = go 0 <$> getContext --′
  where
    go : ℕ → List (String × Arg Type) → List TTerm
    go _ [] = []
    go n ((_ , arg (arg-info v r) ty) ∷ as) = (var n [] , ty) ∷ go (suc n) as

hintSolver : Hints → Solver
hintSolver hints = λ where
  .View → Term
  .view → just
  .solveView thole t → do
    thints ← hintsFromContext
    ⋃∗ unifyStrict thole <$> (hints ++ map proj₁ thints)

TermCtx = Term → Term
mkTermCtx = id
syntax mkTermCtx (λ x → f) = ⟪ x ∣ f ⟫

_:=_∋_via_ : THole → Type → TermCtx → (Hole → TC ⊤) → TC ⊤
thole := ty ∋ ctx via solver = do
  print $ "=? " ◇ show (ctx $ lit $′ char '◆')
  printLn $ "  where ◆ : " ◇ show ty
  unifyStrict thole =<< ctx <$> withHole ty solver

TermCtx² = Term → Term → Term

_:=_∣_∋_via_ : THole → Type → Type → TermCtx² → (Hole → TC ⊤) → TC ⊤
thole := ty₁ ∣ ty₂ ∋ ctx via solver = do
  print $ "=? " ◇ show (ctx (lit $′ char '◆') (lit $′ char '◇'))
  printLn $ "  where ◆ : " ◇ show ty₁
  printLn $ "  where ◇ : " ◇ show ty₂
  unifyStrict thole =<< ctx <$> withHole ty₁ solver <*> withHole ty₂ solver
