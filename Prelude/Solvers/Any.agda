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
open Debug ("Generics.Solvers.Any" , 100)

open import Prelude.Solvers.Base

module Prelude.Solvers.Any
  (newGoal : Type → TC Hole)
  (_:=_∋_ : THole → Type → TermCtx → TC ⊤)
  where

data ViewAny : Set where
  Any⦅_⦆ : Term × Term → ViewAny

viewAny : Term → Maybe ViewAny
viewAny = λ where
  (def (quote Any) as) → case vArgs as of λ where
    (P ∷ xs ∷ []) → just Any⦅ P , xs ⦆
    _ → nothing
  _ → nothing

data ViewList : Set where
  ∷⦅_,_⦆ : Term → Term → ViewList
  ++⦅_,_⦆ : Term → Term → ViewList

viewList : Term → Maybe ViewList
viewList = λ where
  (con (quote L._∷_) args) →
    case vArgs args of λ where
      (x ∷ xs ∷ []) → just ∷⦅ x , xs ⦆
      _ → nothing
  (def (quote _++_) args) →
    case vArgs args of λ where
      (xs ∷ ys ∷ []) → just ++⦅ xs , ys ⦆
      _ → nothing
  _ → nothing

solveAny : THole → ViewAny → TC ⊤
solveAny thole@(hole , ty) Any⦅ P , xs ⦆ = do
  print ">solveAny"
  xs ← normalise xs
  case viewList xs of λ where
    nothing → error $ "Not recognized: " ◇ show xs
    (just c) → case c of λ where
      ∷⦅ y , ys ⦆ → do
        printLn $ "Any? (" ◇ show P ◇ ") " ◇ show y ◇ " ∷ " ◇ show ys
        ty ← P -∙- y
        (thole := ty ∋ λ ◆ → quote Any.here ◆⟦ ◆ ⟧)
          <|> (thole := quote Any ∙⟦ P ∣ ys ⟧ ∋ λ ◆ → quote Any.there ◆⟦ ◆ ⟧)
      ++⦅ ys , zs ⦆ → do
        printLn $ "Any? (" ◇ show P ◇ ") " ◇ show ys ◇ " ++ " ◇ show zs
        (thole := quote Any ∙⟦ P ∣ ys ⟧ ∋ λ ◆ → quote L.Any.++⁺ˡ ∙⟦ ◆ ⟧)
          <|> (thole := quote Any ∙⟦ P ∣ zs ⟧ ∋ λ ◆ → quote L.Any.++⁺ʳ ∙⟦ ys ∣ ◆ ⟧)

Solver-Any : Solver
Solver-Any = λ where
  .View → ViewAny
  .view → viewAny
  .solveView → solveAny
