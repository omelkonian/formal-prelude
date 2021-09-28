{-# OPTIONS -v Generics.Solvers:100 #-}
module Prelude.Solvers where

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
open Debug ("Generics.Solvers" , 100)

open import Prelude.Solvers.Base
open import Prelude.Tactics.Intro

mutual
  newGoal : Hints → Type → TC Hole
  newGoal hints ty = withHole ty (solve′ hints)

  {-# TERMINATING #-}
  solve′ : Hints → Hole → TC ⊤
  solve′ hints hole = do
    print "****************************"
    printLn $ "Hints: " ◇ show hints
    printCurrentContext
    print "****************************"
    ty ← inferType hole
    let holeInfo = show hole ◇ " : " ◇ show ty
    printLn $ "≫≫≫≫≫≫≫≫≫≫≫≫≫≫≫≫≫≫≫≫ " ◇ holeInfo
    ⋃⁺ callSolver <$> solvers
    printLn $ "≪≪≪≪≪≪≪≪≪≪≪≪≪≪≪≪≪≪≪≪ " ◇ holeInfo
    where
      callSolver : String × Solver → TC ⊤
      callSolver (n , s) = do
        printLn $ ">solve" ◇ show n
        solveM s hole

      newGoalRec = newGoal hints
      _:=_∋_     = _:=_∋_via (solve′ hints)
      _:=_∣_∋_   = _:=_∣_∋_via (solve′ hints)

      open import Prelude.Solvers.Any newGoalRec _:=_∋_
      open import Prelude.Solvers.Eq  newGoalRec _:=_∋_
      open import Prelude.Solvers.Choice newGoalRec _:=_∋_ _:=_∣_∋_

      solvers =
        ( ("Eq" , Solver-Eq)
        ∷ ("Any" , Solver-Any)
        ∷ ("Hints" , hintSolver hints)
        -- ∷ ("Choices" , choiceSolver)
        ∷ [])

macro
  solve : Hole → TC ⊤
  solve hole = intros hole (solve′ [])

  solveWith : Hints → Hole → TC ⊤
  solveWith hints hole = intros hole (solve′ hints)

{-
open L.Mem

macro
  `∈-++⁺ʳ : ∀ {A : Set} {x : A} {xs} → x ∈ xs → Tactic
  `∈-++⁺ʳ x∈ hole = do
    ty ← inferType hole
    `x∈ ← quoteTC x∈
    let err = error $ "`∈-++⁺ʳ: expression " ◇ show ty ◇ " is not of the form _ ∈ _ ++ _"
    case ty of λ where
      (def (quote L.Mem._∈_) as) → case vArgs as of λ where
        (x ∷ xs₀ ∷ []) → case xs₀ of λ where
          (def (quote _++_) args) → case vArgs args of λ where
            (xs ∷ ys ∷ []) → unifyStrict (hole , ty) $ def (quote L.Mem.∈-++⁺ʳ) (vArg xs ∷ hArg ys ∷ vArg `x∈ ∷ [])
            _ → err
          _ → err
        _ → err
      _ → err

f : ∀ (x y z : ℕ) xs ys → x ∈ xs ++ ys ++ (z ∷ y ∷ x ∷ [])
-- f x y z xs ys = ∈-++⁺ʳ xs (∈-++⁺ʳ _ (there (there (here refl))))
f x y z xs ys = `∈-++⁺ʳ (`∈-++⁺ʳ ((x ∈ (z ∷ y ∷ x ∷ [])) ∋ there (there (here refl))))
-}

{-
private
  _ : 5 ≡ 5
  _ = solveWith []

  _ : 5 ≡ 1 + 1 + 0 + 2 + 0 + 1
  _ = solve

  _ : ∀ {x : ℕ} → x ≡ x
  _ = solve

  _ : ∀ {x} → suc x ≡ suc x
  _ = solve
-}

private
  variable
    x y z : ℕ
    xs ys zs : List ℕ
{-
  _ : Any (_≡ 0) (0 ∷ [])
  _ = solve

  _ : Any (_≡ 0) [ 0 ]
  _ = solve

  _ : Any (_≡ 0) ⟦ 0 ⟧
  _ = solve

  _ : Any (_≡ 0) (1 ∷ 0 ∷ [])
  _ = solve

  _ : Any (_≡ 0) (2 ∷ 1 ∷ 0 ∷ [])
  _ = solve

  _ : Any (_≡ 0) (0 ∷ xs)
  _ = solve

  _ : Any (_≡ 0) ((0 ∷ []) ++ xs)
  _ = solve

  _ : Any (_≡ 0) (xs ++ (0 ∷ []))
  _ = solve

  _ : Any (_≡ 0) (xs ++ (0 ∷ []))
  _ = solve

  _ : Any (_≡ 0) (xs ++ ys ++ (0 ∷ []))
  _ = solve

  _ : Any (_≡ 0) (xs ++ ys ++ (1 ∷ 125 ∷ 0 ∷ []))
  _ = solve
-}
  module _ where
    open L.Mem

    _ : 0 ∈ (0 ∷ 1 ∷ xs)
    _ = solve


    -- _ : 0 ∈ xs ++ (0 ∷ 1 ∷ xs)
    -- _ = solve

    -- _ : x ∈ ys → x ∈ xs ++ ys
    -- _ = solve

    -- _ : x ∈ xs → x ∈ xs ++ ys ++ zs
    -- _ = solve

{-
    _ : x ∈ xs ⊎ x ∈ ys → x ∈ xs ++ ys
    -- _ = solve
    -- _ = λ where
    --   (inj₁ x∈) → solve
    --   (inj₂ x∈) → solve
    _ = λ x∈ →
          Sum.[ (λ x → {!!}) -- solve -- (λ x∈l → solve)
              , {!!} -- solve -- (λ x∈r → solve)
              ] x∈
-}

    -- f : x ∈ xs ++ ys → x ∈ xs ++ ys ++ zs
    -- f {x}{xs}{ys}{zs} = λ x∈ → case L.Mem.∈-++⁻ xs {ys} x∈ of λ where
    --   (inj₁ x∈xs) → solve -- (_ ∈ _ ++ ys ++ _ ∋ solve)
    --   (inj₂ x∈ys) → ? -- (_ ∈ xs ++ _ ++ _ ∋ solve)

  -- module _ where
  --   open import Prelude.Membership

  --   -- _ : 0 ∈ (List ℕ ∋ 0 ∷ 1 ∷ xs)
  --   -- _ = solve

  --   -- _ : 0 ∈ ys ++ (0 ∷ 1 ∷ xs)
  --   -- _ = solve

  --   -- _ : x ∈ ys → x ∈ xs ++ ys
  --   -- _ = solve

  --   _ : x ∈ xs → x ∈ xs ++ ys ++ zs
  --   _ = solve

  --   g : x ∈ xs ++ ys → x ∈ xs ++ ys ++ zs
  --   g {x}{xs}{ys}{zs} = λ x∈ → case L.Mem.∈-++⁻ xs {ys} x∈ of λ where
  --     (inj₁ x∈xs) → (_ L.Mem.∈ _ ++ ys ++ _ ∋ solve)
  --     (inj₂ x∈ys) → (_ L.Mem.∈ xs ++ _ ++ _ ∋ solve)

  -- T0D0: solver for _⊆_
  -- _ : (0 ∷ 1 ∷ xs) ⊆ (0 ∷ 2 ∷ 1 ∷ 2 ∷ 2 ∷ [])
  -- _ = {!!} -- solve
