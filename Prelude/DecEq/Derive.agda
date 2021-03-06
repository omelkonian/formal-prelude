-- {-# OPTIONS -v DecEq:100 #-}
module Prelude.DecEq.Derive where

open import Prelude.Init
open Meta
import Reflection.Argument as RArg
open import Reflection.Name renaming (_≟_ to _≟ₙ_)
open import Reflection.Term renaming (_≟_ to _≟ₜ_)
open import Reflection.Argument.Visibility renaming (_≟_ to _≟ᵥ_)

open import Prelude.Generics
open import Prelude.Generics using (DERIVE) public
open Debug ("DecEq" , 100)
open import Prelude.Lists
open import Prelude.Show
open import Prelude.Monoid
open import Prelude.Functor
open import Prelude.Monad

open import Prelude.DecEq.Core

-------------------------------
-- ** Generic deriving of DecEq

pattern `yes x  = quote _because_ ◆⟦ quote true ◆  ∣ quote ofʸ ◆⟦ x ⟧ ⟧
pattern ``yes x = quote _because_ ◇⟦ quote true ◇  ∣ quote ofʸ ◇⟦ x ⟧ ⟧
pattern `no x   = quote _because_ ◆⟦ quote false ◆ ∣ quote ofⁿ ◆⟦ x ⟧ ⟧
pattern ``no x  = quote _because_ ◇⟦ quote false ◇ ∣ quote ofⁿ ◇⟦ x ⟧ ⟧

compatible? : Type → Type → TC Bool
compatible? ty ty′ = do
  print $ show ty ◇ " ≈? " ◇ show ty′
  b ← runSpeculative $ (_, false) <$>
    catchTC (unify (varsToUnknown ty) (varsToUnknown ty′) >> return true)
            (return false)
  print $ "  ——→ " ◇ show b
  return b

derive-DecEq : (Name × Name) → Definition → TC Term

derive-DecEq _              (data-type _ []) = return `λ∅
derive-DecEq (this , ≟-rec) (data-type pars cs) = do
  print $ "DATATYPE {pars = " ◇ show pars ◇ "; cs = " ◇ show cs ◇ "}"
  cls ← concatMap L.fromMaybe <$> mapM f (allPairs cs)
  return $ pat-lam cls []
  where
    go : ℕ → List (ℕ × Type) → Term
    go _ []              = `yes (quote refl ◆)
    go n ((x , ty) ∷ xs) =
      quote case_of_
        ∙⟦ quote _≟_ ∙⟦ ♯ (x + n) ∣ ♯ x ⟧
         ∣ `λ⟦ ``no (Pattern.var "¬p") ⇒ `no (`λ⟦ (quote refl ◇) ⇒ (♯ 0 ⟦ quote refl ◆ ⟧) ⟧)
             ∣ ``yes (quote refl ◇)    ⇒ go n xs ⟧ ⟧

    f : Name × Name → TC (Maybe Clause)
    f (c , c′) = do
      (pc  , _ , pvs) ← mkPattern c
      (pc′ , n , _)   ← mkPattern c′
      ty  ← getType c
      ty′ ← getType c′
      b   ← compatible? (resultTy ty) (resultTy ty′)
      return $
        if b then
          just (if c == c′ then ⟦ pc ∣ mapVariables (_<> "′") pc ⇒ go n pvs ⟧
                           else ⟦ pc ∣ pc′ ⇒ `no `λ∅ ⟧)
        else nothing
derive-DecEq _ (record-type rn fs) = do
  print $ "RECORD {name = " ◇ show rn ◇ "; fs = " ◇ show fs ◇ "}"
  return $ `λ⟦ "r" ∣ "r′" ⇒ go fs ⟧
  where
    go : List (Arg Name) → Term
    go [] = `yes (quote refl ◆)
    go (arg (arg-info _ irrelevant) _ ∷ args) = go args
    go (arg (arg-info _ relevant)   n ∷ args) =
      quote case_of_
        ∙⟦ quote _≟_ ∙⟦ n ∙⟦ ♯ 1 ⟧ ∣ n ∙⟦ ♯ 0 ⟧ ⟧
         ∣ `λ⟦ ``no (Pattern.var "¬p")
             ⇒ `no (`λ⟦ (quote refl ◇) ⇒ (♯ 0 ⟦ quote refl ◆ ⟧) ⟧)
             ∣ ``yes (quote refl ◇)
             ⇒ go args
             ⟧
         ⟧
derive-DecEq _ _ = error "impossible"

instance
  Derivable-DecEq : Derivable DecEq
  Derivable-DecEq .DERIVE' xs = do
    print "*************************************************************************"
    (record-type c _) ← getDefinition (quote DecEq)
      where _ → error "impossible"

    -- ** Declare ⋯ fᵢ′ : Decidable² {A = Tᵢ} _≡_ ⋯
    -- and define ⋯ instance
    --                fᵢ : DecEq Tᵢ ⋯
    --                fᵢ = ⋯
    --            ⋯
    ys ← forM xs λ{ (n , f) → do
      print $ "Deriving " ◇ parens (show f ◇ " : DecEq " ◇ show n)
      f′ ← freshName (show {A = Name} f)
      T ← getType n
      ctx ← getContext
      print $ "  Context: " ◇ show ctx
      print $ "  n: " ◇ show n
      print $ "  Type: " ◇ show T
      d ← getDefinition n
      let is = drop ({-parameters d-} length ctx) (argTys T)
      let n′ = apply⋯ is n
      print $ "  Parameters: " ◇ show (parameters d)
      print $ "  Indices: " ◇ show is
      print $ "  n′: " ◇ show n′
      t ← derive-DecEq (n , f′) d
      -- print $ "  Term: " ◇ show t
      let ty′ = ∀indices⋯ is $ def (quote Decidable²) (hArg? ∷ hArg n′ ∷ hArg? ∷ hArg? ∷ vArg (quote _≡_ ∙) ∷ [])
      print $ "  Ty′: " ◇ show ty′
      declareDef (vArg f′) ty′
      let ty = ∀indices⋯ is $ quote DecEq ∙⟦ n′ ⟧
      print $ "  Ty: " ◇ show ty
      declareDef (iArg f) ty
      defineFun f (⟦⇒ c ◆⟦ f′ ∙ ⟧ ⟧ ∷ [])
      return (f′ , t)
      }

    -- ** Define ⋯ fᵢ′ : Decidable² {A = Tᵢ} _≡_ ⋯
    return⊤ $ forM ys λ{ (f′ , t) → defineFun f′ (⟦⇒ t ⟧ ∷ []) }

--------------------------
-- Example

private

-- ** record types

  record R⁰ : Set where
  unquoteDecl r⁰ = DERIVE DecEq [ quote R⁰ , r⁰ ]

  record R¹ : Set where
    field
      x : ℕ
  unquoteDecl r¹ = DERIVE DecEq [ quote R¹ , r¹ ]

  record R² : Set where
    field
      x : ℕ × ℤ
      y : ⊤ ⊎ Bool
  unquoteDecl r² = DERIVE DecEq [ quote R² , r² ]

-- ** inductive datatypes

  data X⁰ : Set where
  unquoteDecl x⁰ = DERIVE DecEq [ quote X⁰ , x⁰ ]

  data X¹ : Set where
    x : X¹
  unquoteDecl x¹ = DERIVE DecEq [ quote X¹ , x¹ ]

  data X² : Set where
    x y : X²
  unquoteDecl x² = DERIVE DecEq [ quote X² , x² ]

  data XX : Set where
    c₁ : X¹ → X² → XX
    c₂ : List X² → XX
  unquoteDecl xx = DERIVE DecEq [ quote XX , xx ]

-- ** recursive datatypes

  data ℕ′ : Set where
    O : ℕ′
    S : ℕ′ → ℕ′
  unquoteDecl DecEq-ℕ′ = DERIVE DecEq [ quote ℕ′ , DecEq-ℕ′ ]

-- ** list recursion

  data Nats : Set where
    O : Nats
    S : List Nats → Nats

  {-# TERMINATING #-}
{- *** T0D0: figure out how to pass termination checker

  go : Decidable² {A = Nat} _≡_
  instance
    dn : DecEq Nat
    dn ._≟_ = go
  go = λ
    { O O → yes refl
    ; O (S x0) → no (λ { () })
    ; (S x0) O → no (λ { () })
    ; (S x0) (S x0′)
        → case _≟_ ⦃ DecEq-List ⦃ dn ⦄ ⦄ x0 x0′ of λ
            { (no ¬p) → no λ { refl → ¬p refl }
            ; (yes refl) → yes refl  ⦄
-}
  unquoteDecl DecEq-Nats = DERIVE DecEq [ quote Nats , DecEq-Nats ]

-- ** mutually recursive datatypes

  data M₁ : Set
  data M₂ : Set
  data M₁ where
    m₁ : M₁
    m₂→₁ : M₂ → M₁
  data M₂ where
    m₂ : M₂
    m₁→₂ : M₁ → M₂
  unquoteDecl DecEq-M₁ DecEq-M₂ = DERIVE DecEq $ (quote M₁ , DecEq-M₁) ∷ (quote M₂ , DecEq-M₂) ∷ []

-- ** make sure all derivations were successful
  open import Data.List.Relation.Unary.All using (All; []; _∷_)
  _ : All (λ x → Decidable² {A = x} _≡_) (R⁰ ∷ R¹ ∷ R² ∷ X⁰ ∷ X¹ ∷ X² ∷ XX ∷ ℕ′ ∷ M₁ ∷ M₂ ∷ [])
  _ = _≟_ ∷ _≟_ ∷ _≟_ ∷ _≟_ ∷ _≟_ ∷ _≟_ ∷ _≟_ ∷ _≟_ ∷ _≟_ ∷ _≟_ ∷ []

-- ** indexed types

  data Fin′ : ℕ → Set where
    O : ∀ {n} → Fin′ (suc n)
    S : ∀ {n} → Fin′ n → Fin′ (suc n)
  unquoteDecl DecEq-Fin′ = DERIVE DecEq [ quote Fin′ , DecEq-Fin′ ]
  _ : ∀ {n} → Decidable² {A = Fin′ n} _≡_
  _ = _≟_

  data Boolℕ : Bool → ℕ → Set where
    O : Boolℕ true 0
  unquoteDecl DecEq-Boolℕ = DERIVE DecEq [ quote Boolℕ , DecEq-Boolℕ ]
  _ : ∀ {b n} → Decidable² {A = Boolℕ b n} _≡_
  _ = _≟_

  data Boolℕ² : Bool → ℕ → Set where
    O : Boolℕ² false 0
    I : Boolℕ² true  1
  unquoteDecl DecEq-Boolℕ² = DERIVE DecEq [ quote Boolℕ² , DecEq-Boolℕ² ]
  _ : ∀ {b n} → Decidable² {A = Boolℕ² b n} _≡_
  _ = _≟_

-- ** parametrized datatypes

  -- data Expr Set) : Set where
  --   Con : A → Expr A
  --   _⊕_ : Expr A → Expr A → Expr A
  -- unquoteDecl DecEq-Expr  = DERIVE DecEq [ quote Expr , DecEq-Expr ]
  -- _ : ∀ {A} ⦃ _ : DecEq A ⦄ → Decidable² {A = Expr A} _≡_
  -- _ = _≟_

  -- data Exprℕ : ℕ → Set where
  --   Con : ∀ {n} → ℕ → Exprℕ n
  --   _⊕_ : ∀ {x y z} → Exprℕ x → Exprℕ y → Exprℕ z
  -- unquoteDecl DecEq-Exprℕ  = DERIVE DecEq [ quote Exprℕ , DecEq-Exprℕ ]
  -- _ : ∀ {n} → Decidable² {A = Exprℕ A} _≡_
  -- _ = _≟_

-- ** indexed records

  record Pos (n : ℕ) : Set where
    field
      pos : Fin n
  unquoteDecl DecEq-Pos  = DERIVE DecEq [ quote Pos , DecEq-Pos ]
  _ : ∀ {n} → Decidable² {A = Pos n} _≡_
  _ = _≟_

-- ** datatypes inside module

  module Test₁ (A : Set) ⦃ _ : DecEq A ⦄ (B : Set) ⦃ _ : DecEq B ⦄ where

    data X : ℕ → Set where
      x₀ y₀ z₀ : X 0
      x₁ y₁ z₁ : X 1
      fromA    : ∀ {n} → A → X n
      fromB    : ∀ {n} → B → X n
    unquoteDecl DecEq-Test1X = DERIVE DecEq [ quote X , DecEq-Test1X ]
    _ : ∀ {n} → Decidable² {A = X n} _≡_
    _ = _≟_

    record R : Set where
      field
        r₁ : A
        r₂ : B
    unquoteDecl DecEq-Test1R = DERIVE DecEq [ quote R , DecEq-Test1R ]
    _ : Decidable² {A = R} _≡_
    _ = _≟_

    record R′ : Set where
      field
        r₁ : A × B
        r₂ : X 0
    unquoteDecl DecEq-Test1R′ = DERIVE DecEq [ quote R′ , DecEq-Test1R′ ]
    _ : Decidable² {A = R′} _≡_
    _ = _≟_

  module _ (A : Set) ⦃ _ : DecEq A ⦄ {B : Set} ⦃ _ : DecEq B ⦄ where
    open Test₁ A B

    _ : ∀ {n} → Decidable² {A = X n} _≡_
    _ = _≟_
    _ : Decidable² {A = R} _≡_
    _ = _≟_
    _ : Decidable² {A = R′} _≡_
    _ = _≟_

  unquoteDecl DecEq-Test1R = DERIVE DecEq [ quote Test₁.R , DecEq-Test1R ]
  _ : ∀ {A : Set} ⦃ _ : DecEq A ⦄ {B : Set} ⦃ _ : DecEq B ⦄
    → Decidable² {A = Test₁.R A B} _≡_
  _ = _≟_

  -- unquoteDecl DecEq-Test1R′ = DERIVE DecEq [ quote Test₁.R′ , DecEq-Test1R′ ]
  -- _ : ∀ {A : Set} ⦃ _ : DecEq A ⦄ {B : Set} ⦃ _ : DecEq B ⦄
  --   → Decidable² {A = Test₁.R′ A B} _≡_
  -- _ = _≟_

{-
  module Test₂ (A : Set) ⦃ _ : DecEq A ⦄ (B : Set) ⦃ _ : DecEq B ⦄ where

    data X : ℕ → Set where
      x₀ y₀ z₀ : X 0
      x₁ y₁ z₁ : X 1
      fromA    : ∀ {n} → A → X n
      fromB    : ∀ {n} → B → X n
    unquoteDecl DecEq-Test2X = DERIVE DecEq [ quote X , DecEq-Test2X ]
    _ : ∀ {n} → Decidable² {A = X n} _≡_
    _ = _≟_

    record R : Set where
      field
        r₁ : X 1
        r₂ : X 2

  unquoteDecl DecEq-TestR = DERIVE DecEq [ quote Test₂.R , DecEq-TestR ]

  _ : ∀ {A : Set} ⦃ _ : DecEq A ⦄ {B : Set} ⦃ _ : DecEq B ⦄ → Decidable² {A = Test₂.R {A} {B ⦄ _≡_
  _ = _≟_
-}
