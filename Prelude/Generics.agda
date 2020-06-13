{- Meta-programming utilities -}
module Prelude.Generics where

open import Function
open import Reflection

open import Data.Unit
open import Data.Bool
open import Data.String
open import Data.List

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
  hiding ([_])


-- ** Errors, debugging

error : ∀ {A : Set} → String → TC A
error s = typeError [ strErr s ]

print⊤ : String → TC ⊤
print⊤ s = debugPrint "Prelude.Generics" 0 [ strErr s ]
-- e.g. set {-# OPTIONS -v "Prelude.Generics" 1 #-} to enable messages.


-- ** Smart constructors

-- arguments
pattern vArg x = arg (arg-info visible relevant) x
pattern hArg x = arg (arg-info hidden relevant) x
pattern hArg?  = hArg unknown

-- variables
pattern # n = var n []
pattern #_⟦_⟧ n x = var n (vArg x ∷ [])
pattern #_⟦_∣_⟧ n x y = var n (vArg x ∷ vArg y ∷ [])

-- lambdas
pattern `λ_⇒_ x k = lam visible (abs x k)
pattern `λ⟦_∣_⟧⇒_ x y k = `λ x ⇒ `λ y ⇒ k

pattern `λ⟦_⇒_⟧ p k =
  pat-lam (Clause.clause (vArg p ∷ []) k ∷ []) []
pattern `λ⟦_⇒_∣_⇒_⟧ p₁ k₁ p₂ k₂ =
  pat-lam (Clause.clause (vArg p₁ ∷ []) k₁ ∷ Clause.clause (vArg p₂ ∷ []) k₂ ∷ []) []

-- function application
pattern _∙ n = def n []
pattern _∙⟦_⟧ n x = def n (vArg x ∷ [])
pattern _∙⟦_∣_⟧ n x y = def n (vArg x ∷ vArg y ∷ [])

pattern _◆ n = con n []
pattern _◆⟦_⟧ n x = con n (vArg x ∷ [])
pattern _◆⟦_∣_⟧ n x y = con n (vArg x ∷ vArg y ∷ [])

pattern _◇ n = Pattern.con n []
pattern _◇⟦_⟧ n x = Pattern.con n (vArg x ∷ [])
pattern _◇⟦_∣_⟧ n x y = Pattern.con n (vArg x ∷ vArg y ∷ [])
