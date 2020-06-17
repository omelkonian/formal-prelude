module Prelude.Show where

open import Function
open import Reflection
open import Reflection.Argument using (unArg)
open import Data.String hiding (show) renaming (_++_ to _<>_)
open import Data.Product
open import Data.Bool
open import Data.Bool.Show using () renaming (show to showᵇ)
open import Data.Nat
open import Data.Nat.Show using () renaming (show to showℕ)

open import Prelude.Lists

private
  variable
    A B : Set

record Show (A : Set) : Set where
  field
    show : A → String

open Show {{...}} public

instance
  Show-String : Show String
  Show-String .show x = x

  Show-Bool : Show Bool
  Show-Bool .show = showᵇ

  Show-ℕ : Show ℕ
  Show-ℕ .show = showℕ

  Show-Name : Show Name
  Show-Name .show = showName

  Show-Term : Show Term
  Show-Term .show = showTerm

  Show-Clause : Show Clause
  Show-Clause .show = showClause

  Show-Definition : Show Definition
  Show-Definition .show = showDefinition

  Show-List : {{_ : Show A}} → Show (List A)
  Show-List .show = braces ∘ join show

  Show-Arg : {{_ : Show A}} → Show (Arg A)
  Show-Arg .show = show ∘ unArg

  Show-× : {{_ : Show A}} {{_ : Show B}} → Show (A × B)
  Show-× .show (x , y) = parens $ show x <> " , " <> show y
