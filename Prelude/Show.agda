module Prelude.Show where

open import Reflection
open import Reflection.Argument using (unArg)
open import Reflection.Show

open import Prelude.Init
open import Prelude.Lists
open import Prelude.Monoid

private
  variable
    A B : Set

record Show (A : Set) : Set where
  field
    show : A → String

open Show {{...}} public

instance
  Show-⊤ : Show ⊤
  Show-⊤ .show tt = "tt"

  Show-String : Show String
  Show-String .show x = x

  Show-Bool : Show Bool
  Show-Bool .show = B.show

  Show-ℕ : Show ℕ
  Show-ℕ .show = Nat.show

  Show-Name : Show Name
  Show-Name .show = showName

  Show-Term : Show Term
  Show-Term .show = showTerm

  Show-Clause : Show Clause
  Show-Clause .show = showClause

  Show-Definition : Show Definition
  Show-Definition .show = showDefinition

  Show-List : {{_ : Show A}} → Show (List A)
  Show-List .show = braces ∘ Str.intersperse ", " ∘ map show

  Show-Arg : {{_ : Show A}} → Show (Arg A)
  Show-Arg .show = show ∘ unArg

  Show-× : {{_ : Show A}} {{_ : Show B}} → Show (A × B)
  Show-× .show (x , y) = parens $ show x <> " , " <> show y
