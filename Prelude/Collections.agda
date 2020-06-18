module Prelude.Collections where

open import Data.Unit
open import Data.Product
open import Data.List

private
  variable
    X Y Z : Set

record _has_ (A : Set) (B : Set) : Set where
  field
    collect : A → List B
open _has_ {{...}} public

instance
  H-List : ∀ {{_ : X has Y}} → List X has Y
  H-List .collect []       = []
  H-List .collect (x ∷ xs) = collect x ++ collect xs

  -- H-×ˡ : ∀ {{_ : X has Z}} → (X × Y) has Z
  -- H-×ˡ .collect (x , _) = collect x

  H-×ʳ : ∀ {{_ : Y has Z}} → (X × Y) has Z
  H-×ʳ .collect (_ , y) = collect y
