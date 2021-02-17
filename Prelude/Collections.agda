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
open _has_ ⦃...⦄ public

collectFromList : ∀ ⦃ _ : X has Y ⦄ → List X has Y
collectFromList .collect = concatMap collect
-- collectFromList .collect = go
--   where
--     go : ⦃ _ : X has Y ⦄ → List X → List Y
--     go []       = []
--     go (x ∷ xs) = collect x ++ go xs

collectFromPairˡ : ∀ ⦃ _ : X has Z ⦄ → (X × Y) has Z
collectFromPairˡ .collect (x , _) = collect x

collectFromPairʳ : ∀ ⦃ _ : Y has Z ⦄ → (X × Y) has Z
collectFromPairʳ .collect (_ , y) = collect y

-- NB: do not expose instances, let user decide
