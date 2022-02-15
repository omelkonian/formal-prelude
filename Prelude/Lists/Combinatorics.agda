------------------------------------------------------------------------
-- Combinatorics on lists.

module Prelude.Lists.Combinatorics where

open import Prelude.Init
open L.Mem

private variable
  A : Set ℓ;  x : A; xs : List A
  B : Set ℓ′; y : B; ys : List B

-- e.g. subsequences "abc" ≡ ["","c","b","bc","a","ab","ac","abc"]
subsequences : List A → List (List A)
subsequences []       = [ [] ]
subsequences (x ∷ xs) = xss ++ map (x ∷_) xss
  where xss = subsequences xs

subsequences-refl : xs ∈ subsequences xs
subsequences-refl {xs = []}     = here refl
subsequences-refl {xs = x ∷ xs} = ∈-++⁺ʳ (subsequences xs) (∈-map⁺ (x ∷_) (subsequences-refl {xs = xs}))

-- e.g. combinations [[1,2,3],[4,5]] ≡ [[1,4],[1,5],[2,4],[2,5],[3,4],[3,5]]
combinations : List (List A) → List (List A)
combinations []         = [ [] ]
combinations (xs ∷ xss) = concatMap (λ x → map (x ∷_) xss′) xs
  where xss′ = combinations xss

cartesianProduct : List A → List B → List (A × B)
cartesianProduct xs ys = concatMap (λ x → map (x ,_) ys) xs

postulate
  cartesianProduct-∈ : x ∈ xs → y ∈ ys → (x , y) ∈ cartesianProduct xs ys

allPairs : List A → List (A × A)
allPairs xs = cartesianProduct xs xs
