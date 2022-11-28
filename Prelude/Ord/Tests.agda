module Prelude.Ord.Tests where

open import Prelude.Init
open import Prelude.General
open import Prelude.Nary
open import Prelude.DecEq
open import Prelude.Ord

private

  -- ** min/max
  _ = min 10 20 ≡ 10
    ∋ refl

  _ = min 20 10 ≡ 10
    ∋ refl

  _ = min 0 1 ≡ 0
    ∋ refl

  _ = max 10 20 ≡ 20
    ∋ refl

  _ = max 20 10 ≡ 20
    ∋ refl

  _ = max 0 1 ≡ 1
    ∋ refl

  -- ** minimum/maximum

  _ = minimum⁺ ⟦ 1 , 3 , 2 , 0 ⟧ ≡ 0
    ∋ refl

  _ = minimum⁺ ⟦ 1 , 3 , 2 ⟧ ≡ 1
    ∋ refl

  _ = maximum⁺ ⟦ 1 , 3 , 2 , 0 ⟧ ≡ 3
    ∋ refl

  -- ** sorting

  _ = sort (List ℤ ∋ []) ≡ []
    ∋ refl

  _ = sort ⟦ 1 , 3 , 2 , 0 ⟧ ≡ ⟦ 0 , 1 , 2 , 3 ⟧
    ∋ refl

  _ = True (Sorted? ⟦ 1 , 6 , 15 ⟧)
    ∋ tt

  open Char-DecOrd
  _ = sort ⦃ Ord-Char ⦄ ⦃ DecOrd-Char ⦄ ⦃ it ⦄ ⦃ TotalOrderChar-≤ ⦄
      ⟦ 'a' , 'c' , '0' ⟧ ≡ ⟦ '0' , 'a' , 'c' ⟧
    ∋ refl

  open String-DecOrd
  _ = sort ⦃ itω ⦄ ⦃ λ {x}{y} → DecOrd-String {x}{y} ⦄ ⦃ it ⦄ ⦃ TotalOrderString-≤ ⦄
      ⟦ "abc" , "cde" , "cdc" ⟧ ≡ ⟦ "abc" , "cdc" , "cde" ⟧
    ∋ refl
