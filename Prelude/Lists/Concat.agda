{-# OPTIONS --safe #-}
module Prelude.Lists.Concat where

open import Prelude.Init; open SetAsType
open L.Mem
open Nat.Ord
open import Prelude.InferenceRules

private variable
  A : Type ℓ; B : Type ℓ′
  x : A; xs ys : List A; xss : List (List A)

⊆-concat⁺ :
  xs ∈ xss
  ───────────────
  xs ⊆ concat xss
⊆-concat⁺ = λ where
  (here refl) → ∈-++⁺ˡ
  (there xs∈) → ∈-++⁺ʳ _ ∘ ⊆-concat⁺ xs∈

length-concat :
    xs ∈ xss
    ───────────────────────────────
    length xs ≤ length (concat xss)
length-concat {xss = xs ∷ xss} p
  rewrite L.length-++ xs {concat xss}
  with p
... | here refl = Nat.m≤m+n    (length xs) (length $ concat xss)
... | there p   = Nat.≤-stepsˡ (length xs) (length-concat p)

concatMap-++ : ∀ (f : A → List B) (xs ys : List A)
  → concatMap f (xs ++ ys) ≡ concatMap f xs ++ concatMap f ys
concatMap-++ f xs ys = begin
  concatMap f (xs ++ ys)           ≡⟨⟩
  concat (map f (xs ++ ys))        ≡⟨ cong concat $ L.map-++-commute f xs ys ⟩
  concat (map f xs ++ map f ys)    ≡˘⟨ L.concat-++ (map f xs) (map f ys) ⟩
  concatMap f xs ++ concatMap f ys ∎ where open ≡-Reasoning

module _ (f : A → List B) where

  Any-concatMap : ∀ {p} {P : Pred B p} →
    Any (Any P ∘ f) xs
    ══════════════════════
    Any P (concatMap f xs)
  Any-concatMap  = Any-concatMap⁺ , Any-concatMap⁻
    module _ where
    Any-concatMap⁺ = L.Any.concat⁺ ∘ L.Any.map⁺
    Any-concatMap⁻ = L.Any.map⁻ ∘ L.Any.concat⁻ _

  module _ {y} where
    ∈-concatMap⁺ : Any ((y ∈_) ∘ f) xs → y ∈ concatMap f xs
    ∈-concatMap⁺ = Any-concatMap⁺

    ∈-concatMap⁻ : y ∈ concatMap f xs → Any ((y ∈_) ∘ f) xs
    ∈-concatMap⁻ = Any-concatMap⁻

    ∈-concatMap :
      Any ((y ∈_) ∘ f) xs
      ═══════════════════
      y ∈ concatMap f xs
    ∈-concatMap  = ∈-concatMap⁺ , ∈-concatMap⁻
