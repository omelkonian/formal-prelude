module Prelude.Lists.Concat where

open import Prelude.Init
open L.Mem
open Nat.Ord
open import Prelude.InferenceRules

private variable
  A : Set ℓ; B : Set ℓ′
  x : A; xs ys : List A; xss : List (List A)

concat-∷ : concat (x ∷ xs) ≡ x ++ concat xs
concat-∷ {xs = []}    = refl
concat-∷ {xs = _ ∷ _} = refl

⊆-concat⁺ :
    xs ∈ xss
    ────────
    xs ⊆ concat xss
⊆-concat⁺ (here refl) = ∈-++⁺ˡ
⊆-concat⁺ (there xs∈) = ∈-++⁺ʳ _ ∘ ⊆-concat⁺ xs∈

length-concat :
    xs ∈ xss
    ──────────
    length xs ≤ length (concat xss)
length-concat {xs = .xs} {xss = xs ∷ xss} (here refl)
  rewrite L.length-++ xs {concat xss}
  = Nat.m≤m+n (length xs) (length $ concat xss)
length-concat {xs = xs} {xss = ys ∷ xss} (there xs∈)
  rewrite L.length-++ ys {concat xss}
  = Nat.≤-stepsˡ (length ys) $ length-concat {xs = xs}{xss = xss} xs∈

∈-concatMap⁻ : ∀ {y : B} (f : A → List B)
  → y ∈ concatMap f xs
  → Any (λ x → y ∈ f x) xs
∈-concatMap⁻ f = L.Any.map⁻ ∘ ∈-concat⁻ (map f _)

∈-concatMap⁺ : ∀ {y : B} {f : A → List B}
  → Any (λ x → y ∈ f x) xs
  → y ∈ concatMap f xs
∈-concatMap⁺ = ∈-concat⁺ ∘ L.Any.map⁺

concatMap-∷ : ∀ {A B : Set} {x : A} {xs : List A} {f : A → List B}
  → concatMap f (x ∷ xs) ≡ f x ++ concatMap f xs
concatMap-∷ {x = x}{xs}{f} rewrite concat-∷ {x = f x}{map f xs} = refl

concatMap-++ : ∀ {A B : Set} (f : A → List B) (xs ys : List A)
  → concatMap f (xs ++ ys) ≡ concatMap f xs ++ concatMap f ys
concatMap-++ f xs ys =
  begin concatMap f (xs ++ ys)                 ≡⟨⟩
        concat (map f (xs ++ ys))              ≡⟨ cong concat (L.map-++-commute f xs ys) ⟩
        concat (map f xs ++ map f ys)          ≡⟨ sym (L.concat-++ (map f xs) (map f ys)) ⟩
        concat (map f xs) ++ concat (map f ys) ≡⟨⟩
        concatMap f xs ++ concatMap f ys       ∎
  where open ≡-Reasoning
