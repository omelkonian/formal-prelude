module Prelude.Lists.Membership where

open import Prelude.Init
open L.Mem

private variable
  a : Level; A : Set a
  x y : A; xs ys : List A

∈-++⁻∘∈-++⁺ˡ : (x∈ : x ∈ xs)
  → ∈-++⁻ xs {ys} (∈-++⁺ˡ {xs = xs}{ys} x∈)
  ≡ inj₁ x∈
∈-++⁻∘∈-++⁺ˡ (here _) = refl
∈-++⁻∘∈-++⁺ˡ {ys = ys} (there x∈) rewrite ∈-++⁻∘∈-++⁺ˡ {ys = ys} x∈ = refl

∈-++⁻∘∈-++⁺ʳ : (y∈ : y ∈ ys)
  → ∈-++⁻ xs {ys} (∈-++⁺ʳ xs {ys} y∈)
  ≡ inj₂ y∈
∈-++⁻∘∈-++⁺ʳ {xs = []} _ = refl
∈-++⁻∘∈-++⁺ʳ {xs = _ ∷ xs} y∈ rewrite ∈-++⁻∘∈-++⁺ʳ {xs = xs} y∈ = refl
