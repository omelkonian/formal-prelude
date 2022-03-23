------------------------------------------------------------------------
-- Properties of permuting lists with _↭_.

module Prelude.Lists.Permutations where

open import Prelude.Init
open L.Mem using (_∈_; mapWith∈)

private variable
  A : Set ℓ
  B : Set ℓ′
  x y : A
  xs ys zs ws : List A
  xss yss : List (List A)

open L.Perm using (shifts; ++⁺ˡ; ++⁺ʳ; map⁺; ↭-sym-involutive; ++-comm)

↭-concat⁺ : xss ↭ yss → concat xss ↭ concat yss
↭-concat⁺ ↭-refl = ↭-refl
↭-concat⁺ (↭-prep xs p) = ++⁺ˡ xs (↭-concat⁺ p)
↭-concat⁺ {xss = _ ∷ _ ∷ xss}{_ ∷ _ ∷ yss} (↭-swap xs ys p) = begin
  xs ++ ys ++ concat xss ↭⟨ shifts xs ys ⟩
  ys ++ xs ++ concat xss ↭⟨ ++⁺ˡ ys $ ++⁺ˡ xs $ ↭-concat⁺ p ⟩
  ys ++ xs ++ concat yss ∎ where open PermutationReasoning
↭-concat⁺ (↭-trans xs↭ys ys↭zs) = ↭-trans (↭-concat⁺ xs↭ys) (↭-concat⁺ ys↭zs)

↭-concatMap⁺ : (f : A → List B) → xs ↭ ys → concatMap f xs ↭ concatMap f ys
↭-concatMap⁺ f = ↭-concat⁺ ∘ map⁺ f

↭-sym∘++⁺ˡ :
  (p : xs ↭ ys)
  --——————————————————————————
  → ↭-sym (++⁺ˡ zs p)
  ≡ ++⁺ˡ zs (↭-sym p)
↭-sym∘++⁺ˡ {zs = []}    p = refl
↭-sym∘++⁺ˡ {zs = x ∷ _} p = cong (↭-prep x) (↭-sym∘++⁺ˡ p)

↭-sym∘++⁺ʳ :
  (p : xs ↭ ys)
  --——————————————————————————
  → ↭-sym (++⁺ʳ zs p)
  ≡ ++⁺ʳ zs (↭-sym p)
↭-sym∘++⁺ʳ {zs = zs} ↭-refl = refl
↭-sym∘++⁺ʳ {zs = zs} (↭-prep x p) = cong (↭-prep x) (↭-sym∘++⁺ʳ p)
↭-sym∘++⁺ʳ {zs = zs} (↭-swap x y p) = cong (↭-swap y x) (↭-sym∘++⁺ʳ p)
↭-sym∘++⁺ʳ {zs = zs} (↭-trans p q)
  rewrite ↭-sym∘++⁺ʳ {zs = zs} p
        | ↭-sym∘++⁺ʳ {zs = zs} q
        = refl

↭-sym∘++⁺ˡ∘++⁺ˡ :
  (p : xs ↭ ys)
  --——————————————————————————
  → ↭-sym (++⁺ˡ zs $ ++⁺ˡ ws p)
  ≡ (++⁺ˡ zs $ ++⁺ˡ ws $ ↭-sym p)
↭-sym∘++⁺ˡ∘++⁺ˡ {zs = zs}{ws} p
  rewrite ↭-sym∘++⁺ˡ {zs = zs} (++⁺ˡ ws p)
        | ↭-sym∘++⁺ˡ {zs = ws} p
        = refl

↭-sym∘map⁺ :
  (f : A → B)
  (p : xs ↭ ys)
  --——————————————————————————
  → ↭-sym (map⁺ f p)
  ≡ map⁺ f (↭-sym p)
↭-sym∘map⁺ f ↭-refl = refl
↭-sym∘map⁺ f (↭-prep x p) = cong (↭-prep $ f x) (↭-sym∘map⁺ f p)
↭-sym∘map⁺ f (↭-swap x y p) = cong (↭-swap (f y) (f x)) (↭-sym∘map⁺ f p)
↭-sym∘map⁺ f (↭-trans {xs}{ys}{zs} p q)
  rewrite ↭-sym∘map⁺ {xs = xs} {ys} f p
        | ↭-sym∘map⁺ {xs = ys} {zs} f q
        = refl

↭-sym∘↭-trans :
  (p : ys ↭ xs)
  (q : ys ↭ zs)
  --——————————————————————————
  → ↭-sym (↭-trans (↭-sym p) q)
  ≡ ↭-trans (↭-sym q) p
↭-sym∘↭-trans p q = cong (↭-trans $ ↭-sym q) (↭-sym-involutive p)

↭trans∘↭-refl :
  (p : xs ↭ ys)
  --——————————————————————————
  → L.Perm.↭-trans p ↭-refl
  ≡ p
↭trans∘↭-refl = λ where
  ↭-refl → refl
  (↭-prep _ _) → refl
  (↭-swap _ _ _) → refl
  (↭-trans _ _) → refl

↭-sym∘↭trans :
  (p : xs ↭ ys)
  (q : ys ↭ zs)
  --——————————————————————————
  → ↭-sym (L.Perm.↭-trans p q)
  ≡ L.Perm.↭-trans (↭-sym q) (↭-sym p)
↭-sym∘↭trans ↭-refl q rewrite ↭trans∘↭-refl (↭-sym q) = refl
↭-sym∘↭trans (↭-prep _ _) = λ where
  ↭-refl         → refl
  (↭-prep _ _)   → refl
  (↭-swap _ _ _) → refl
  (↭-trans _ _)  → refl
↭-sym∘↭trans (↭-swap _ _ _) = λ where
  ↭-refl         → refl
  (↭-prep _ _)   → refl
  (↭-swap _ _ _) → refl
  (↭-trans _ _)  → refl
↭-sym∘↭trans (↭-trans _ _) = λ where
  ↭-refl         → refl
  (↭-prep _ _)   → refl
  (↭-swap _ _ _) → refl
  (↭-trans _ _)  → refl

open Alg≡
postulate
  ↭⇒≡ : ∀ {x₀ : A} {xs ys : List A} {_⊕_ : Op₂ A}
    → Identity x₀ _⊕_
    → Commutative _⊕_
    → xs ↭ ys
    → foldr _⊕_ x₀ xs ≡ foldr _⊕_ x₀ ys
-- ↭⇒≡ = {!!}
