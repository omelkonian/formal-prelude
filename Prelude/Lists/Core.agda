module Prelude.Lists.Core where

open import Prelude.Init; open SetAsType
open L.Mem
open import Prelude.Bifunctor

private variable
  A : Type ℓ; B : Type ℓ′; C : Type ℓ″
  x : A; y : B
  xs ys : List A

-- ** _++_
length-++-∸ : length (xs ++ ys) ∸ length ys ≡ length xs
length-++-∸ {xs = xs}{ys}
  rewrite L.length-++ xs {ys}
        | Nat.m+n∸n≡m (length xs) (length ys)
        = refl

-- ** map

map-proj₁-map₁ : ∀ {A B C : Type} {xs : List (A × B)} {f : A → C}
  → map proj₁ (map (map₁ f) xs)
  ≡ map (f ∘ proj₁) xs
map-proj₁-map₁ {xs = []} = refl
map-proj₁-map₁ {xs = x ∷ xs} {f = f} rewrite map-proj₁-map₁ {xs = xs} {f = f} = refl


-- ** unzip
proj₁∘unzip≡map∘proj₁ : (xys : List (A × B)) → proj₁ (unzip xys) ≡ map proj₁ xys
proj₁∘unzip≡map∘proj₁ [] = refl
proj₁∘unzip≡map∘proj₁ (_ ∷ xys) rewrite proj₁∘unzip≡map∘proj₁ xys = refl

proj₂∘unzip≡map∘proj₂ : (xys : List (A × B)) → proj₂ (unzip xys) ≡ map proj₂ xys
proj₂∘unzip≡map∘proj₂ [] = refl
proj₂∘unzip≡map∘proj₂ (_ ∷ xys) rewrite proj₂∘unzip≡map∘proj₂ xys = refl

∈-unzip⁻ˡ : (xys : List (A × B)) → x ∈ proj₁ (unzip xys) → ∃ λ xy → xy ∈ xys × x ≡ proj₁ xy
∈-unzip⁻ˡ xys rewrite proj₁∘unzip≡map∘proj₁ xys = ∈-map⁻ proj₁

∈-unzip⁻ʳ : (xys : List (A × B)) → y ∈ proj₂ (unzip xys) → ∃ λ xy → xy ∈ xys × y ≡ proj₂ xy
∈-unzip⁻ʳ xys rewrite proj₂∘unzip≡map∘proj₂ xys = ∈-map⁻ proj₂

unzip₃ : List (A × B × C) → List A × List B × List C
unzip₃ = map₂ unzip ∘ unzip

length-unzip₃ : ∀ (xyzs : List (A × B × C)) → let xs , ys , zs = unzip₃ xyzs in
    (length xs ≡ length xyzs)
  × (length ys ≡ length xyzs)
  × (length zs ≡ length xyzs)
length-unzip₃ [] = refl , refl , refl
length-unzip₃ (_ ∷ xyzs) =
  let xs≡ , ys≡ , zs≡ = length-unzip₃ xyzs
  in cong suc xs≡ , cong suc ys≡ , cong suc zs≡

length-unzip₃₁ : ∀ (xyzs : List (A × B × C)) → length (proj₁ $ unzip₃ xyzs) ≡ length xyzs
length-unzip₃₁ = proj₁ ∘ length-unzip₃

length-unzip₃₂ : ∀ (xyzs : List (A × B × C)) → length (proj₁ $ proj₂ $ unzip₃ xyzs) ≡ length xyzs
length-unzip₃₂ = proj₁ ∘ proj₂ ∘ length-unzip₃

length-unzip₃₃ : ∀ (xyzs : List (A × B × C)) → length (proj₂ $ proj₂ $ unzip₃ xyzs) ≡ length xyzs
length-unzip₃₃ = proj₂ ∘ proj₂ ∘ length-unzip₃

-- ** filter
filter₁ : List (A ⊎ B) → List A
filter₁ = mapMaybe isInj₁

filter₂ : List (A ⊎ B) → List B
filter₂ = mapMaybe isInj₂

-- ** Any/All

All-Any-refl : ∀ {xs : List A} {f : A → B}
  → All (λ x → Any (λ x′ → f x ≡ f x′) xs) xs
All-Any-refl {xs = []}     = []
All-Any-refl {xs = _ ∷ xs} = here refl ∷ L.All.map there (All-Any-refl {xs = xs})

all-filter⁺ : ∀ {P Q : A → Type ℓ} {P? : Decidable¹ P} {xs : List A}
  → All (λ x → P x → Q x) xs
  → All Q (filter P? xs)
all-filter⁺ {xs = _} [] = []
all-filter⁺ {P? = P?} {xs = x ∷ _} (Qx ∷ Qxs)
  with P? x
... | no  _  = all-filter⁺ Qxs
... | yes Px = Qx Px ∷ all-filter⁺ Qxs

All-map : ∀ {P : Pred₀ A} {Q : Pred₀ A} {xs : List A}
  → (∀ x → P x → Q x)
  → All P xs
  → All Q xs
All-map P⇒Q = L.All.map (λ {x} → P⇒Q x)

-- ** partitioning
lefts : List (A ⊎ B) → List A
lefts = proj₁ ∘ partitionSums

rights : List (A ⊎ B) → List B
rights = proj₂ ∘ partitionSums
