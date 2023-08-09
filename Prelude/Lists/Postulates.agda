-- {-# OPTIONS --safe #-}
module Prelude.Lists.Postulates where

open import Prelude.Init; open SetAsType
open L.Mem
open Nat
open import Prelude.Null
open import Prelude.Bifunctor

private variable
  A B C : Type ℓ
  x : A; xs : List A
  y : B; ys : List B
  P : Pred A ℓ

open Alg≡

open import Prelude.Lists.Combinatorics
postulate
  cartesianProduct-∈ : x ∈ xs → y ∈ ys → (x , y) ∈ cartesianProduct xs ys

open import Prelude.Lists.Permutations
postulate
  ↭⇒≡ : ∀ {x₀ : A} {xs ys : List A} {_⊕_ : Op₂ A}
    → Identity x₀ _⊕_
    → Commutative _⊕_
    → xs ↭ ys
    → foldr _⊕_ x₀ xs ≡ foldr _⊕_ x₀ ys

open import Prelude.Lists.Count
module _ {P : Pred A ℓ} (P? : Decidable¹ P) where postulate
  ⊆⇒count≤ : xs ⊆ ys → count P? xs ≤ count P? ys
  count≡0⇒null-filter : count P? xs ≡ 0 → Null $ filter P? xs
  count≡0⇒All¬ : count P? xs ≡ 0 → All (¬_ ∘ P) xs
  count-map⁺ : ∀ {f : B → A}
    → count (P? ∘ f) xs
    ≡ count P? (map f xs)
  count-single : ∀ {x xs}
    → count P? (x ∷ xs) ≡ 1
    → P x
    → All (x ≢_) xs
  -- count-single {x} {xs} count≡1 px
  --   with P? x
  -- ... | no ¬px = ⊥-elim $ ¬px px
  -- ... | yes _  = L.All.¬Any⇒All¬ xs h
  --   where
  --     h : x ∉ xs
  --     h x∈ = {!!}

open import Prelude.Lists.Sums
private variable
  X Y : Pred₀ ℕ
  n : ℕ; ns : List ℕ
postulate
  ∑₁-limit : ∀ {lim} {xs : List (∃ X)}
    {k₁ : ∀ {n} → lim ≤ n → X n → Y lim} {k₂ : ∀ {n} → n ≤ lim → X n → Y n}
    → ∑₁ xs ≥ lim
    → ∑₁ (limit lim k₁ k₂ xs) ≥ lim

  ∑₁-++ : ∀ {xs ys : List (∃ X)}
    → ∑₁ (xs ++ ys)
    ≡ ∑₁ xs + ∑₁ ys

  ∑ℕ-∀≡0 : ∀ {xs}
    → All (_≡ 0) xs
    → ∑ℕ xs ≡ 0

  ∑ℕ-⊆ : ∀ {xs ys} → xs ⊆ ys → ∑ℕ xs ≤ ∑ℕ ys

  ∑₁-map₂ : ∀ {xs : List (∃ X)} {f : ∀ {n} → X n → Y n}
    → ∑₁ (map (map₂′ f) xs)
    ≡ ∑₁ xs

  ∑₁-single : ∀ {x : ∃ X} → ∑₁ [ n , x ] ≡ n

  x∈∑ℕ : n L.Mem.∈ ns → n ≤ ∑ℕ ns

open import Prelude.Lists.Singletons
postulate
  ams-filter-map : ∀ {xs : List A} {f : A → B} {P : Pred₀ B} {P? : Decidable¹ P}
    → AtMostSingleton $ filter P? (map f xs)
    → AtMostSingleton $ filter (P? ∘ f) xs

  ams-filter-reject : ∀ {x : A} {xs : List A} {P : Pred₀ A}
    → (P? : Decidable¹ P)
    → ¬ P x
    → AtMostSingleton $ filter P? xs
    → AtMostSingleton $ filter P? (x ∷ xs)

  ams-filter-accept : ∀ {x : A} {xs : List A} {P : Pred₀ A}
    → (P? : Decidable¹ P)
    → P x
    → Null $ filter P? xs
    → AtMostSingleton $ filter P? (x ∷ xs)

  length≤1⇒ams : ∀ {xs : List A}
    → length xs ≤ 1
    → AtMostSingleton xs

  ams-count : ∀ (P? : Decidable¹ P) {xs : List A} {f : A → Maybe B}
    → (∀ x → P x → Is-just (f x))
    → count P? xs ≤ 1
    → AtMostSingleton (mapMaybe f xs)

  singleton⁺-map⁺ : ∀ {xs : List⁺ A} {f : A → B} →
    Singleton⁺ xs → Singleton⁺ (L.NE.map f xs)

open import Prelude.Lists.Membership
postulate
  lookup≡find∘map⁻ : ∀ {xs : List A} {f : A → B} {P : Pred₀ B}
    → (p : Any P (map f xs))
    → L.Any.lookup p ≡ f (proj₁ $ find $ L.Any.map⁻ p)

  Any-lookup∘map : ∀ {P Q : Pred₀ A}
    → (P⊆Q : ∀ {x} → P x → Q x)
    → (p : Any P xs)
    → L.Any.lookup (L.Any.map P⊆Q p) ≡ L.Any.lookup p

  lookup∘∈-map⁺ : ∀ {f : A → B}
    → (x∈ : x ∈ xs)
    → L.Any.lookup (∈-map⁺ f x∈) ≡ f x

  mapWith∈-id :  mapWith∈ xs (λ {x} _ → x) ≡ xs

  filter-exists : ∀ {_∈?_ : ∀ (x : A) (xs : List A) → Dec (x ∈ xs)} {f : B → A} {x : A} {xs : List A} {ys : List B}
    → (x∈ : x ∈ map f ys)
    → Unique ys
    → filter ((_∈? (x ∷ xs)) ∘ f) ys
    ↭ (proj₁ ∘ ∈-map⁻ f) x∈ ∷ filter ((_∈? xs) ∘ f) ys
-- filter-exists {A = A} {B = B} {_∈?_ = _∈?_} {f = f} {x = x} {xs = xs} {ys = ys} x∈ uniq
--   with ∈-map⁻ f x∈
-- ... | y , y∈ , refl -- y∈  : y ∈ ys
--   with ∈-filter⁺ (_∈? (x ∷ xs) ∘ f) y∈ (here refl)
-- ... | y∈′           -- y∈′ : y ∈ filter _ ys
--     = begin
--         filter ((_∈? (x ∷ xs)) ∘ f) ys
--       ↭⟨ {!!} ⟩
--         y ∷ filter ((_∈? xs) ∘ f) ys
--       ∎ where open PermutationReasoning

mapWith∈↭filter : ∀ {_∈?_ : ∀ (x : A) (xs : List A) → Dec (x ∈ xs)} {f : B → A}
                    {xs : List A} {ys : List B}
  → (p⊆ : xs ⊆ map f ys)
  → Unique ys
  → mapWith∈ xs (proj₁ ∘ ∈-map⁻ f ∘ p⊆)
  ↭ filter ((_∈? xs) ∘ f) ys
mapWith∈↭filter {A = A} {B = B} {_∈?_ = _∈?_} {f = f} {xs = []}     {ys = ys} p⊆ uniq =
  ↭-sym (↭-reflexive $ L.filter-none ((_∈? []) ∘ f) (L.All.universal (λ _ ()) ys))
mapWith∈↭filter {A = A} {B = B} {_∈?_ = _∈?_} {f = f} {xs = x ∷ xs} {ys = ys} p⊆ uniq =
  begin
    mapWith∈ (x ∷ xs) get
  ≡⟨⟩
    get {x} _ ∷ mapWith∈ xs (proj₁ ∘ ∈-map⁻ f ∘ p⊆ ∘ there)
  ↭⟨ ↭-prep (get {x} _) (mapWith∈↭filter {_∈?_ = _∈?_} (p⊆ ∘ there) uniq) ⟩
    get {x} _ ∷ filter ((_∈? xs) ∘ f) ys
  ↭⟨ ↭-sym (filter-exists {_∈?_ = _∈?_} (p⊆ (here refl)) uniq) ⟩
    filter ((_∈? (x ∷ xs)) ∘ f) ys
  ∎ where open PermutationReasoning
          get : ∀ {x′} → x′ ∈ x ∷ xs → B
          get = proj₁ ∘ ∈-map⁻ f ∘ p⊆


open import Prelude.Lists.Suffix
open import Prelude.Lists.NonEmpty
postulate
  Suffix⇒⊆ : Suffix≡ xs ys → xs ⊆ ys

  proj₁∘∈⇒Suffix≡ : {xs : List⁺ A} {ys zs : List A} (∀x∈ : All⁺ (_∈ ys) xs) (ys≼ : Suffix≡ ys zs)
    → (proj₁ ∘ ∈⇒Suffix ∘ All⁺-last ∘ L.All.map (Suffix⇒⊆ ys≼)) ∀x∈
    ≡ (proj₁ ∘ ∈⇒Suffix ∘ All⁺-last) ∀x∈
