------------------------------------------------------------------------
-- Properties of permuting lists with _↭_

{-# OPTIONS --safe #-}
module Prelude.Lists.Permutations where

open import Prelude.Init; open SetAsType
open import Prelude.Bifunctor
open L.Mem using (_∈_; mapWith∈)
open L.Perm using (shifts; ++⁺ˡ; ++⁺ʳ; map⁺; ↭-sym-involutive; ++-comm)
open import Prelude.Null
open import Prelude.Lists.Empty

private variable
  A B : Type ℓ
  x y : A
  xs ys zs ws : List A
  xss yss : List (List A)

Null-↭ : xs ↭ ys → Null xs → Null ys
Null-↭ = length≡⇒Null ∘ L.Perm.↭-length

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

Unique-resp-↭ : Unique {A = A} Respects _↭_
Unique-resp-↭ ↭-refl = id
Unique-resp-↭ (↭-prep _ xs↭) (x∉ ∷ p)
  = L.Perm.All-resp-↭ xs↭ x∉
  ∷ Unique-resp-↭ xs↭ p
Unique-resp-↭ (↭-swap _ _ xs↭) ((x≢y ∷ x∉xs) ∷ y∉xs ∷ p)
  = (≢-sym x≢y ∷ L.Perm.All-resp-↭ xs↭ y∉xs)
  ∷ (L.Perm.All-resp-↭ xs↭ x∉xs ∷ Unique-resp-↭ xs↭ p)
Unique-resp-↭ (↭-trans p₁ p₂)
  = Unique-resp-↭ p₂
  ∘ Unique-resp-↭ p₁

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

-- ** _∈_
open L.Mem -- using (_∈_; mapWith∈; ∈-++⁻)
open L.Perm using (∈-resp-↭; Any-resp-↭)

∈-resp-↭∘∈-resp-↭ :
  (p : xs ↭ ys) (q : ys ↭ zs) (x∈ : x L.Mem.∈ xs) →
  --——————————————————————————————————————————————————————
  ∈-resp-↭ q (∈-resp-↭ p x∈) ≡ ∈-resp-↭ (↭-trans p q) x∈
∈-resp-↭∘∈-resp-↭ p q x∈ =
  begin
      ∈-resp-↭ q (∈-resp-↭ p x∈)
    ≡⟨⟩
      ∈-resp-↭ (↭-trans p q) x∈
    ∎ where open ≡-Reasoning

Any-resp-↭∘Any-resp-↭˘ : ∀ {x : A} {xs ys : List A}
    (p↭ : xs ↭ ys)
    (x∈ : x ∈ xs)
    --——————————————————————————————————————————
  → (Any-resp-↭ (↭-sym p↭) ∘ Any-resp-↭ p↭) x∈ ≡ x∈
Any-resp-↭∘Any-resp-↭˘ ↭-refl _ = refl
Any-resp-↭∘Any-resp-↭˘ (↭-prep _ _) (here _) = refl
Any-resp-↭∘Any-resp-↭˘ (↭-prep x p↭) (there p)
  = cong there $ Any-resp-↭∘Any-resp-↭˘ p↭ p
Any-resp-↭∘Any-resp-↭˘ (↭-swap _ _ _) (here _) = refl
Any-resp-↭∘Any-resp-↭˘ (↭-swap _ _ _) (there (here _)) = refl
Any-resp-↭∘Any-resp-↭˘ (↭-swap x y p↭) (there (there p))
  = cong there $ cong there $ Any-resp-↭∘Any-resp-↭˘ p↭ p
Any-resp-↭∘Any-resp-↭˘ (↭-trans p↭ p↭′) p
  rewrite Any-resp-↭∘Any-resp-↭˘ p↭′ (Any-resp-↭ p↭ p)
  = Any-resp-↭∘Any-resp-↭˘ p↭ p

Any-resp-↭˘∘Any-resp-↭ : ∀ {x : A} {xs ys : List A}
    (p↭ : xs ↭ ys)
    (x∈ : x ∈ ys)
    --——————————————————————————————————————————
  → (Any-resp-↭ p↭ ∘ Any-resp-↭ (↭-sym p↭)) x∈ ≡ x∈
Any-resp-↭˘∘Any-resp-↭ p↭ x∈ =
  begin
    ( Any-resp-↭ p↭
    ∘ Any-resp-↭ (↭-sym p↭)
    ) x∈
  ≡˘⟨ cong (λ ◆ → (Any-resp-↭ ◆ ∘ Any-resp-↭ (↭-sym p↭)) x∈)
         $ L.Perm.↭-sym-involutive p↭ ⟩
    ( Any-resp-↭ (↭-sym $ ↭-sym p↭)
    ∘ Any-resp-↭ (↭-sym p↭)
    ) x∈
  ≡⟨ Any-resp-↭∘Any-resp-↭˘ (↭-sym p↭) x∈ ⟩
    x∈
  ∎ where open ≡-Reasoning

∈-resp-↭∘∈-resp-↭˘ : ∀ {x : A} {xs ys : List A}
    (p↭ : xs ↭ ys)
    (x∈ : x ∈ xs)
    --——————————————————————————————————————————
  → (∈-resp-↭ (↭-sym p↭) ∘ ∈-resp-↭ p↭) x∈ ≡ x∈
∈-resp-↭∘∈-resp-↭˘ = Any-resp-↭∘Any-resp-↭˘

∈-resp-↭˘∘∈-resp-↭ : ∀ {x : A} {xs ys : List A}
    (p↭ : xs ↭ ys)
    (x∈ : x ∈ ys)
    --——————————————————————————————————————————
  → (∈-resp-↭ p↭ ∘ ∈-resp-↭ (↭-sym p↭)) x∈ ≡ x∈
∈-resp-↭˘∘∈-resp-↭ = Any-resp-↭˘∘Any-resp-↭

-- ** map
module _ {A : Type ℓ} {B : Type ℓ′} (f : A → B) where

  ∈-map-resp-↭ : ∀ {xs ys} → xs ↭ ys → map f xs ⊆ map f ys
  ∈-map-resp-↭ xs↭ys = ∈-resp-↭ $ map⁺ f xs↭ys

  ∈-map-resp-↭∘∈-map-resp-↭˘ : ∀ {fx : B} {xs ys} →
    (p : xs ↭ ys)
    (fx∈ : fx ∈ map f xs)
    --——————————————————————————
    → ( ∈-map-resp-↭ (↭-sym p)
      ∘ ∈-map-resp-↭ p
      ) fx∈
    ≡ fx∈
  ∈-map-resp-↭∘∈-map-resp-↭˘ {xs = xs}{ys} p fx∈ =
    begin
      ( ∈-map-resp-↭ (↭-sym p)
      ∘ ∈-map-resp-↭ p
      ) fx∈
    ≡⟨⟩
      ( ∈-resp-↭ (map⁺ f (↭-sym p))
      ∘ ∈-resp-↭ (map⁺ f p)
      ) fx∈
    ≡˘⟨ cong (λ ◆ → ∈-resp-↭ ◆ $ ∈-resp-↭ (map⁺ f p) fx∈) $ ↭-sym∘map⁺ f p ⟩
      ( ∈-resp-↭ (↭-sym $ map⁺ f p)
      ∘ ∈-resp-↭ (map⁺ f p)
      ) fx∈
    ≡⟨ ∈-resp-↭∘∈-resp-↭˘ (map⁺ f p) _ ⟩
      fx∈
    ∎ where open ≡-Reasoning


  ∈-map⁺′ : ∀ {y xs} → (∃ λ x → x ∈ xs × y ≡ f x) → y ∈ map f xs
  ∈-map⁺′ = L.Any.map⁺ ∘ L.Mem.∃∈-Any

  ∈-map⁺′∘∈-map⁻ : ∀ {y : B} {xs : List A} →
    (x∈ : y ∈ map f xs)
    --——————————————————————————
    → ( ∈-map⁺′
      ∘ ∈-map⁻ f
      ) x∈
    ≡ x∈
  ∈-map⁺′∘∈-map⁻ {y = y}{xs} x∈ =
    begin
      ( ∈-map⁺′
      ∘ ∈-map⁻ f
      ) x∈
    ≡⟨⟩
      ( LA.map⁺
      ∘ L.Mem.∃∈-Any
      ∘ find
      ∘ LA.map⁻
      ) x∈
    ≡⟨ cong LA.map⁺ $ lose∘find _ ⟩
      ( LA.map⁺
      ∘ LA.map⁻
      ) x∈
    ≡⟨ L.Any.map⁺∘map⁻ _ ⟩
      x∈
    ∎ where open ≡-Reasoning; module LA = L.Any

  ∈-map⁻∘∈-map⁺′ : ∀ {y : B} {xs : List A} →
    (x∈ : ∃ λ x → x ∈ xs × y ≡ f x)
    --——————————————————————————
    → ( ∈-map⁻ f
      ∘ ∈-map⁺′
      ) x∈
    ≡ x∈
  ∈-map⁻∘∈-map⁺′ {y = y}{xs} x∈ =
    begin
      ( ∈-map⁻ f -- ∃x. (x ∈ xs) × (y ≡ f x)
      ∘ ∈-map⁺′  -- y ∈ map f xs
      ) x∈       -- ∃x. (x ∈ xs) × (y ≡ f x)
    ≡⟨⟩
      ( find         -- ∃x. (x ∈ xs) × (y ≡ f x)
      ∘ LA.map⁻      -- Any ((y ≡_) ∘ f) xs
      ∘ LA.map⁺      -- Any (y ≡_) (map f xs)
      ∘ L.Mem.∃∈-Any -- Any ((y ≡_) ∘ f) xs
      ) x∈           -- ∃x. (x ∈ xs) × (y ≡ f x)
    ≡⟨ cong find $ L.Any.map⁻∘map⁺ (y ≡_) (L.Mem.∃∈-Any x∈) ⟩
      ( find         -- ∃x. (x ∈ xs) × (y ≡ f x)
      ∘ L.Mem.∃∈-Any -- Any ((y ≡_) ∘ f) xs
      ) x∈           -- ∃x. (x ∈ xs) × (y ≡ f x)
    ≡⟨ find∘lose _ _ _ ⟩
      x∈
    ∎ where open ≡-Reasoning; module LA = L.Any


  ∈-map-resp-↭′ : ∀ {xs ys} → xs ↭ ys → map f xs ⊆ map f ys
  ∈-map-resp-↭′ {ys = ys} xs↭ =
    ( ∈-map⁺′                     -- y ∈ map f ys
    ∘ map₂′ (map₁ $ ∈-resp-↭ xs↭) -- (x ∈ ys) × (y ≡ f x)
    ∘ ∈-map⁻ f                    -- (x ∈ xs) × (y ≡ f x)
    )

  ∈-map-resp-↭′∘∈-map-resp-↭′˘ : ∀ {fx : B} {xs ys} →
    (p : xs ↭ ys)
    (fx∈ : fx ∈ map f xs)
    --——————————————————————————
    → ( ∈-map-resp-↭′ (↭-sym p)
      ∘ ∈-map-resp-↭′ p
      ) fx∈
    ≡ fx∈
  ∈-map-resp-↭′∘∈-map-resp-↭′˘ {xs = xs}{ys} p fx∈ =
    begin
      ( ∈-map-resp-↭′ (↭-sym p)
      ∘ ∈-map-resp-↭′ p
      ) fx∈
    ≡⟨⟩
      ( ∈-map⁺′                           -- (f x ∈ map f xs)
      ∘ map₂′ (map₁ $ ∈-resp-↭ (↭-sym p)) -- ∃x. (x ∈ xs) × —//—
      ∘ ∈-map⁻ f                          -- ∃x. (x ∈ ys) × (fx ≡ f x)
      ∘ ∈-map⁺′                           -- (fx ∈ map f ys)
      ∘ map₂′ (map₁ $ ∈-resp-↭ p)         -- ∃x. (x ∈ ys) × –‌//—
      ∘ ∈-map⁻ f                          -- ∃x. (x ∈ xs) × (fx ≡ f x)
      ) fx∈                               -- fx ∈ map f xs
    ≡⟨ cong (∈-map⁺′ ∘ map₂′ (map₁ $ ∈-resp-↭ (↭-sym p)))
         $ ∈-map⁻∘∈-map⁺′ (map₂′ (map₁ $ ∈-resp-↭ p) (∈-map⁻ f fx∈)) ⟩
      ( ∈-map⁺′
      ∘ map₂′ (map₁ $ ∈-resp-↭ (↭-sym p))
      ∘ map₂′ (map₁ $ ∈-resp-↭ p)
      ∘ ∈-map⁻ f
      ) fx∈
    ≡⟨⟩
      ( ∈-map⁺′
      ∘ map₂′ (map₁ $ ∈-resp-↭ (↭-sym p) ∘ ∈-resp-↭ p)
      ∘ ∈-map⁻ f
      ) fx∈
    ≡⟨⟩
      let x , x∈ , fx≡ = ∈-map⁻ f fx∈
      in ∈-map⁺′ (x , ∈-resp-↭ (↭-sym p) (∈-resp-↭ p x∈) , fx≡)
    ≡⟨ cong (λ ◆ → let x , _ , fx≡ = ∈-map⁻ f fx∈
                   in ∈-map⁺′ (x , ◆ , fx≡))
        $ ∈-resp-↭∘∈-resp-↭˘ p _ ⟩
      let x , x∈ , fx≡ = ∈-map⁻ f fx∈
      in ∈-map⁺′ (x , x∈ , fx≡)
    ≡⟨⟩
      ∈-map⁺′ (∈-map⁻ f fx∈)
    ≡⟨ ∈-map⁺′∘∈-map⁻ _ ⟩
      fx∈
    ∎ where open ≡-Reasoning
