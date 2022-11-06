open import Prelude.Init
open L.Any using (index)
open L.Mem using (∈-map⁺; ∈-map⁻)
open L.All using (lookup; ¬All⇒Any¬; ¬Any⇒All¬)
open L.Perm using (drop-∷; drop-mid; ∈-resp-↭)
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Membership
open import Prelude.Decidable
open import Prelude.Ord
open import Prelude.Lists.Count

module Prelude.DecLists {a} {A : Set a} ⦃ _ : DecEq A ⦄ where

private variable
  x y z : A
  xs ys zs : List A

¬∉⇒∈ : ¬ (x ∉ xs) → x ∈ xs
¬∉⇒∈ {x}{xs = []}      ¬x∉ = ⊥-elim $ ¬x∉ λ ()
¬∉⇒∈ {x}{xs = x′ ∷ xs} ¬x∉ with x ≟ x′
... | yes refl = here refl
... | no ¬p    = there (¬∉⇒∈ (λ x∉ → ¬x∉ (λ { (here refl) → ⊥-elim $ ¬p refl; (there x∈) → x∉ x∈})))

instance
  Dec-⊆ : _⊆_ {A = A} ⁇²
  Dec-⊆ {x = []}     {y = ys} .dec = yes λ ()
  Dec-⊆ {x = x ∷ xs} {y = ys} .dec = case x ∈? ys of λ where
    (no  x∉ys) → no λ xs⊆ys → x∉ys (xs⊆ys (here refl))
    (yes x∈ys) → case ¿ xs ⊆ ys ¿ of λ where
      (no  xs⊈ys) → no λ xs⊆ys → xs⊈ys (λ {x} z → xs⊆ys (there z))
      (yes xs⊆ys) → yes λ{ (here refl) → x∈ys
                          ; (there x∈)  → xs⊆ys x∈ }

  Dec-Disjoint : Disjoint {A = A} ⁇²
  Dec-Disjoint {x = xs} {y = ys} .dec with all? (_∉? ys) xs
  ... | yes p = yes (λ {v} (v∈ , v∈′) → lookup p v∈ v∈′ )
  ... | no ¬p = let (x , x∈ , Px) = find $ ¬All⇒Any¬ (_∉? ys) _ ¬p
                in no λ p → p {x} (x∈ , ¬∉⇒∈ Px)

infix 4 _⊆?_
_⊆?_ = ¿ _⊆_ {A = A} ¿²

disjoint? = ¿ Disjoint {A = A} ¿²
unique?   = ¿ Unique {A = A} ¿¹

-- ** nub

nub : List A → List A
nub [] = []
nub (x ∷ xs) with x ∈? xs
... | yes _ = nub xs
... | no  _ = x ∷ nub xs

nub-⊆⁺ : xs ⊆ nub xs
nub-⊆⁺ {xs = x ∷ xs} (here refl)
  with x ∈? xs
... | yes x∈ = nub-⊆⁺ {xs = xs} x∈
... | no  _  = here refl
nub-⊆⁺ {xs = x ∷ xs} (there y∈)
  with x ∈? xs
... | yes _ = nub-⊆⁺ {xs = xs} y∈
... | no  _ = there $ nub-⊆⁺ {xs = xs} y∈

nub-⊆⁻ : nub xs ⊆ xs
nub-⊆⁻ {xs = x ∷ xs}
  with x ∈? xs
... | yes x∈ = there ∘ nub-⊆⁻ {xs = xs}
... | no  _  = λ where
  (here refl) → here refl
  (there y∈)  → there $ nub-⊆⁻ {xs = xs} y∈

All-nub : ∀ {p}{P : Pred A p} → All P xs → All P (nub xs)
All-nub {xs = []}     []       = []
All-nub {xs = x ∷ xs} (p ∷ ps) with x ∈? xs
... | yes _ = All-nub ps
... | no  _ = p ∷ All-nub ps

Unique-nub : Unique (nub xs)
Unique-nub {[]} = []
Unique-nub {x ∷ xs} with x ∈? xs
... | yes _ = Unique-nub {xs}
... | no x∉ = All-nub {xs = xs} {P = _≢_ x} (¬Any⇒All¬ xs x∉) ∷ Unique-nub {xs}

nub-from∘to : Unique xs → nub xs ≡ xs
nub-from∘to {[]}     _ = refl
nub-from∘to {x ∷ xs} u@(_ ∷ Uxs) with x ∈? xs
... | no  _    = cong (x ∷_) (nub-from∘to Uxs)
... | yes x∈xs = ⊥-elim (unique-∈ u x∈xs)

unique-nub-∈ : Unique xs → (x ∈ nub xs) ≡ (x ∈ xs)
unique-nub-∈ uniq rewrite nub-from∘to uniq = refl

∈-nub⁻ : x ∈ nub xs → x ∈ xs
∈-nub⁻ {x}{x′ ∷ xs} x∈
  with x′ ∈? xs
... | yes _ = there (∈-nub⁻ x∈)
... | no ¬p
  with x∈
... | (here refl) = here refl
... | (there x∈ˢ) = there (∈-nub⁻ x∈ˢ)

∈-nub⁺ : x ∈ xs → x ∈ nub xs
∈-nub⁺ {x}{.x ∷ xs} (here refl)
  with x ∈? xs
... | yes x∈ = ∈-nub⁺ x∈
... | no  _  = here refl
∈-nub⁺ {x}{x′ ∷ xs} (there x∈)
  with x′ ∈? xs
... | yes x∈ˢ = ∈-nub⁺ x∈
... | no  _   = there $ ∈-nub⁺ x∈

∈-map∘nub⁻ : ∀ {B : Set ℓ} (f : A → B) x xs →
  f x L.Mem.∈ map f (nub xs) → f x L.Mem.∈ map f xs
∈-map∘nub⁻ f _ []       fx∈ = fx∈
∈-map∘nub⁻ f x (y ∷ xs) fx∈ with y ∈? xs
... | yes y∈ = there $ ∈-map∘nub⁻ f x xs fx∈
... | no  y∉ with fx∈
... | here  eq   = here eq
... | there fx∈′ = there $ ∈-map∘nub⁻ f x xs fx∈′

‼-nub⁺ : Index xs → Index (nub xs)
‼-nub⁺ {x ∷ xs} i with x ∈? xs
... | yes x∈ = ‼-nub⁺ {xs} $ L.Any.index x∈
... | no  _ = case i of λ where
  0F → 0F
  (fsuc j) → fsuc $ ‼-nub⁺ {xs} j

‼-nub⁻ : Index (nub xs) → Index xs
‼-nub⁻ {x ∷ xs} i with x ∈? xs
... | yes x∈ = fsuc $ ‼-nub⁻ {xs} i
... | no  _ = case i of λ where
  0F → 0F
  (fsuc j) → fsuc $ ‼-nub⁻ {xs} j

-- ** nubBy

module _ {B : Set ℓ} where

  -- NB: right-biased, e.g. nubBy ∣_∣ [-1,0,1] = [0,1]
  nubBy : (B → A) → List B → List B
  nubBy f [] = []
  nubBy f (x ∷ xs) with f x ∈? map f xs
  ... | yes _ = nubBy f xs
  ... | no  _ = x ∷ nubBy f xs

  All-nubBy : ∀ {p}{P : Pred B p} (f : B → A) xs → All P xs → All P (nubBy f xs)
  All-nubBy f []       []       = []
  All-nubBy f (x ∷ xs) (p ∷ ps) with f x ∈? map f xs
  ... | yes _ = All-nubBy f xs ps
  ... | no  _ = p ∷ All-nubBy f xs ps

  module _ (f : B → A) where
    ∈-nubBy⁻ : ∀ (x : B) xs → x ∈ nubBy f xs → x ∈ xs
    ∈-nubBy⁻ x (y ∷ xs) x∈ with f y ∈? map f xs
    ... | yes _ = there (∈-nubBy⁻ x xs x∈)
    ... | no  _ with x∈
    ... | here refl = here refl
    ... | there x∈′ = there (∈-nubBy⁻ x xs x∈′)

    ∈-map∘nubBy⁻ : ∀ (x : B) xs → f x ∈ map f (nubBy f xs) → f x ∈ map f xs
    ∈-map∘nubBy⁻ _ []       fx∈ = fx∈
    ∈-map∘nubBy⁻ x (y ∷ xs) fx∈ with f y ∈? map f xs
    ... | yes y∈ = there $ ∈-map∘nubBy⁻ x xs fx∈
    ... | no  y∉ with fx∈
    ... | here  eq   = here eq
    ... | there fx∈′ = there $ ∈-map∘nubBy⁻ x xs fx∈′

    -- ∈-nubBy⁺ : ∀ (xs : List B) → x ∈ xs → x ∈ nubBy f xs
    -- ∈-nubBy⁺ (y ∷ xs) x∈ with f y ∈? map f xs
    -- ∈-nubBy⁺ (y ∷ xs) x∈ | yes fy∈ with x∈
    -- ... | here refl with x′ , fx∈ , eq ← ∈-map⁻ f fy∈ = ∈-nubBy⁺ xs {!!}
    -- ... | there x∈′ = ∈-nubBy⁺ xs x∈′
    -- ∈-nubBy⁺ (y ∷ xs) x∈ | no  _ with x∈
    -- ... | here refl = here refl
    -- ... | there x∈′ = there (∈-nubBy⁺ xs x∈′)

    Unique-nubBy : ∀ xs → Unique (nubBy f xs)
    Unique-nubBy [] = []
    Unique-nubBy (x ∷ xs) with f x ∈? map f xs
    ... | yes _  = Unique-nubBy xs
    ... | no fx∉ = All-nubBy f xs (¬Any⇒All¬ xs (fx∉ ∘ ∈-map⁺ f))
                 ∷ Unique-nubBy xs

    Unique-map∘nubBy : ∀ xs → Unique $ map f (nubBy f xs)
    Unique-map∘nubBy [] = []
    Unique-map∘nubBy (x ∷ xs) with f x ∈? map f xs
    ... | yes _  = Unique-map∘nubBy xs
    ... | no fx∉ = ¬Any⇒All¬ (map f (nubBy f xs)) (fx∉ ∘ ∈-map∘nubBy⁻ x xs )
                 ∷ Unique-map∘nubBy xs

-- ** deletion

_\\_ : List A → List A → List A
xs \\ [] = xs
xs \\ (x ∷ ys) with x ∈? xs
... | no _     = xs \\ ys
... | yes x∈xs = (remove xs (index x∈xs)) \\ ys

\\-left : [] ≡ [] \\ xs
\\-left {[]}     = refl
\\-left {x ∷ ys} with x ∈? (List _ ∋ [])
... | no _ = \\-left {ys}
... | yes ()

\\-head : [] ≡ [ x ] \\ (x ∷ xs)
\\-head {x = x} {xs = xs} with x ∈? [ x ]
... | no ¬p = ⊥-elim (¬p (here refl))
... | yes p with index p
... | 0F = \\-left {xs = xs}
... | fsuc ()

\\-‼ : ∀ {i : Index xs}
      → [] ≡ [ xs ‼ i ] \\ xs
\\-‼ {xs = []} {()}
\\-‼ {xs = x ∷ xs} {0F} with x ∈? [ x ]
... | no ¬p = ⊥-elim (¬p (here refl))
... | yes (here relf) = \\-left {xs = xs}
... | yes (there ())
\\-‼ {xs = x ∷ xs} {fsuc i} with x ∈? [ xs ‼ i ]
... | no ¬p = \\-‼ {xs = xs} {i}
... | yes (here refl) = \\-left {xs = xs}
... | yes (there ())

postulate \\-⊆ : xs \\ ys ⊆ xs

-- ** permutation binary relation

private
  ¬[]↭ : ¬ ([] ↭ x ∷ xs)
  ¬[]↭ (↭-trans {.[]} {[]}     {.(_ ∷ _)} []↭ []↭₁) = ¬[]↭ []↭₁
  ¬[]↭ (↭-trans {.[]} {x ∷ ys} {.(_ ∷ _)} []↭ []↭₁) = ¬[]↭ []↭

  ↭-remove : ∀  {x∈ : x ∈ ys} → x ∷ remove ys (index x∈) ↭ ys
  ↭-remove {x} {.(x ∷ _)}       {here refl}          = ↭-refl
  ↭-remove {x} {(y ∷ x ∷ _)}    {there (here refl)}  = ↭-swap x y ↭-refl
  ↭-remove {x} {(x₁ ∷ x₂ ∷ ys)} {there (there x∈ys)} = ↭-trans h₁ h₂
    where
      ys′ : List A
      ys′ = remove ys (index x∈ys)

      h₁ : x ∷ x₁ ∷ x₂ ∷ ys′ ↭ x₁ ∷ x₂ ∷ x ∷ ys′
      h₁ = ↭-trans (↭-swap x x₁ ↭-refl) (↭-prep x₁ (↭-swap x x₂ ↭-refl))

      h₂ : x₁ ∷ x₂ ∷ x ∷ ys′ ↭ x₁ ∷ x₂ ∷ ys
      h₂ = ↭-prep x₁ (↭-prep x₂ ↭-remove)

  ↭-helper→ : ∀ {x∈ : x ∈ ys}
    → xs ↭ remove ys (index x∈)
    → x ∷ xs ↭ ys
  ↭-helper→ {x} {xs} {ys} h = ↭-trans (↭-prep x h) ↭-remove

  ↭-helper← : ∀ {x∈ : x ∈ ys}
    → x ∷ xs ↭ ys
    → xs ↭ remove ys (index x∈)
  ↭-helper← {x} {x ∷ _}        {x∈ = here refl}          = drop-∷
  ↭-helper← {x} {y ∷ x ∷ _}    {x∈ = there (here refl)}  = drop-mid [] [ y ]
  ↭-helper← {x} {x₁ ∷ x₂ ∷ ys} {x∈ = there (there x∈ys)} = drop-∷ ∘ flip ↭-trans h
    where
      ys′ = remove ys (index x∈ys)

      h′ : x₂ ∷ ys ↭ x ∷ x₂ ∷ ys′
      h′ = ↭-trans (↭-prep x₂ $ ↭-sym ↭-remove) (↭-swap x₂ x ↭-refl)

      h : x₁ ∷ x₂ ∷ ys ↭ x ∷ x₁ ∷ x₂ ∷ ys′
      h = ↭-trans (↭-prep x₁ h′) (↭-swap x₁ x ↭-refl)

instance
  Dec-↭ : _↭_ {A = A} ⁇²
  Dec-↭ {x = xs} {y = ys} .dec with xs | ys
  ... | []      | []    = yes ↭-refl
  ... | []      | _ ∷ _ = no ¬[]↭
  ... | x ∷ xs′ | ys′   with x ∈? ys′
  ... | no  x∉          = no λ x∷xs↭ → x∉ (∈-resp-↭ x∷xs↭ (here refl))
  ... | yes x∈          with ¿ xs′ ↭ remove ys′ (index x∈) ¿
  ... | no ¬xs↭         = no (¬xs↭ ∘ ↭-helper←)
  ... | yes xs↭         = yes (↭-helper→ xs↭)

_↭?_ = ¿ _↭_ {A = A} ¿²

-- ** interleaving ternary relation

instance
  Dec-Interleaving : _∥_≡_ {A = A} ⁇³
  Dec-Interleaving {x = xs} {y = ys} {z = zs} .dec
    with xs | ys | zs
  ... | []     | []     | []    = yes []
  ... | []     | []     | _ ∷ _ = no λ ()
  ... | _ ∷ _  | _      | []    = no λ ()
  ... | _      | _ ∷ _  | []    = no λ ()
  ... | xˡ ∷ l | []     | x ∷ l↔r
      = case xˡ ≟ x of λ where
          (yes refl) → case ¿ l ∥ [] ≡ l↔r ¿ of λ where
            (yes p) → yes (keepˡ p)
            (no ¬p) → no (λ where (keepˡ p) → ¬p p)
          (no x≢) → no λ where (keepˡ _) → x≢ refl
  ... | [] | xʳ ∷ r | x ∷ l↔r
      = case xʳ ≟ x of λ where
          (yes refl) → case ¿ [] ∥ r ≡ l↔r ¿ of λ where
            (yes p) → yes (keepʳ p)
            (no ¬p) → no (λ where (keepʳ p) → ¬p p)
          (no x≢) → no λ where (keepʳ _) → x≢ refl
  ... | xˡ ∷ l | xʳ ∷ r | x ∷ l↔r
    with ¿ (xˡ ≡ x) × (l ∥ (xʳ ∷ r) ≡ l↔r) ¿
  ... | yes (refl , p) = yes (keepˡ p)
  ... | no x≢×¬pˡ
    with ¿ (xʳ ≡ x) × ((xˡ ∷ l) ∥ r ≡ l↔r) ¿
  ... | yes (refl , p) = yes (keepʳ p)
  ... | no x≢×¬pʳ = no λ where
      (keepˡ l↔r′) → x≢×¬pˡ (refl , l↔r′)
      (keepʳ l↔r′) → x≢×¬pʳ (refl , l↔r′)

_∥_≟_ = ¿ _∥_≡_ {A = A} ¿³

-- ** bag inclusion
_⊆[bag]_ _⊈[bag]_ : Rel (List A) _
xs ⊆[bag] ys = All (λ x → count (_≟ x) xs ≤ count (_≟ x) ys) (nub xs)
_⊈[bag]_ = ¬_ ∘₂ _⊆[bag]_

_⊆[bag]?_ = Decidable² _⊆[bag]_ ∋ dec²

_∸[bag]_ _*[bag]_ : Op₂ (List A)
xs ∸[bag] ys = concatMap (λ x → L.replicate (count (_≟ x) xs ∸ count (_≟ x) ys) x) (nub xs)
ys *[bag] xs = concatMap (λ x → L.replicate (count (_≟ x) xs * count (_≟ x) ys) x) (nub xs)
