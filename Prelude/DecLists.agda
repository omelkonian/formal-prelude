open import Prelude.Init
open import Prelude.Membership
open import Prelude.Lists
open import Prelude.DecEq

module Prelude.DecLists {A : Set} ⦃ _ : DecEq A ⦄ where
  private
    variable
      x y z : A
      xs ys zs : List A

  infix 4 _⊆?_
  _⊆?_ : (xs : List A) → (ys : List A) → Dec (xs ⊆ ys)
  []       ⊆? ys  = yes λ ()
  (x ∷ xs) ⊆? ys  with x ∈? ys
  ... | no  x∉ys  = no λ xs⊆ys → x∉ys (xs⊆ys (here refl))
  ... | yes x∈ys  with xs ⊆? ys
  ... | no  xs⊈ys = no λ xs⊆ys → xs⊈ys (λ {x} z → xs⊆ys (there z))
  ... | yes xs⊆ys = yes λ{ (here refl) → x∈ys
                         ; (there x∈)  → xs⊆ys x∈ }

  ¬∉⇒∈ : ¬ (x ∉ xs) → x ∈ xs
  ¬∉⇒∈ {x}{xs = []}      ¬x∉ = ⊥-elim $ ¬x∉ λ ()
  ¬∉⇒∈ {x}{xs = x′ ∷ xs} ¬x∉ with x ≟ x′
  ... | yes refl = here refl
  ... | no ¬p    = there (¬∉⇒∈ (λ x∉ → ¬x∉ (λ { (here refl) → ⊥-elim $ ¬p refl; (there x∈) → x∉ x∈})))

  disjoint? : Decidable² {A = List A} Disjoint
  disjoint? xs ys with all? (_∉? ys) xs
  ... | yes p = yes (λ {v} (v∈ , v∈′) → L.All.lookup p v∈ v∈′ )
  ... | no ¬p = let (x , x∈ , Px) = find $ L.All.¬All⇒Any¬ (_∉? ys) _ ¬p
                in no λ p → p {x} (x∈ , ¬∉⇒∈ Px)

  unique? : (xs : List A) → Dec (Unique xs)
  unique? xs = allPairs? (λ x y → ¬? (x ≟ y)) xs

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

  nubBy : ∀ {B : Set} → (B → A) → List B → List B
  nubBy f [] = []
  nubBy f (x ∷ xs) with f x ∈? map f xs
  ... | yes _ = nubBy f xs
  ... | no  _ = x ∷ nubBy f xs

  nub-all : ∀ {P : A → Set} → All P xs → All P (nub xs)
  nub-all {xs = []}     []       = []
  nub-all {xs = x ∷ xs} (p ∷ ps) with x ∈? xs
  ... | yes _ = nub-all ps
  ... | no  _ = p ∷ nub-all ps

  nub-unique : Unique (nub xs)
  nub-unique {[]} = []
  nub-unique {x ∷ xs} with x ∈? xs
  ... | yes _ = nub-unique {xs}
  ... | no x∉ = nub-all {xs = xs} {P = _≢_ x} (L.All.¬Any⇒All¬ xs x∉) ∷ nub-unique {xs}

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

  open L.Any using (index)
  open import Data.List.Relation.Binary.Permutation.Propositional.Properties
    using (∈-resp-↭; drop-∷; drop-mid)

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

  -- ** permutation relation

  ¬[]↭ : ¬ ([] ↭ x ∷ xs)
  ¬[]↭ (↭-trans {.[]} {[]}     {.(_ ∷ _)} []↭ []↭₁) = ¬[]↭ []↭₁
  ¬[]↭ (↭-trans {.[]} {x ∷ ys} {.(_ ∷ _)} []↭ []↭₁) = ¬[]↭ []↭

  ↭-remove : ∀ {x : A} {ys : List A} {x∈ys : x ∈ ys}
           → x ∷ remove ys (index x∈ys) ↭ ys
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

  ↭-helper : ∀ {x∈ys : x ∈ ys}
           → xs ↭ remove ys (index x∈ys)
           → x ∷ xs ↭ ys
  ↭-helper {x} {xs} {ys} {x∈ys} h = ↭-trans (↭-prep x h) ↭-remove

  ↭-helper′ : ∀ {x∈ys : x ∈ ys}
         → x ∷ xs ↭ ys
         → xs ↭ remove ys (index x∈ys)
  ↭-helper′ {x} {.(x ∷ _)}       {xs} {here refl}          h = drop-∷ h
  ↭-helper′ {x} {(y ∷ x ∷ _)}    {xs} {there (here refl)}  h = drop-mid [] [ y ] h
  ↭-helper′ {x} {(x₁ ∷ x₂ ∷ ys)} {xs} {there (there x∈ys)} h = drop-∷ {x = x} (↭-trans h h′)
    where
      ys′ : List A
      ys′ = remove ys (index x∈ys)

      h‴ : ys ↭ x ∷ ys′
      h‴ = ↭-sym ↭-remove

      h″ : x₂ ∷ ys ↭ x ∷ x₂ ∷ ys′
      h″ = ↭-trans (↭-prep x₂ h‴) (↭-swap x₂ x ↭-refl)

      h′ : x₁ ∷ x₂ ∷ ys ↭ x ∷ x₁ ∷ x₂ ∷ ys′
      h′ = ↭-trans (↭-prep x₁ h″) (↭-swap x₁ x ↭-refl)

  _↭?_ : (xs : List A) → (ys : List A) → Dec (xs ↭ ys)
  []       ↭? []       = yes ↭-refl
  []       ↭? (x ∷ ys) = no ¬[]↭
  (x ∷ xs) ↭? ys       with x ∈? ys
  ... | no  x∉         = no λ x∷xs↭ → x∉ (∈-resp-↭ x∷xs↭ (here refl))
  ... | yes x∈         with xs ↭? remove ys (index x∈)
  ... | no ¬xs↭        = no (¬xs↭ ∘ ↭-helper′)
  ... | yes xs↭        = yes (↭-helper xs↭)
