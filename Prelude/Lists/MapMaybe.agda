module Prelude.Lists.MapMaybe where

open import Prelude.Init
open Nat.Ord
open L.Mem
open import Prelude.General
open import Prelude.InferenceRules
open import Prelude.Bifunctor
open import Prelude.Lists.Empty
open import Prelude.Lists.Indexed
open import Prelude.Lists.Count
open import Prelude.Lists.Membership
open import Prelude.Split

private variable
  a b : Level; A : Set a; B : Set b
  x x′ y : A; xs ys : List A

module MapMaybeDSL (f : A → Maybe B) where
  ⊥⋯_ _⋯⊥ ⊤⋯_ _⋯⊤ : ∀ {x : A} → x ∈ xs → ℕ
  ⊥⋯ x∈ = countNothing f (x∈ ∙left)
  ⊤⋯ x∈ = countJust    f (x∈ ∙left)
  x∈ ⋯⊥ = countNothing f (x∈ ∙right)
  x∈ ⋯⊤ = countJust    f (x∈ ∙right)

  countNothing≡⊥⋯⊥ : (x∈ : x ∈ xs) → countNothing f xs ≡ ⊥⋯ x∈ + x∈ ⋯⊥
  countNothing≡⊥⋯⊥ {xs = x ∷ xs} (here refl)
    with f x
  ... | nothing = refl
  ... | just _  = refl
  countNothing≡⊥⋯⊥ {xs = x ∷ xs} (there x∈)
    with f x
  ... | nothing = cong suc (countNothing≡⊥⋯⊥ x∈)
  ... | just _  = countNothing≡⊥⋯⊥ x∈

  countNothing≤ : (x∈ : x ∈ xs) → ⊥⋯ x∈ ≤ suc (indexℕ x∈)
  countNothing≤ {xs = xs} x∈ =
    begin ⊥⋯ x∈                      ≡⟨⟩
          countNothing f (x∈ ∙left) ≤⟨ length-count (is-nothing? ∘ f) {xs = x∈ ∙left} ⟩
          length (x∈ ∙left)         ≡⟨ length-∈∙left x∈ ⟩
          suc (indexℕ x∈)           ∎ where open ≤-Reasoning

module _ (f : A → Maybe B) where
  open MapMaybeDSL f

  mapMaybe-++ : ∀ xs ys → mapMaybe f (xs ++ ys) ≡ mapMaybe f xs ++ mapMaybe f ys
  mapMaybe-++ []       ys = refl
  mapMaybe-++ (x ∷ xs) ys with f x
  ... | just _  = cong (_ ∷_) (mapMaybe-++ xs ys)
  ... | nothing = mapMaybe-++ xs ys

  mapMaybe-skip : f x ≡ nothing → mapMaybe f (x ∷ xs) ≡ mapMaybe f xs
  mapMaybe-skip {x = x} _ with nothing ← f x = refl

  ∈-mapMaybe⁻ : y ∈ mapMaybe f xs
              → ∃ λ x → (x ∈ xs) × (f x ≡ just y)
  ∈-mapMaybe⁻ {y = y} {xs = x ∷ xs} y∈
  -- [BUG] `in` does not work like `inspect`...
  --   with f x in fx≡
    with f x | inspect f x
  ... | nothing | _ = map₂′ (map₁′ there) (∈-mapMaybe⁻ y∈)
  ... | just y′ | ≡[ fx≡ ]
    with y∈
  ... | here refl = x , here refl , fx≡
  ... | there y∈′ = map₂′ (map₁′ there) (∈-mapMaybe⁻ y∈′)

  ∈-mapMaybe⁻-nothing : (y∈ : y ∈ mapMaybe f (x ∷ xs))
    → f x ≡ nothing
    → Is-there $ ∈-mapMaybe⁻ y∈ .proj₂ .proj₁
  ∈-mapMaybe⁻-nothing {x = x} {xs = xs} y∈ fx≡
    with f x | inspect f x | fx≡
  ... | nothing | _ | _ = tt
  ... | just _  | _ | ()

  ∈-mapMaybe⁻-here : (y∈ : y ∈ mapMaybe f (x ∷ xs))
    → Is-here $ ∈-mapMaybe⁻ y∈ .proj₂ .proj₁
    → Is-here y∈
  ∈-mapMaybe⁻-here {x = x} {xs = xs} y∈ y∈≡
    with f x | inspect f x
  ... | nothing | _ = case y∈≡ of λ ()
  ... | just _ | _ with here _ ← y∈ = tt

  ∈-mapMaybe⁺ : x ∈ xs → f x ≡ just y → y ∈ mapMaybe f xs
  ∈-mapMaybe⁺ {xs = x ∷ xs} x∈ eq with x∈
  ... | here refl with just y ← f x -- in fx≡ [BUG]
    = here $ M.just-injective (sym eq)
  ... | there x∈ with IH ← ∈-mapMaybe⁺ x∈ eq
    with f x
  ... | nothing = IH
  ... | just _  = there IH

  mapMaybe-here : (eq : f x ≡ just y)
    → mapMaybe f (x ∷ xs) ≡ y ∷ mapMaybe f xs
  mapMaybe-here {x = x} eq with just _ ← f x = cong (_∷ _) (M.just-injective eq)

  ∈-mapMaybe⁺-here : (eq : f x ≡ just y)
    → Is-here $ ∈-mapMaybe⁺ (here {xs = xs} refl) eq
  ∈-mapMaybe⁺-here {x = x} {y = y} {xs = xs} eq with just _ ← f x = _

  mapMaybe-⊆ : xs ⊆ ys → mapMaybe f xs ⊆ mapMaybe f ys
  mapMaybe-⊆ {xs = x ∷ xs} {ys = ys} xs⊆ fx∈ =
    let x , x∈ , fx≡ = ∈-mapMaybe⁻ fx∈
    in  ∈-mapMaybe⁺ (xs⊆ x∈) fx≡

  mapMaybe-↭ : xs ↭ ys → mapMaybe f xs ↭ mapMaybe f ys
  mapMaybe-↭ {xs = xs} {ys = .xs} ↭-refl = ↭-refl
  mapMaybe-↭ {xs = .(x ∷ _)} {ys = .(x ∷ _)} (↭-prep x xs↭ys)
    with IH ← mapMaybe-↭ xs↭ys
    with f x
  ... | nothing = IH
  ... | just y  = ↭-prep y IH
  mapMaybe-↭ {xs = .(x ∷ y ∷ _)} {ys = .(y ∷ x ∷ _)} (↭-swap x y xs↭ys)
    with IH ← mapMaybe-↭ xs↭ys
    with f x | inspect f x | f y | inspect f y
  ... | nothing | ≡[ fx ] | nothing | ≡[ fy ] rewrite fx | fy = IH
  ... | nothing | ≡[ fx ] | just y′ | ≡[ fy ] rewrite fx | fy = ↭-prep y′ IH
  ... | just x′ | ≡[ fx ] | nothing | ≡[ fy ] rewrite fx | fy = ↭-prep x′ IH
  ... | just x′ | ≡[ fx ] | just y′ | ≡[ fy ] rewrite fx | fy = ↭-swap x′ y′ IH
  mapMaybe-↭ {xs = xs} {ys = ys} (↭-trans xs↭ ↭ys) = ↭-trans (mapMaybe-↭ xs↭) (mapMaybe-↭ ↭ys)

  ∈-mapMaybe-skip : f x ≡ nothing → y ∈ mapMaybe f (x ∷ xs) → y ∈ mapMaybe f xs
  ∈-mapMaybe-skip fx≡ = subst (_ ∈_) (mapMaybe-skip fx≡)

  ∈-mapMaybe-here : ∀ {y′} → f x ≡ just y′ → y ∈ mapMaybe f (x ∷ xs) → y ∈ y′ ∷ mapMaybe f xs
  ∈-mapMaybe-here fx≡ = subst (_ ∈_) (mapMaybe-here fx≡)

  ∈-mapMaybe-++⁻ : ∀ xs {ys} {x : B}
    → x ∈ mapMaybe f (xs ++ ys)
    → x ∈ mapMaybe f xs
    ⊎ x ∈ mapMaybe f ys
  ∈-mapMaybe-++⁻ xs {ys} rewrite mapMaybe-++ xs ys = ∈-++⁻ _

  ∈-mapMaybe-++⁺ˡ : ∀ {xs ys} {x : B}
    → x ∈ mapMaybe f xs
    → x ∈ mapMaybe f (xs ++ ys)
  ∈-mapMaybe-++⁺ˡ {xs}{ys} rewrite mapMaybe-++ xs ys = ∈-++⁺ˡ

  ∈-mapMaybe-++⁺ʳ : ∀ xs {ys} {y : B}
    → y ∈ mapMaybe f ys
    → y ∈ mapMaybe f (xs ++ ys)
  ∈-mapMaybe-++⁺ʳ xs {ys} rewrite mapMaybe-++ xs ys = ∈-++⁺ʳ _

  -- ** Last∈

  Last∈-mapMaybe⁺ :
    ∀ (x∈ : x ∈ xs)
    → (f≡ : f x ≡ just y)
    → Last∈ x∈
    → Last∈ $ ∈-mapMaybe⁺ x∈ f≡
  Last∈-mapMaybe⁺ {x = x} {xs = .x ∷ []} {y = y} (here refl) f≡ tt
    with f x | ∈-mapMaybe⁺ {x = x} {xs = [ x ]} (here refl) f≡
  ... | nothing | ()
  ... | just _  | here refl = tt
  Last∈-mapMaybe⁺ {x = x} {xs = .(_ ∷ _)} {y = y} (there {x = z} x∈) f≡ last-x∈
    with f z
  ... | nothing = Last∈-mapMaybe⁺ x∈ f≡ $ Last∈-there⁻ x∈ last-x∈
  ... | just fz = Last∈-there⁺ (∈-mapMaybe⁺ x∈ f≡) (Last∈-mapMaybe⁺ x∈ f≡ $ Last∈-there⁻ x∈ last-x∈)

  -- ** mapMaybe˘
  mapMaybe˘ : List A → List A
  mapMaybe˘ = filter (T? ∘ M.is-nothing ∘ f)

  length˘f : List A → ℕ
  length˘f zs = length zs ∸ length (mapMaybe f zs)

  length∈˘f : ∀ {x : A} → (x ∈ xs) → ℕ
  length∈˘f {xs = xs} x∈ =
    let xsˡ⁺ , _ , _ = splitAt⁺ʳ xs (L.Any.index x∈)
        xsˡ = L.NE.toList xsˡ⁺
    in  length˘f xsˡ

  length-mapMaybe : length (mapMaybe f xs) ≡ length xs ∸ length (mapMaybe˘ xs)
  length-mapMaybe {[]} = refl
  length-mapMaybe {x ∷ xs} with f x
  ... | nothing = length-mapMaybe {xs = xs}
  ... | just _  rewrite length-mapMaybe {xs = xs}
    = ∸-suc (length xs) (length (mapMaybe˘ xs)) (length-count (T? ∘ M.is-nothing ∘ f) {xs = xs})

  -- ** indexℕ
  indexℕ-mapMaybe⁻ : ∀ {y : B}
    (y∈ : y ∈ mapMaybe f (x ∷ xs))
    → let _ , x∈ , _ = ∈-mapMaybe⁻ {xs = x ∷ xs} y∈
      in indexℕ x∈ ≡ ⊥⋯ x∈ + indexℕ y∈
  indexℕ-mapMaybe⁻ {x = x} {xs = []} {y = y} y∈
    with f x | inspect f x | y∈
  ... | nothing | _ | ()
  ... | just _ | _ | here refl = refl
  indexℕ-mapMaybe⁻ {x = x} {xs = xs@(x′ ∷ xs′)} {y = y} y∈
    with f x | inspect f x
  ... | nothing | _ =
    let _ , x∈ , _ = ∈-mapMaybe⁻ y∈
    in cong suc
    $ begin
      indexℕ x∈
    ≡⟨ indexℕ-mapMaybe⁻ y∈ ⟩
      ⊥⋯ x∈ + indexℕ y∈
    ∎ where open ≡-Reasoning
  ... | just _  | _
    with y∈
  ... | here refl = refl
  ... | there y∈′ =
    let _ , x∈ , _ = ∈-mapMaybe⁻ y∈′
    in begin
      suc (indexℕ x∈)
    ≡⟨ cong suc $ indexℕ-mapMaybe⁻ y∈′ ⟩
      suc (⊥⋯ x∈ + indexℕ y∈′)
    ≡⟨ sym $ Nat.+-suc (⊥⋯ x∈) (indexℕ y∈′) ⟩
      ⊥⋯ x∈ + suc (indexℕ y∈′)
    ∎ where open ≡-Reasoning

  indexℕ-mapMaybe≡0 : ∀ {y : B} (fx≡ : f x ≡ just y)
    → indexℕ (∈-mapMaybe⁺ (here {x = x} {xs = xs} refl) fx≡) ≡ 0
  indexℕ-mapMaybe≡0 {x = x} {xs = xs} {y = y} eq with just _ ← f x = refl

  ⊥⋯≤indexℕ : (x∈ : x ∈ xs) → ⊥⋯ x∈ ≤ suc (indexℕ x∈)
  ⊥⋯≤indexℕ {xs = x ∷ _} (here refl)
    with f x
  ... | nothing = Nat.≤-refl
  ... | just _  = z≤n
  ⊥⋯≤indexℕ {xs = x ∷ xs} (there x∈)
    with IH ← ⊥⋯≤indexℕ {xs = xs} x∈
    with f x
  ... | nothing = s≤s IH
  ... | just _ = Nat.≤-step IH

  ⊥⋯just≤indexℕ : ∀ {y : B} (x∈ : x ∈ xs) →
    f x ≡ just y
    ────────────────
    ⊥⋯ x∈ ≤ indexℕ x∈
  ⊥⋯just≤indexℕ {xs = x ∷ xs} (here refl) f≡
    with just _ ← f x = z≤n
  ⊥⋯just≤indexℕ {xs = x ∷ xs} (there x∈) f≡
    with IH ← ⊥⋯just≤indexℕ {xs = xs} x∈ f≡
    with f x
  ... | nothing = s≤s IH
  ... | just _  = Nat.≤-step IH

  indexℕ-mapMaybe⁺ : ∀ {y : B} (x∈ : x ∈ xs) (fx≡ : f x ≡ just y)
    → indexℕ (∈-mapMaybe⁺ x∈ fx≡) ≡ indexℕ x∈ ∸ ⊥⋯ x∈
  indexℕ-mapMaybe⁺ {xs = x ∷ xs} {y = y} (here refl) eq
    with just _ ← f x
    = refl
  indexℕ-mapMaybe⁺ {xs = x ∷ xs} (there x∈) eq
    with f x | indexℕ-mapMaybe⁺ {xs = xs} x∈ eq
  ... | nothing | IH = IH
  ... | just _  | IH rewrite IH
    = ∸-suc (indexℕ x∈) (⊥⋯ x∈) (⊥⋯just≤indexℕ x∈ eq)

postulate
  mapMaybe≡[]⇒All-nothing : ∀ {xs : List A} {f : A → Maybe B}
    → Null (mapMaybe f xs)
    → All (Is-nothing ∘ f) xs

  All-nothing⇒mapMaybe≡[] : ∀ {xs : List A} {f : A → Maybe B}
    → All Is-nothing (map f xs)
    → Null (mapMaybe f xs)
