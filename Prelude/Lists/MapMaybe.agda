{-# OPTIONS --safe #-}
module Prelude.Lists.MapMaybe where

open import Prelude.Init; open SetAsType
open Nat.Ord
open L.Mem
open import Prelude.General
open import Prelude.Maybes
open import Prelude.Nats
open import Prelude.InferenceRules
open import Prelude.Bifunctor
open import Prelude.Split
open import Prelude.Null

open import Prelude.Lists.Empty
open import Prelude.Lists.Indexed
open import Prelude.Lists.Count
open import Prelude.Lists.Membership

private variable
  a b : Level; A : Type a; B : Type b
  x x′ y : A; xs ys : List A

-- ** mapMaybe
mapMaybeIsInj₁∘mapInj₁ : (xs : List A) → mapMaybe (isInj₁ {B = B}) (map inj₁ xs) ≡ xs
mapMaybeIsInj₁∘mapInj₁ = λ where
  [] → refl
  (x ∷ xs) → cong (x ∷_) (mapMaybeIsInj₁∘mapInj₁ xs)

mapMaybeIsInj₁∘mapInj₂ : (xs : List B) → mapMaybe (isInj₁ {A = A}) (map inj₂ xs) ≡ []
mapMaybeIsInj₁∘mapInj₂ = λ where
  [] → refl
  (x ∷ xs) → mapMaybeIsInj₁∘mapInj₂ xs

mapMaybeIsInj₂∘mapInj₂ : (xs : List B) → mapMaybe (isInj₂ {A = A}) (map inj₂ xs) ≡ xs
mapMaybeIsInj₂∘mapInj₂ = λ where
  [] → refl
  (x ∷ xs) → cong (x ∷_) (mapMaybeIsInj₂∘mapInj₂ xs)

mapMaybeIsInj₂∘mapInj₁ : (xs : List A) → mapMaybe (isInj₂ {B = B}) (map inj₁ xs) ≡ []
mapMaybeIsInj₂∘mapInj₁ = λ where
  [] → refl
  (x ∷ xs) → mapMaybeIsInj₂∘mapInj₁ xs

-- ** catMaybes
catMaybes : List (Maybe A) → List A
catMaybes [] = []
catMaybes (nothing ∷ xs) = catMaybes xs
catMaybes (just x ∷ xs)  = x ∷ catMaybes xs

Any-catMaybes⁺ : ∀ {P : Pred A ℓ} {xs : List (Maybe A)}
  → Any (M.Any.Any P) xs → Any P (catMaybes xs)
Any-catMaybes⁺ {xs = nothing ∷ xs} (there x∈) = Any-catMaybes⁺ x∈
Any-catMaybes⁺ {xs = just x ∷ xs} = λ where
  (here (M.Any.just px)) → here px
  (there x∈)             → there $ Any-catMaybes⁺ x∈

catMaybes-↭ : xs ↭ ys → catMaybes xs ↭ catMaybes ys
catMaybes-↭ ↭-refl = ↭-refl
catMaybes-↭ (↭-trans xs↭ ↭ys) = ↭-trans (catMaybes-↭ xs↭) (catMaybes-↭ ↭ys)
catMaybes-↭ {xs = .(mx ∷ _)} {.(mx ∷ _)} (↭-prep mx xs↭)
  with mx
... | nothing = catMaybes-↭ xs↭
... | just x  = ↭-prep x $ catMaybes-↭ xs↭
catMaybes-↭ {xs = .(mx ∷ my ∷ _)} {.(my ∷ mx ∷ _)} (↭-swap mx my xs↭)
  with mx | my
... | nothing | nothing = catMaybes-↭ xs↭
... | nothing | just y  = ↭-prep y $ catMaybes-↭ xs↭
... | just x  | nothing = ↭-prep x $ catMaybes-↭ xs↭
... | just x  | just y  = ↭-swap x y $ catMaybes-↭ xs↭

-- mapMaybe′: a simpler definition than the one found in stdlib
-- NB: does not use a `with` statement and is therefore much easier to reason about
mapMaybe′ : (A → Maybe B) → List A → List B
mapMaybe′ f = catMaybes ∘ map f

module _ (f : A → Maybe B) where
  mapMaybe≗mapMaybe′ :
    mapMaybe′ f ≗ mapMaybe f
  mapMaybe≗mapMaybe′ [] = refl
  mapMaybe≗mapMaybe′ (x ∷ xs) with f x
  ... | nothing = mapMaybe≗mapMaybe′ xs
  ... | just _  = cong (_ ∷_) (mapMaybe≗mapMaybe′ xs)

  mapMaybe′-↭ : xs ↭ ys → mapMaybe′ f xs ↭ mapMaybe′ f ys
  mapMaybe′-↭ = catMaybes-↭ ∘ L.Perm.map⁺ f

  mapMaybe-↭ : xs ↭ ys → mapMaybe f xs ↭ mapMaybe f ys
  mapMaybe-↭ {xs}{ys} xs↭ =
    subst (_↭ _) (mapMaybe≗mapMaybe′ xs) $
    subst (_ ↭_) (mapMaybe≗mapMaybe′ ys) $
    mapMaybe′-↭ xs↭

module MapMaybeDSL (f : A → Maybe B) where

  module _ {P : Pred A ℓ′} where
    ⊥⋯_ _⋯⊥ ⊤⋯_ _⋯⊤ : Any P xs → ℕ
    ⊥⋯ x∈ = countNothing f (x∈ ∙left)
    ⊤⋯ x∈ = countJust    f (x∈ ∙left)
    x∈ ⋯⊥ = countNothing f (x∈ ∙right)
    x∈ ⋯⊤ = countJust    f (x∈ ∙right)

    countNothing≤ : (x∈ : Any P xs) → ⊥⋯ x∈ ≤ suc (indexℕ x∈)
    countNothing≤ {xs = xs} x∈ =
      begin ⊥⋯ x∈                     ≡⟨⟩
            countNothing f (x∈ ∙left) ≤⟨ length-count (is-nothing? ∘ f) {xs = x∈ ∙left} ⟩
            length (x∈ ∙left)         ≡⟨ length-∈∙left x∈ ⟩
            suc (indexℕ x∈)           ∎ where open ≤-Reasoning

  countNothing≡⊥⋯⊥ : (x∈ : x ∈ xs) → countNothing f xs ≡ ⊥⋯ x∈ + x∈ ⋯⊥
  countNothing≡⊥⋯⊥ {xs = x ∷ xs} (here refl)
    with f x
  ... | nothing = refl
  ... | just _  = refl
  countNothing≡⊥⋯⊥ {xs = x ∷ xs} (there x∈)
    with f x
  ... | nothing = cong suc (countNothing≡⊥⋯⊥ x∈)
  ... | just _  = countNothing≡⊥⋯⊥ x∈

module _ (f : A → Maybe B) where
  open MapMaybeDSL f

  mapMaybe-++ : ∀ xs ys → mapMaybe f (xs ++ ys) ≡ mapMaybe f xs ++ mapMaybe f ys
  mapMaybe-++ []       ys = refl
  mapMaybe-++ (x ∷ xs) ys with f x
  ... | just _  = cong (_ ∷_) (mapMaybe-++ xs ys)
  ... | nothing = mapMaybe-++ xs ys

  mapMaybe-skip : f x ≡ nothing → mapMaybe f (x ∷ xs) ≡ mapMaybe f xs
  mapMaybe-skip {x = x} _ with nothing ← f x = refl

  mapMaybe-here : (eq : f x ≡ just y)
    → mapMaybe f (x ∷ xs) ≡ y ∷ mapMaybe f xs
  mapMaybe-here {x = x} eq with just _ ← f x = cong (_∷ _) (M.just-injective eq)

  All-nothing⇒mapMaybe≡[] : ∀ {xs} → All Is-nothing (map f xs) → Null (mapMaybe f xs)
  All-nothing⇒mapMaybe≡[] {xs = []}     [] = refl
  All-nothing⇒mapMaybe≡[] {xs = x ∷ xs} (px ∷ pxs) with f x | px
  ... | just _  | M.All.just ()
  ... | nothing | _ = All-nothing⇒mapMaybe≡[] {xs = xs} pxs

  mapMaybe≡[]⇒All-nothing : ∀ {xs} → Null (mapMaybe f xs) → All (Is-nothing ∘ f) xs
  mapMaybe≡[]⇒All-nothing {xs = []}     p = []
  mapMaybe≡[]⇒All-nothing {xs = x ∷ xs} p
    with nothing ← f x in fx≡
    = subst (M.All.All _) (sym fx≡) M.All.nothing
    ∷ mapMaybe≡[]⇒All-nothing {xs = xs} p

  -- ** mapMaybe⁻

  module _ {P : Pred B ℓ} where
    Any-mapMaybe′⁺ : Any (M.Any.Any P ∘ f) xs → Any P (mapMaybe′ f xs)
    Any-mapMaybe′⁺ = Any-catMaybes⁺ ∘ L.Any.map⁺

    -- private
    Any[_]⇒_ : ∀ xs → Any P (mapMaybe′ f xs) → Any P (mapMaybe f xs)
    Any[ xs ]⇒ x∈ = subst (Any P) (mapMaybe≗mapMaybe′ f xs) x∈

    Any-mapMaybe⁺ : Any (M.Any.Any P ∘ f) xs → Any P (mapMaybe f xs)
    Any-mapMaybe⁺ {xs = xs} x∈ = Any[ xs ]⇒ Any-mapMaybe′⁺ x∈

    --

    Any-mapMaybe′⁺-here : (Px : M.Any.Any P (f x))
      → Is-here $ Any-mapMaybe′⁺ (here {xs = xs} Px)
    Any-mapMaybe′⁺-here {x = x} Px
      with f x      | Px
    ... | .(just _) | M.Any.just _ = tt

    Is-here∘Any⇒ : ∀ xs →
      (p : Any P (mapMaybe′ f xs)) →
      Is-here p →
      Is-here (Any[ xs ]⇒ p)
    Is-here∘Any⇒ (x ∷ xs) p hp with f x
    ... | nothing = Is-here∘Any⇒ xs p hp
    ... | just _ rewrite mapMaybe≗mapMaybe′ f xs = hp

    Any-mapMaybe⁺-here : (Px : M.Any.Any P (f x))
      → Is-here $ Any-mapMaybe⁺ (here {xs = xs} Px)
    Any-mapMaybe⁺-here {x = x} {xs = xs} Px =
      Is-here∘Any⇒ _ (Any-mapMaybe′⁺ (here Px)) (Any-mapMaybe′⁺-here Px)

    --

    Is-here⇒indexℕ≡0 : (p : Any P xs) →
      Is-here p
      ────────────
      indexℕ p ≡ 0
    Is-here⇒indexℕ≡0 (here _) _ = refl

    indexℕ-Any-mapMaybe≡0 : ∀ {y : B} (Px : M.Any.Any P (f x))
      → indexℕ (Any-mapMaybe⁺ (here {x = x} {xs = xs} Px)) ≡ 0
    indexℕ-Any-mapMaybe≡0 {x = x} {xs = xs} Px = Is-here⇒indexℕ≡0 _ (Any-mapMaybe⁺-here Px)

    --

    indexℕ∘Any⇒ : (p : Any P (mapMaybe′ f xs)) →
       indexℕ (Any[ xs ]⇒ p) ≡ indexℕ p
    indexℕ∘Any⇒ {xs = xs} p rewrite mapMaybe≗mapMaybe′ f xs = refl

  ≡just⇒MAny :
      f x ≡ just y
    → (x ≡_) ⊆¹ M.Any.Any (_≡_ y) ∘ f
  ≡just⇒MAny eq refl = subst (M.Any.Any (_ ≡_)) (sym eq) (M.Any.just refl)

  ∈-mapMaybe⁺ : x ∈ xs → f x ≡ just y → y ∈ mapMaybe f xs
  ∈-mapMaybe⁺ {x = x} {xs = xs} {y = y} x∈ eq = Any-mapMaybe⁺ $ L.Any.map (≡just⇒MAny eq) x∈

  Is-here∘map : ∀ {X : Type ℓ} {P : Pred A ℓ′} {Q : Pred A ℓ″} (g : P ⊆¹ Q)
    → (p : Any P xs)
    → Is-here p
    → Is-here $ L.Any.map g p
  Is-here∘map _ (here _) _ = tt

  ∈-mapMaybe⁺-here : (eq : f x ≡ just y)
    → Is-here $ ∈-mapMaybe⁺ (here {xs = xs} refl) eq
  ∈-mapMaybe⁺-here {x = x} {y = y} {xs = xs} eq = Any-mapMaybe⁺-here (≡just⇒MAny eq refl)

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

  -- ** ∈-mapMaybe⁻

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
    with f x    | inspect f x
  ... | nothing | _ = case y∈≡ of λ ()
  ... | just _  | _ with here _ ← y∈ = tt

  mapMaybe-⊆ : xs ⊆ ys → mapMaybe f xs ⊆ mapMaybe f ys
  mapMaybe-⊆ {xs = x ∷ xs} {ys = ys} xs⊆ fx∈ =
    let x , x∈ , fx≡ = ∈-mapMaybe⁻ fx∈
    in  ∈-mapMaybe⁺ (xs⊆ x∈) fx≡

  -- ** LastAny

  module _ {P : Pred B ℓ} where
    LastAny-catMaybes⁺ : (p : Any (M.Any.Any P) xs) →
      LastAny p
      ──────────────────────────
      LastAny (Any-catMaybes⁺ p)
    LastAny-catMaybes⁺ {just x ∷ .[]} (here (M.Any.just _)) refl = refl
    LastAny-catMaybes⁺ {just x  ∷ _}  (there p) lp = LastAny-catMaybes⁺ p lp
    LastAny-catMaybes⁺ {nothing ∷ _}  (there p) lp = LastAny-catMaybes⁺ p lp

    LastAny-mapMaybe′⁺ :
      ∀ (x∈ : Any (M.Any.Any P ∘ f) xs)
      → LastAny x∈
      → LastAny $ Any-mapMaybe′⁺ x∈
    LastAny-mapMaybe′⁺ {xs = xs} p lp = LastAny-catMaybes⁺ (L.Any.map⁺ p) (LastAny-map⁺⁺ f (M.Any.Any P) p lp)

    Last∘Any⇒ : ∀ xs →
      (p : Any P (mapMaybe′ f xs)) →
      LastAny p →
      LastAny (Any[ xs ]⇒ p)
    Last∘Any⇒ (x ∷ xs) p hp with f x
    ... | nothing = Last∘Any⇒ xs p hp
    ... | just _  rewrite mapMaybe≗mapMaybe′ f xs = hp

    LastAny-mapMaybe⁺ :
      ∀ (x∈ : Any (M.Any.Any P ∘ f) xs)
      → LastAny x∈
      → LastAny $ Any-mapMaybe⁺ x∈
    LastAny-mapMaybe⁺ {xs = xs} = Last∘Any⇒ xs _ ∘₂ LastAny-mapMaybe′⁺

  -- ** Last∈

  Last∈-mapMaybe⁺ :
    ∀ (x∈ : x ∈ xs)
    → (f≡ : f x ≡ just y)
    → Last∈ x∈
    → Last∈ $ ∈-mapMaybe⁺ x∈ f≡
  Last∈-mapMaybe⁺ p eq = LastAny-mapMaybe⁺ (L.Any.map _ p) ∘ LastAny-map⁺ (≡just⇒MAny eq) p

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
  indexℕ-mapMaybe≡0 {y = y} eq = indexℕ-Any-mapMaybe≡0 {y = y} (≡just⇒MAny eq refl)
