{-# OPTIONS --safe --with-K #-}
module Prelude.Lists.WithK where

open import Prelude.Init; open SetAsType
open Nat
open L.Mem
open import Prelude.InferenceRules
open import Prelude.General
open import Prelude.Maybes
open import Prelude.Nats
open import Prelude.ToN
open import Prelude.Split

private variable
  A B : Type ℓ; P : A → Type ℓ
  x y : A; xs ys : List A

--

open import Prelude.Lists.Indexed

indexℕ-injective : ∀ (p q : x ∈ xs) →
  indexℕ p ≡ indexℕ q
  ───────────────────
  p ≡ q
indexℕ-injective {xs = .(_ ∷ _)} (here refl) (here refl) i≡ = refl
indexℕ-injective {xs = .(_ ∷ _)} (there p) (there q) i≡
  = cong there $ indexℕ-injective p q $ Nat.suc-injective {indexℕ p} {indexℕ q} i≡


⁉→‼ : ∀ {xs ys : List A} {ix : Index xs}
    → (len≡ : length xs ≡ length ys)
    → (xs ⁉ toℕ ix) ≡ (ys ⁉ toℕ ix)
    → (xs ‼ ix) ≡ (ys ‼ F.cast len≡ ix)
⁉→‼ {xs = []}     {[]}      {ix}      len≡ eq   = refl
⁉→‼ {xs = []}     {x ∷ ys}  {ix}      () eq
⁉→‼ {xs = x ∷ xs} {[]}      {ix}      () eq
⁉→‼ {xs = x ∷ xs} {.x ∷ ys} {fzero}   len≡ refl = refl
⁉→‼ {xs = x ∷ xs} {y ∷ ys}  {fsuc ix} len≡ eq
  rewrite ‼-suc {x = x} {xs} {ix}
        = ⁉→‼ {xs = xs} {ys} {ix} (Nat.suc-injective len≡) eq

indexℕ-++⁻ : ∀ (y∈ : y ∈ ys) (y∈′ : y ∈ xs ++ ys) →
  indexℕ y∈′ ≡ length xs + indexℕ y∈
  ──────────────────────────────────
  ∈-++⁻ xs {ys} y∈′ ≡ inj₂ y∈
indexℕ-++⁻ {xs = []}     y∈ y∈′         i≡ = cong inj₂ $ indexℕ-injective y∈′ y∈ i≡
indexℕ-++⁻ {xs = x ∷ xs} y∈ (there y∈′) i≡ = qed
  where
    IH : ∈-++⁻ xs y∈′ ≡ inj₂ y∈
    IH = indexℕ-++⁻ {xs = xs} y∈ y∈′ (Nat.suc-injective i≡)

    qed : ∈-++⁻ (x ∷ xs) (there y∈′) ≡ inj₂ y∈
    qed rewrite IH = refl

--

open import Prelude.Lists.Membership

module _ (P? : Decidable¹ P) where
  ∈-filter⁻-injective : ∀ {xs} (x∈ x∈′ : x ∈ filter P? xs)
    → ∈-filter⁻ P? {xs = xs} x∈ ≡ ∈-filter⁻ P? {xs = xs} x∈′
    → x∈ ≡ x∈′
  ∈-filter⁻-injective {xs = x ∷ xs} x∈ x∈′ eq
    with P? x | x∈ | x∈′ | eq
  ... | no  _ | x∈ | x∈′ | eq
    = ∈-filter⁻-injective x∈ x∈′
    $ map×-injective L.Any.there-injective id eq
  ... | yes _ | here px | here .px | refl = refl
  ... | yes _ | there x∈ | there x∈′ | eq
      = cong there
      $ ∈-filter⁻-injective x∈ x∈′
      $ map×-injective L.Any.there-injective id eq

  ∈-filter⁻∙proj₁-injective : ∀ {xs} (x∈ x∈′ : x ∈ filter P? xs)
    → ∈-filter⁻ P? {xs = xs} x∈ .proj₁ ≡ ∈-filter⁻ P? {xs = xs} x∈′ .proj₁
    → x∈ ≡ x∈′
  ∈-filter⁻∙proj₁-injective {xs = x ∷ xs} x∈ x∈′ eq
    with P? x | x∈ | x∈′ | eq
  ... | no  _ | x∈ | x∈′ | eq
    = ∈-filter⁻∙proj₁-injective x∈ x∈′
    $ L.Any.there-injective eq
  ... | yes _ | here px | here .px | refl = refl
  ... | yes _ | there x∈ | there x∈′ | eq
    = cong there
    $ ∈-filter⁻∙proj₁-injective x∈ x∈′
    $ L.Any.there-injective eq

∈-irr : Unique xs → Irrelevant (x ∈ xs)
∈-irr (x∉ ∷ _)  (here refl) (here refl) = refl
∈-irr (x∉ ∷ _)  (here refl) (there x∈)  = ⊥-elim $ L.All.lookup x∉ x∈ refl
∈-irr (x∉ ∷ _)  (there x∈)  (here refl) = ⊥-elim $ L.All.lookup x∉ x∈ refl
∈-irr (_  ∷ un) (there p)   (there q)   = cong there $ ∈-irr un p q

--

open import Prelude.Lists.Mappings

Unique⇒weaken≗ : ∀ (f : xs ↦′ P) (p p′ : ys ⊆ xs)
  → Unique xs
  → weaken-↦ f p ≗↦ weaken-↦ f p′
Unique⇒weaken≗ f p p′ uniq x∈ =
  cong f $ ∈-irr uniq (p x∈) (p′ x∈)

--

open import Prelude.Lists.MapMaybe
open import Prelude.Lists.Count

module _ (f : A → Maybe B) where
  open MapMaybeDSL f
  module _ {P : Pred B ℓ} where
    indexℕ-Any-catMaybes⁺ : ∀ {xs : List (Maybe B)} (p : Any (M.Any.Any P) xs)
      → indexℕ (Any-catMaybes⁺ p) ≡ indexℕ p ∸ count is-nothing? (p ∙left)
    indexℕ-Any-catMaybes⁺ {xs = nothing ∷ xs} (there p) = indexℕ-Any-catMaybes⁺ {xs = xs} p
    indexℕ-Any-catMaybes⁺ {xs = just x ∷ _}   (here (M.Any.just _)) = refl
    indexℕ-Any-catMaybes⁺ {xs = just x ∷ xs}  (there p) =
      begin
        indexℕ (there {x = x} (Any-catMaybes⁺ p))
      ≡⟨⟩
        suc (indexℕ $ Any-catMaybes⁺ p)
      ≡⟨ cong suc $ indexℕ-Any-catMaybes⁺ p ⟩
        suc (indexℕ p ∸ ⊥⋯p)
      ≡⟨ ∸-suc (indexℕ p) ⊥⋯p (⊥≤ p) ⟩
        suc (indexℕ p) ∸ ⊥⋯p
      ≡⟨ cong (suc (indexℕ p) ∸_) $ sym $ c≡ (p ∙left) ⟩
        suc (indexℕ p) ∸ count is-nothing? ((there {x = just x} p) ∙left)
      ≡⟨⟩
        indexℕ (there {x = just x} p) ∸ (MapMaybeDSL.⊥⋯ id) (there {x = just x} p)
      ∎ where
        open ≡-Reasoning
        ⊥⋯p = count is-nothing? (p ∙left)

        c≡ : ∀ xs → count is-nothing? (just x ∷ xs) ≡ count is-nothing? xs
        c≡ xs = cong length $ L.filter-reject is-nothing? {x = just x} {xs = xs} (λ ())

        ⊥≤ : ∀ {xs} (p : Any (M.Any.Any P) xs) → count is-nothing? (p ∙left) ≤ indexℕ p
        ⊥≤ (here (M.Any.just _)) = z≤n
        ⊥≤ {xs = xs} (there {x = just x} p)
          rewrite L.filter-reject is-nothing? {x = just x} {xs = xs} (λ ())
          = Nat.≤-step (⊥≤ p)
        ⊥≤ {xs = xs} (there {x = nothing} p)
          rewrite L.filter-accept is-nothing? {x = nothing} {xs = xs} tt
          = s≤s (⊥≤ p)

    indexℕ-Any-mapMaybe′⁺ : ∀ (x∈ : Any (M.Any.Any P ∘ f) xs)
      → indexℕ (Any-mapMaybe′⁺ f x∈) ≡ indexℕ x∈ ∸ ⊥⋯ x∈
    indexℕ-Any-mapMaybe′⁺ {xs = xs} p =
      begin
        indexℕ (Any-mapMaybe′⁺ f p)
      ≡⟨⟩
        indexℕ (Any-catMaybes⁺ $ L.Any.map⁺ p)
      ≡⟨ indexℕ-Any-catMaybes⁺ (L.Any.map⁺ p) ⟩
        indexℕ (L.Any.map⁺ p) ∸ count is-nothing? ((L.Any.map⁺ p) ∙left)
      ≡⟨ cong (_∸ count is-nothing? ((L.Any.map⁺ p) ∙left)) $ indexℕ-Any-map⁺ p ⟩
        indexℕ p ∸ count is-nothing? ((L.Any.map⁺ p) ∙left)
      ≡⟨ cong (indexℕ p ∸_) $ c≡ p ⟩
        indexℕ p ∸ ⊥⋯ p
      ∎ where
        open ≡-Reasoning
        c≡ : ∀ {xs : List A} (p : Any (M.Any.Any P ∘ f) xs)
          → count is-nothing? ((L.Any.map⁺ {P = M.Any.Any P} p) ∙left)
          ≡ ⊥⋯ p
        c≡ {xs = x ∷ xs} (here px) with just _ ← f x = refl
        c≡ {xs = x ∷ xs} (there p)
          with IH ← c≡ p
          with f x
        ... | nothing = cong suc IH
        ... | just _  = IH

    indexℕ-Any-mapMaybe⁺ : ∀ (x∈ : Any (M.Any.Any P ∘ f) xs)
      → indexℕ (Any-mapMaybe⁺ f x∈) ≡ indexℕ x∈ ∸ ⊥⋯ x∈
    indexℕ-Any-mapMaybe⁺ {xs = xs} p =
      begin
        indexℕ (Any-mapMaybe⁺ f p)
      ≡⟨ indexℕ∘Any⇒ f {xs = xs} _ ⟩
        indexℕ (Any-mapMaybe′⁺ f p)
      ≡⟨ indexℕ-Any-mapMaybe′⁺ p ⟩
        indexℕ p ∸ ⊥⋯ p
      ∎ where open ≡-Reasoning

  indexℕ-mapMaybe⁺ : ∀ {y : B} (x∈ : x ∈ xs) (fx≡ : f x ≡ just y)
    → indexℕ (∈-mapMaybe⁺ f x∈ fx≡) ≡ indexℕ x∈ ∸ ⊥⋯ x∈
  indexℕ-mapMaybe⁺ {xs = xs} {y = y} x∈ eq =
    begin
      indexℕ (∈-mapMaybe⁺ f x∈ eq)
    ≡⟨⟩
      indexℕ (Any-mapMaybe⁺ f $ L.Any.map (≡just⇒MAny f eq) x∈)
    ≡⟨ indexℕ-Any-mapMaybe⁺ $ L.Any.map (≡just⇒MAny f eq) x∈ ⟩
      indexℕ (L.Any.map (≡just⇒MAny f eq) x∈) ∸ ⊥⋯ (L.Any.map (≡just⇒MAny f eq) x∈)
    ≡⟨ cong (_∸ ⊥⋯ (L.Any.map (≡just⇒MAny f eq) x∈)) $ indexℕ-Any-map x∈ ⟩
      indexℕ x∈ ∸ ⊥⋯ (L.Any.map (≡just⇒MAny f eq) x∈)
    ≡⟨ cong (indexℕ x∈ ∸_) $ ⊥-map eq x∈ ⟩
      indexℕ x∈ ∸ ⊥⋯ x∈
    ∎ where
      open ≡-Reasoning
      ⊥-map : ∀ {x} {xs} (eq : f x ≡ just y) (x∈ : x ∈ xs) →
        ⊥⋯ (L.Any.map (≡just⇒MAny f eq) x∈) ≡ ⊥⋯ x∈
      ⊥-map {xs = _ ∷ _}  _  (here _)   = refl
      ⊥-map {xs = x ∷ xs} eq (there x∈) with f x
      ... | nothing = cong suc (⊥-map eq x∈)
      ... | just _  = ⊥-map eq x∈
