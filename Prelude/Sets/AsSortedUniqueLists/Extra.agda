{-# OPTIONS --with-K #-}
module Prelude.Sets.AsSortedUniqueLists.Extra where

open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.InferenceRules
open import Prelude.Ord
open import Prelude.Ord.Product
open import Prelude.ToList; open import Prelude.FromList
open import Prelude.DecEq
open import Prelude.Setoid
open import Prelude.Null
open import Prelude.Membership
open import Prelude.Bifunctor

open import Prelude.Lists.Core
open import Prelude.Lists.Dec
open import Prelude.Lists.MapMaybe
open import Prelude.Lists.SetEquality
open import Prelude.Lists.Concat

open import Prelude.Sets.AsSortedUniqueLists.Core

open ≈-Reasoning

to = toList; from = fromList

module _ {A : Type ℓ} ⦃ _ : DecEq A ⦄ ⦃ _ : Ord⁺⁺ A ⦄ where
  Nullˢ  = Null {A = Set⟨ A ⟩}
  Null?ˢ = Null? {A = Set⟨ A ⟩}
  Nullᵇˢ = Nullᵇ {A = Set⟨ A ⟩}

  private variable x : A; xs ys zs : Set⟨ A ⟩

  toList∘singleton : toList (singleton x) ≡ [ x ]
  toList∘singleton = refl

  fromList∘singleton : fromList [ x ] ≡ singleton x
  fromList∘singleton = refl

  ∈ˢ-toList⁻ : x ∈ˢ xs → x ∈ toList xs
  ∈ˢ-toList⁻ = id
  ∈ˢ-toList⁺ : x ∈ toList xs → x ∈ˢ xs
  ∈ˢ-toList⁺ = id

  postulate
    ∪-congˡ : ys ≈ zs → xs ∪ ys ≈ xs ∪ zs
    ∪-congʳ : xs ≈ ys → xs ∪ zs ≈ ys ∪ zs

module _ {A : Type ℓ} ⦃ _ : DecEq A ⦄ ⦃ _ : Ord⁺⁺ A ⦄ where
  private variable
    x x′ : A; xs xs′ ys zs : Set⟨ A ⟩

  ∈ˢ-singleton : x ∈ˢ singleton x
  ∈ˢ-singleton = singleton∈ˢ .proj₂ refl

  infixr 5 _∷ˢ_
  _∷ˢ_ : A → Set⟨ A ⟩ → Set⟨ A ⟩
  x ∷ˢ xs = singleton x ∪ xs

  ∈ˢ-∷⁺ˡ hereˢ : x ∈ˢ x ∷ˢ xs
  ∈ˢ-∷⁺ˡ {xs = xs} = ∈-∪⁺ˡ _ (singleton _) xs ∈ˢ-singleton
  hereˢ  {xs = xs} = ∈ˢ-∷⁺ˡ {xs = xs}

  ∈ˢ-∷⁺ʳ thereˢ : x ∈ˢ xs → x ∈ˢ x′ ∷ˢ xs
  ∈ˢ-∷⁺ʳ {xs = xs} = ∈-∪⁺ʳ _ (singleton _) xs
  thereˢ {xs = xs} = ∈ˢ-∷⁺ʳ {xs = xs}

  ∈ˢ-∷⁻ : x ∈ˢ x′ ∷ˢ xs → (x ≡ x′) ⊎ (x ∈ˢ xs)
  ∈ˢ-∷⁻ {xs = xs} x∈ with ∈-∪⁻ _ (singleton _) xs x∈
  ... | inj₁ (here refl) = inj₁ refl
  ... | inj₂ x∈          = inj₂ x∈

  postulate
    from-∷ˢ : ∀ {xs} → from (x ∷ xs) ≈ (x ∷ˢ from xs)
    from-++ˢ : ∀ {xs ys : List A} → from (xs ++ ys) ≡ (from xs ∪ from ys)
    from-≈ : ∀ {xs ys : List A} →
      xs ∼[set] ys
      ──────────────────
      from xs ≈ from ys
    from-≈˘ : ∀ {xs ys : List A} →
      from xs ≈ from ys
      ──────────────────
      xs ∼[set] ys
    to-∷ˢ : (to $ x ∷ˢ xs) ∼[set] (x ∷ to xs)
    to-++ˢ : (to $ xs ∪ ys) ∼[set] (to xs ++ to ys)

    to-≈ :
      xs ≈ ys
      ──────────────────
      to xs ∼[set] to ys


  headˢ : Set' → Maybe A
  headˢ = L.head ∘ to

  private variable P : A → Type ℓ

  filterˢ : Decidable¹ P → Op₁ Set⟨ A ⟩
  filterˢ P? = from ∘ filter P? ∘ to

  module _ {B : Type ℓ} ⦃ _ : DecEq B ⦄ ⦃ _ : Ord⁺⁺ B ⦄ where

    mapˢ : (A → B) → (Set⟨ A ⟩ → Set⟨ B ⟩)
    mapˢ f = from ∘ map f ∘ to

    mapWith∈ˢ : (xs : Set⟨ A ⟩) → (∀ {x} → x ∈ˢ xs → B) → Set⟨ B ⟩
    mapWith∈ˢ xs f = from
                   $ L.Mem.mapWith∈ (to xs)
                   $ f ∘ ∈-nub⁻ ∘ ∈-sort⁻ ∘ ∈ˢ-fromList⁺

    module _ (f : A → B) where

      module _ {P : Pred B ℓ} {xs} where
        Anyˢ-map⁺ : Anyˢ (P ∘ f) xs → Anyˢ P (mapˢ f xs)
        Anyˢ-map⁺ = Anyˢ-fromList⁺ ∘ L.Any.map⁺

        Anyˢ-map⁻ :  Anyˢ P (mapˢ f xs) → Anyˢ (P ∘ f) xs
        Anyˢ-map⁻ = L.Any.map⁻ ∘ Anyˢ-fromList⁻

        Anyˢ-map : Anyˢ (P ∘ f) xs ↔ Anyˢ P (mapˢ f xs)
        Anyˢ-map = Anyˢ-map⁺ , Anyˢ-map⁻

      ∈ˢ-map⁺ : x ∈ˢ xs → f x ∈ˢ mapˢ f xs
      ∈ˢ-map⁺ = ∈ˢ-fromList⁺ ∘ L.Mem.∈-map⁺ f

      ∈ˢ-map⁻ : ∀ {y} → y ∈ˢ mapˢ f xs → ∃ λ x → x ∈ˢ xs × y ≡ f x
      ∈ˢ-map⁻ = L.Mem.∈-map⁻ f ∘ ∈ˢ-fromList⁻

      postulate mapˢ-∪ : mapˢ f (xs ∪ ys) ≈ (mapˢ f xs ∪ mapˢ f ys)

    mapMaybeˢ : (A → Maybe B) → (Set⟨ A ⟩ → Set⟨ B ⟩)
    mapMaybeˢ f = from ∘ mapMaybe f ∘ to

    module _ (f : A → Maybe B) where

      module _ {y} where
        ∈ˢ-mapMaybe⁺ : x ∈ˢ xs → f x ≡ just y → y ∈ˢ mapMaybeˢ f xs
        ∈ˢ-mapMaybe⁺ = ∈ˢ-fromList⁺ ∘₂ ∈-mapMaybe⁺ f

        ∈ˢ-mapMaybe⁻ : y ∈ˢ mapMaybeˢ f xs → ∃ λ x → (x ∈ˢ xs) × (f x ≡ just y)
        ∈ˢ-mapMaybe⁻ = ∈-mapMaybe⁻ f ∘ ∈ˢ-fromList⁻

      postulate
        mapMaybeˢ-∪ : mapMaybeˢ f (xs ∪ ys) ≈ (mapMaybeˢ f xs ∪ mapMaybeˢ f ys)

-- ** align/zip/partition
module _ {A B C : Type}
  ⦃ _ : DecEq A ⦄ ⦃ _ : DecEq B ⦄ ⦃ _ : DecEq C ⦄
  ⦃ _ : Ord⁺⁺ A ⦄ ⦃ _ : Ord⁺⁺ B ⦄ ⦃ _ : Ord⁺⁺ C ⦄
  where
  alignWithˢ : (These A B → C) → Set⟨ A ⟩ → Set⟨ B ⟩ → Set⟨ C ⟩
  alignWithˢ f xs ys = from $ L.alignWith f (to xs) (to ys)

  zipWithˢ : (A → B → C) → Set⟨ A ⟩ → Set⟨ B ⟩ → Set⟨ C ⟩
  zipWithˢ f xs ys = from $ L.zipWith f (to xs) (to ys)

  unalignWithˢ : (A → These B C) → Set⟨ A ⟩ → Set⟨ B ⟩ × Set⟨ C ⟩
  unalignWithˢ f = (λ (xs , ys) → from xs , from ys) ∘ L.unalignWith f ∘ to

  unzipWithˢ : (A → B × C) → Set⟨ A ⟩ → Set⟨ B ⟩ × Set⟨ C ⟩
  unzipWithˢ f = (λ (xs , ys) → from xs , from ys) ∘ L.unzipWith f ∘ to

  partitionSumsWithˢ : (A → B ⊎ C) → Set⟨ A ⟩ → Set⟨ B ⟩ × Set⟨ C ⟩
  partitionSumsWithˢ f = unalignWithˢ (∣These∣.fromSum ∘′ f)

module _ {A B : Type}
  ⦃ _ : DecEq A ⦄ ⦃ _ : DecEq B ⦄
  ⦃ _ : Ord⁺⁺ A ⦄ ⦃ _ : Ord⁺⁺ B ⦄
  where
  alignˢ : Set⟨ A ⟩ → Set⟨ B ⟩ → Set⟨ These A B ⟩
  alignˢ = alignWithˢ id

  zipˢ : Set⟨ A ⟩ → Set⟨ B ⟩ → Set⟨ A × B ⟩
  zipˢ = zipWithˢ (_,_)

  unalignˢ : Set⟨ These A B ⟩ → Set⟨ A ⟩ × Set⟨ B ⟩
  unalignˢ = unalignWithˢ id

  unzipˢ : Set⟨ A × B ⟩ → Set⟨ A ⟩ × Set⟨ B ⟩
  unzipˢ = unzipWithˢ id

  -- partitionSumsˢ : Set⟨ A ⊎ B ⟩ → Set⟨ A ⟩ × Set⟨ B ⟩
  -- partitionSumsˢ = partitionSumsWithˢ id

  partitionSumsˢ : Set⟨ A ⊎ B ⟩ → Set⟨ A ⟩ × Set⟨ B ⟩
  partitionSumsˢ = (λ (as , bs) → from as , from bs) ∘ partitionSums ∘ to

  leftsˢ : Set⟨ A ⊎ B ⟩ → Set⟨ A ⟩
  leftsˢ = proj₁ ∘ partitionSumsˢ

  rightsˢ : Set⟨ A ⊎ B ⟩ → Set⟨ B ⟩
  rightsˢ = proj₂ ∘ partitionSumsˢ

  leftsˢ∘inj₁ : ∀ {a : A} {abs : Set⟨ A ⊎ B ⟩}
    →  leftsˢ (inj₁ a ∷ˢ abs)
    ≈ (a ∷ˢ leftsˢ abs)
  leftsˢ∘inj₁ {a = a}{abs} =
    begin
      leftsˢ (inj₁ a ∷ˢ abs)
    ≡⟨⟩
      from (lefts $ to $ inj₁ a ∷ˢ abs)
    ≈⟨ from-≈ {xs = lefts $ to $ inj₁ a ∷ˢ abs}
              {ys = lefts $ inj₁ a ∷ to abs}
     $ lefts-seteq
     $ to-∷ˢ {x = inj₁ a} {xs = abs}
     ⟩
      from (lefts $ inj₁ a ∷ to abs)
    ≡⟨⟩
      from (a ∷ lefts (to abs))
    ≈⟨ from-∷ˢ {xs = lefts $ to abs} ⟩
      (a ∷ˢ from (lefts $ to abs))
    ≡⟨⟩
      (a ∷ˢ leftsˢ abs)
    ∎

  leftsˢ∘inj₂ : ∀ {b : B} {abs : Set⟨ A ⊎ B ⟩}
    →  leftsˢ (inj₂ b ∷ˢ abs)
    ≈ leftsˢ abs
  leftsˢ∘inj₂ {b = b}{abs} =
    begin
      leftsˢ (inj₂ b ∷ˢ abs)
    ≡⟨⟩
      from (lefts $ to $ inj₂ b ∷ˢ abs)
    ≈⟨ from-≈ {xs = lefts $ to $ inj₂ b ∷ˢ abs}
               {ys = lefts $ inj₂ b ∷ to abs}
     $ lefts-seteq
     $ to-∷ˢ {x = inj₂ b} {xs = abs}
     ⟩
      from (lefts $ inj₂ b ∷ to abs)
    ≡⟨⟩
      from (lefts $ to abs)
    ≡⟨⟩
      leftsˢ abs
    ∎

  rightsˢ∘inj₁ : ∀ {a : A} {abs : Set⟨ A ⊎ B ⟩}
    →  rightsˢ (inj₁ a ∷ˢ abs)
    ≈ rightsˢ abs
  rightsˢ∘inj₁ {a = a}{abs} =
    begin
      rightsˢ (inj₁ a ∷ˢ abs)
    ≡⟨⟩
      from (rights $ to $ inj₁ a ∷ˢ abs)
    ≈⟨ from-≈ {xs = rights $ to $ inj₁ a ∷ˢ abs}
               {ys = rights $ inj₁ a ∷ to abs}
     $ rights-seteq
     $ to-∷ˢ {x = inj₁ a} {xs = abs}
     ⟩
      from (rights $ inj₁ a ∷ to abs)
    ≡⟨⟩
      from (rights $ to abs)
    ≡⟨⟩
      rightsˢ abs
    ∎

  rightsˢ∘inj₂ : ∀ {b : B} {abs : Set⟨ A ⊎ B ⟩}
    →  rightsˢ (inj₂ b ∷ˢ abs)
    ≈ (b ∷ˢ rightsˢ abs)
  rightsˢ∘inj₂ {b = b}{abs} =
    begin
      rightsˢ (inj₂ b ∷ˢ abs)
    ≡⟨⟩
      from (rights $ to $ inj₂ b ∷ˢ abs)
    ≈⟨ from-≈ {xs = rights $ to $ inj₂ b ∷ˢ abs}
               {ys = rights $ inj₂ b ∷ to abs}
     $ rights-seteq
     $ to-∷ˢ {x = inj₂ b} {xs = abs}
     ⟩
      from (rights $ inj₂ b ∷ to abs)
    ≡⟨⟩
      from (b ∷ rights (to abs))
    ≈⟨ from-∷ˢ {xs = rights $ to abs} ⟩
      (b ∷ˢ from (rights $ to abs))
    ≡⟨⟩
      (b ∷ˢ rightsˢ abs)
    ∎

module _ {A B C : Type}
  ⦃ _ : DecEq A ⦄ ⦃ _ : DecEq B ⦄ ⦃ _ : DecEq C ⦄
  ⦃ _ : Ord⁺⁺ A ⦄ ⦃ _ : Ord⁺⁺ B ⦄ ⦃ _ : Ord⁺⁺ C ⦄
  where
  unzip₃ˢ : Set⟨ A × B × C ⟩ → Set⟨ A ⟩ × Set⟨ B ⟩ × Set⟨ C ⟩
  unzip₃ˢ = map₂ unzipˢ ∘ unzipˢ

module _ {A B : Type ℓ}
  ⦃ _ : DecEq A ⦄ ⦃ _ : Ord⁺⁺ A ⦄ ⦃ _ : DecEq B ⦄ ⦃ _ : Ord⁺⁺ B ⦄ where

  filterˢ₁ : Set⟨ A ⊎ B ⟩ → Set⟨ A ⟩
  filterˢ₁ = mapMaybeˢ isInj₁

  filterˢ₂ : Set⟨ A ⊎ B ⟩ → Set⟨ B ⟩
  filterˢ₂ = mapMaybeˢ isInj₂

-- ** sum
sumˢ : Set⟨ ℕ ⟩ → ℕ
sumˢ = sum ∘ to
