module Prelude.Sets.AsUniqueLists.Extra where

open import Prelude.Init; open SetAsType
open L.Mem using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Prelude.DecLists
open import Prelude.Membership
open import Prelude.DecEq
open import Prelude.ToList
open import Prelude.FromList
open import Prelude.InferenceRules
open import Prelude.Setoid
open import Prelude.Functor
open import Prelude.Foldable
open import Prelude.Traversable
open import Prelude.Monad
open import Prelude.Indexable
open import Prelude.Bifunctor

open import Prelude.Lists.Core
open import Prelude.Lists.MapMaybe
open import Prelude.Lists.SetEquality
open import Prelude.Lists.Concat

open import Data.List.Relation.Binary.Subset.Propositional.Properties using (Any-resp-⊆)
import Relation.Binary.Reasoning.Setoid as BinSetoid
open ≈-Reasoning

open import Prelude.Sets.AsUniqueLists.Core

private to = toList; from = fromList

module _ {A : Type} ⦃ _ : DecEq A ⦄ where
  private variable x : A; xs ys zs : Set⟨ A ⟩

  toList∘singleton : toList (singleton x) ≡ [ x ]
  toList∘singleton = refl

  fromList∘singleton : fromList [ x ] ≡ singleton x
  fromList∘singleton = refl

  ∈ˢ-toList⁻ : x ∈ˢ xs → x ∈ toList xs
  ∈ˢ-toList⁻ = id
  ∈ˢ-toList⁺ : x ∈ toList xs → x ∈ˢ xs
  ∈ˢ-toList⁺ = id

  ∪-congˡ : ys ≈ zs → xs ∪ ys ≈ xs ∪ zs
  ∪-congˡ {ys = ys}{zs}{xs} (ys⊆ , zs⊆) = xs∪ys⊆ , xs∪zs⊆
    where
      xs∪ys⊆ : xs ∪ ys ⊆ˢ xs ∪ zs
      xs∪ys⊆ = ∈-∪⁻ _ xs ys >≡> λ where
        (inj₁ ∈xs) → ∈-∪⁺ˡ _ xs zs ∈xs
        (inj₂ ∈ys) → ∈-∪⁺ʳ _ xs zs (ys⊆ ∈ys)

      xs∪zs⊆ : xs ∪ zs ⊆ˢ xs ∪ ys
      xs∪zs⊆ = ∈-∪⁻ _ xs zs >≡> λ where
        (inj₁ ∈xs) → ∈-∪⁺ˡ _ xs ys ∈xs
        (inj₂ ∈zs) → ∈-∪⁺ʳ _ xs ys (zs⊆ ∈zs)

  ∪-congʳ : xs ≈ ys → xs ∪ zs ≈ ys ∪ zs
  ∪-congʳ {xs = xs}{ys}{zs} (xs⊆ , ys⊆) = xs∪zs⊆ , ys∪zs⊆
    where
      xs∪zs⊆ : xs ∪ zs ⊆ˢ ys ∪ zs
      xs∪zs⊆ = ∈-∪⁻ _ xs zs >≡> λ where
        (inj₁ ∈xs) → ∈-∪⁺ˡ _ ys zs (xs⊆ ∈xs)
        (inj₂ ∈zs) → ∈-∪⁺ʳ _ ys zs ∈zs

      ys∪zs⊆ : ys ∪ zs ⊆ˢ xs ∪ zs
      ys∪zs⊆ = ∈-∪⁻ _ ys zs >≡> λ where
        (inj₁ ∈ys) → ∈-∪⁺ˡ _ xs zs (ys⊆ ∈ys)
        (inj₂ ∈zs) → ∈-∪⁺ʳ _ xs zs ∈zs


module _ {A : Type} ⦃ _ : DecEq A ⦄ where
  private variable
    x x′ : A; xs xs′ ys zs : Set⟨ A ⟩
    B : Type; P : Pred₀ A

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

  from-∷ˢ : ∀ {xs} → from (x ∷ xs) ≈ (x ∷ˢ from xs)
  from-∷ˢ {x = x}{xs} =
    (λ x∈ → case ∈ˢ-fromList⁻ {xs = x ∷ xs} x∈ of λ where
      (here refl) → hereˢ {xs = from xs}
      (there x∈)  → thereˢ {xs = from xs} $ ∈ˢ-fromList⁺ x∈
    )
    ,
    (λ x∈ → ∈ˢ-fromList⁺ {xs = x ∷ xs} $ case ∈ˢ-∷⁻ {xs = from xs} x∈ of λ where
      (inj₁ refl) → here refl
      (inj₂ x∈)   → there $ ∈ˢ-fromList⁻ {xs = xs} x∈
    )

  from-++ˢ : ∀ {xs ys : List A} → from (xs ++ ys) ≈ (from xs ∪ from ys)
  from-++ˢ {xs = xs}{ys} =
    (λ x∈ →
      case L.Mem.∈-++⁻ xs (∈ˢ-fromList⁻ x∈) of λ where
         (inj₁ x∈ˡ) → ∈-∪⁺ˡ _ (from xs) (from ys) $ ∈ˢ-fromList⁺ x∈ˡ
         (inj₂ x∈ʳ) → ∈-∪⁺ʳ _ (from xs) (from ys) $ ∈ˢ-fromList⁺ x∈ʳ
    )
    ,
    (λ x∈ →
      ∈ˢ-fromList⁺ $ case ∈-∪⁻ _ (from xs) (from ys) x∈ of λ where
        (inj₁ x∈ˡ) → L.Mem.∈-++⁺ˡ {xs = xs}{ys} $ ∈ˢ-fromList⁻ x∈ˡ
        (inj₂ x∈ʳ) → L.Mem.∈-++⁺ʳ xs $ ∈ˢ-fromList⁻ x∈ʳ
    )

  from-≈ : ∀ {xs ys : List A} →
    xs ∼[set] ys
    ──────────────────
    from xs ≈ from ys
  from-≈ {xs}{ys} eq =
    ( ∈ˢ-fromList⁺ {xs = ys}
    ∘ eq .Fun.Equiv.Equivalence.to .Fun.Eq._⟨$⟩_
    ∘ ∈ˢ-fromList⁻
    ) ,
    ( ∈ˢ-fromList⁺ {xs = xs}
    ∘ eq .Fun.Equiv.Equivalence.from .Fun.Eq._⟨$⟩_
    ∘ ∈ˢ-fromList⁻
    )

  from-≈˘ : ∀ {xs ys : List A} →
    from xs ≈ from ys
    ──────────────────
    xs ∼[set] ys
  from-≈˘ {xs}{ys} eq = ⊆⊇⇒∼set $
    ( ∈ˢ-fromList⁻
    ∘ eq .proj₁
    ∘ ∈ˢ-fromList⁺ {xs = xs}
    ) ,
    ( ∈ˢ-fromList⁻
    ∘ eq .proj₂
    ∘ ∈ˢ-fromList⁺ {xs = ys}
    )

  to-∷ˢ : (to $ x ∷ˢ xs) ∼[set] (x ∷ to xs)
  to-∷ˢ {x = x} = ⊆⊇⇒∼set $
    (λ where
      𝟘 → 𝟘
      (there {x = x} x∈) → there $′ L.Mem.∈-filter⁻ p? x∈ .proj₁
    ) ,
    (λ where
      𝟘 → 𝟘
      {x′} (there {x = x} x∈) →
        case x′ ≟ x of λ where
          (yes x≡) → here x≡
          (no  x≢) → there $′ L.Mem.∈-filter⁺ p? x∈ λ where 𝟘 → x≢ refl
    )
    where p? = _∉? [ x ]
          pattern 𝟘 = here refl

  to-++ˢ : (to $ xs ∪ ys) ∼[set] (to xs ++ to ys)
  to-++ˢ {xs}{ys} = ⊆⊇⇒∼set $
    (∈-++⁻ (to xs) >≡> λ where
      (inj₁ x∈ˡ) → ∈-++⁺ˡ x∈ˡ
      (inj₂ x∈ʳ) → ∈-++⁺ʳ (to xs) (L.Mem.∈-filter⁻ (_∉ˢ? xs) x∈ʳ .proj₁)
    ) ,
    (∈-++⁻ (to xs) >≡> λ where
      (inj₁ x∈ˡ) → ∈-++⁺ˡ x∈ˡ
      (inj₂ x∈ʳ) → case _ ∈ˢ? xs of λ where
        (yes x∈ˡ) → ∈-++⁺ˡ x∈ˡ
        (no  x∉ˡ) → ∈-++⁺ʳ (to xs) (L.Mem.∈-filter⁺ (_∉ˢ? xs) x∈ʳ x∉ˡ))

  to-≈ :
    xs ≈ ys
    ──────────────────
    to xs ∼[set] to ys
  to-≈ = ⊆⊇⇒∼set

  headˢ : Set⟨ A ⟩ → Maybe A
  headˢ = L.head ∘ to

  filterˢ : ∀ {P : Pred₀ A} → Decidable¹ P → Set⟨ A ⟩ → Set⟨ A ⟩
  filterˢ P? = from ∘ filter P? ∘ to

  module _ {B : Type} ⦃ _ : DecEq B ⦄ where
    private variable y : B

    mapˢ : (A → B) → (Set⟨ A ⟩ → Set⟨ B ⟩)
    mapˢ f = from ∘ map f ∘ to

    mapWith∈ˢ : (xs : Set⟨ A ⟩) → (∀ {x} → x ∈ˢ xs → B) → Set⟨ B ⟩
    mapWith∈ˢ xs f = from
                  $ L.Mem.mapWith∈ (to xs)
                  $ f ∘ ∈-nub⁻ ∘ ∈ˢ-fromList⁺

    module _ (f : A → B) where
      ∈ˢ-map⁺ : x ∈ˢ xs → f x ∈ˢ mapˢ f xs
      ∈ˢ-map⁺ = ∈ˢ-fromList⁺ ∘ L.Mem.∈-map⁺ f

      ∈ˢ-map⁻ : y ∈ˢ mapˢ f xs → ∃ λ x → x ∈ˢ xs × y ≡ f x
      ∈ˢ-map⁻ = L.Mem.∈-map⁻ f ∘ ∈ˢ-fromList⁻

      mapˢ-∪ : mapˢ f (xs ∪ ys) ≈ (mapˢ f xs ∪ mapˢ f ys)
      mapˢ-∪ {xs}{ys} =
        let xs′ = mapˢ f xs; ys′ = mapˢ f ys; xys′ = mapˢ f (xs ∪ ys) in
        (λ y∈ →
          let x , x∈ , eq = ∈ˢ-map⁻ {xs = xs ∪ ys} y∈
          in case ∈-∪⁻ x xs ys x∈ of λ where
               (inj₁ x∈ˡ) → ∈-∪⁺ˡ _ xs′ ys′
                          $ subst (_∈ˢ xs′) (sym eq)
                          $ ∈ˢ-map⁺ {xs = xs} x∈ˡ
               (inj₂ x∈ʳ) → ∈-∪⁺ʳ _ xs′ ys′
                          $ subst (_∈ˢ ys′) (sym eq)
                          $ ∈ˢ-map⁺ {xs = ys} x∈ʳ
        ) ,
        (λ y∈ →
          case ∈-∪⁻ _ xs′ ys′ y∈ of λ where
            (inj₁ y∈ˡ) →
              let x , x∈ˡ , eq = ∈ˢ-map⁻ {xs = xs} y∈ˡ
              in  subst (_∈ˢ xys′) (sym eq)
                $ ∈ˢ-map⁺ {xs = xs ∪ ys}
                $ ∈-∪⁺ˡ _ xs ys x∈ˡ
            (inj₂ y∈ʳ) →
              let x , x∈ʳ , eq = ∈ˢ-map⁻ {xs = ys} y∈ʳ
              in  subst (_∈ˢ xys′) (sym eq)
                $ ∈ˢ-map⁺ {xs = xs ∪ ys}
                $ ∈-∪⁺ʳ _ xs ys x∈ʳ
        )

    mapMaybeˢ : (A → Maybe B) → (Set⟨ A ⟩ → Set⟨ B ⟩)
    mapMaybeˢ f = from ∘ mapMaybe f ∘ to

    module _ (f : A → Maybe B) where
      ∈ˢ-mapMaybe⁺ : x ∈ˢ xs → f x ≡ just y → y ∈ˢ mapMaybeˢ f xs
      ∈ˢ-mapMaybe⁺ = ∈ˢ-fromList⁺ ∘₂ ∈-mapMaybe⁺ f

      ∈ˢ-mapMaybe⁻ : y ∈ˢ mapMaybeˢ f xs → ∃ λ x → (x ∈ˢ xs) × (f x ≡ just y)
      ∈ˢ-mapMaybe⁻ = ∈-mapMaybe⁻ f ∘ ∈ˢ-fromList⁻

      mapMaybeˢ-∪ : mapMaybeˢ f (xs ∪ ys) ≈ (mapMaybeˢ f xs ∪ mapMaybeˢ f ys)
      mapMaybeˢ-∪ {xs}{ys} =
        let xs′ = mapMaybeˢ f xs; ys′ = mapMaybeˢ f ys in
        (λ y∈ →
          let x , x∈ , eq = ∈ˢ-mapMaybe⁻ {xs = xs ∪ ys} y∈
          in case ∈-∪⁻ x xs ys x∈ of λ where
               (inj₁ x∈ˡ) → ∈-∪⁺ˡ _ xs′ ys′ $ ∈ˢ-mapMaybe⁺ {xs = xs} x∈ˡ eq
               (inj₂ x∈ʳ) → ∈-∪⁺ʳ _ xs′ ys′ $ ∈ˢ-mapMaybe⁺ {xs = ys} x∈ʳ eq)
        ,
        (λ y∈ →
          case ∈-∪⁻ _ xs′ ys′ y∈ of λ where
            (inj₁ y∈ˡ) →
              let x , x∈ˡ , eq = ∈ˢ-mapMaybe⁻ {xs = xs} y∈ˡ
              in  ∈ˢ-mapMaybe⁺ {xs = xs ∪ ys} (∈-∪⁺ˡ _ xs ys x∈ˡ) eq
            (inj₂ y∈ʳ) →
              let x , x∈ʳ , eq = ∈ˢ-mapMaybe⁻ {xs = ys} y∈ʳ
              in  ∈ˢ-mapMaybe⁺ {xs = xs ∪ ys} (∈-∪⁺ʳ _ xs ys x∈ʳ) eq
        )

  module _ {F : Set↑} ⦃ _ : Foldable F ⦄ ⦃ _ : Monad F ⦄ ⦃ _ : DecEq (F A) ⦄ where
    sequenceMˢ : Set⟨ F A ⟩ → F (Set⟨ A ⟩)
    sequenceMˢ = fmap from ∘ sequenceM ∘ to

-- ** concat
module _ {A : Type} ⦃ _ : DecEq A ⦄ where

  concatˢ : Set⟨ Set⟨ A ⟩ ⟩ → Set⟨ A ⟩
  concatˢ = from ∘ concatMap to ∘ to

  private variable xss yss : Set⟨ Set⟨ A ⟩ ⟩

  concatˢ-∪ : concatˢ xss ∪ concatˢ yss ≈ concatˢ (xss ∪ yss)
  concatˢ-∪ {xss}{yss} =
    begin
      concatˢ xss ∪ concatˢ yss
    ≡⟨⟩
      from (concatMap to $ to xss) ∪ from (concatMap to $ to yss)
    ≈˘⟨ from-++ˢ {xs = concatMap to $ to xss} ⟩
      from (concatMap to (to xss) ++ concatMap to (to yss))
    ≡˘⟨ cong from $ concatMap-++ to (to xss) _ ⟩
      from (concatMap to (to xss ++ to yss))
    ≈˘⟨ from-≈ $ ∼[set]-concatMap⁺ to $ to-++ˢ {xs = xss}{yss} ⟩
      from (concatMap to $ to (xss ∪ yss))
    ≡⟨⟩
      concatˢ (xss ∪ yss)
    ∎

  ≈ˢ-concat⁺ :
    xss ≈ yss
    ─────────────────────────
    concatˢ xss ≈ concatˢ yss
  ≈ˢ-concat⁺ {xss}{yss} eq =
    begin
      concatˢ xss
    ≡⟨⟩
      from (concatMap to $ to xss)
    ≈⟨ from-≈ $ ∼[set]-concatMap⁺ to $ to-≈ {xs = xss}{yss} eq ⟩
      from (concatMap to $ to yss)
    ≡⟨⟩
      concatˢ yss
    ∎

-- ** map
module _ {A B : Type} ⦃ _ : DecEq A ⦄ ⦃ _ : DecEq B ⦄ where
  private variable xs ys : Set⟨ A ⟩

  module _ (f : A → B) where

    ≈ˢ-map⁺ :
      xs ≈ ys
      ─────────────────────
      mapˢ f xs ≈ mapˢ f ys
    ≈ˢ-map⁺ {xs}{ys} = from-≈ ∘ ∼[set]-map⁺ f ∘ to-≈ {xs = xs}{ys}

    mapˢ-∪-commute : mapˢ f (xs ∪ ys) ≈ mapˢ f xs ∪ mapˢ f ys
    mapˢ-∪-commute {xs}{ys} =
      begin
        mapˢ f (xs ∪ ys)
      ≡⟨⟩
        from (map f $ to (xs ∪ ys))
      ≈⟨ from-≈ $ ∼[set]-map⁺ f $ to-++ˢ {xs = xs}{ys} ⟩
        from (map f $ to xs ++ to ys)
      ≡⟨ cong from $ L.map-++-commute f (to xs) _ ⟩
        from (map f (to xs) ++ map f (to ys))
      ≈⟨ from-++ˢ {xs = map f $ to xs} ⟩
        from (map f $ to xs) ∪ from (map f $ to ys)
      ≡⟨⟩
        mapˢ f xs ∪ mapˢ f ys
      ∎

  module _ (f : A → Maybe B) where
    ≈ˢ-mapMaybe⁺ :
      xs ≈ ys
      ───────────────────────────────
      mapMaybeˢ f xs ≈ mapMaybeˢ f ys
    ≈ˢ-mapMaybe⁺ {xs}{ys} = from-≈ ∘ ∼[set]-mapMaybe⁺ f ∘ to-≈ {xs = xs}{ys}

-- ** concatMap
module _ {A B : Type} ⦃ _ : DecEq A ⦄ ⦃ _ : DecEq B ⦄ where
  filterˢ₁ : Set⟨ A ⊎ B ⟩ → Set⟨ A ⟩
  filterˢ₁ = mapMaybeˢ isInj₁

  filterˢ₂ : Set⟨ A ⊎ B ⟩ → Set⟨ B ⟩
  filterˢ₂ = mapMaybeˢ isInj₂

  concatMapˢ : (A → Set⟨ B ⟩) → (Set⟨ A ⟩ → Set⟨ B ⟩)
  concatMapˢ f = concatˢ ∘ mapˢ f

  module _ (f : A → Set⟨ B ⟩) {xs ys} where
    concatMapˢ-∪ : concatMapˢ f (xs ∪ ys) ≈ concatMapˢ f xs ∪ concatMapˢ f ys
    concatMapˢ-∪ =
      begin
        concatMapˢ f (xs ∪ ys)
      ≡⟨⟩
        concatˢ (mapˢ f (xs ∪ ys))
      ≈⟨ ≈ˢ-concat⁺ {xss = mapˢ f (xs ∪ ys)}{yss = mapˢ f xs ∪ mapˢ f ys}
                  $ mapˢ-∪-commute f {xs}{ys} ⟩
        concatˢ (mapˢ f xs ∪ mapˢ f ys)
      ≈˘⟨ concatˢ-∪ {xss = mapˢ f xs}{mapˢ f ys} ⟩
        concatˢ (mapˢ f xs) ∪ concatˢ (mapˢ f ys)
      ≡⟨⟩
        concatMapˢ f xs ∪ concatMapˢ f ys
      ∎

    ≈ˢ-concatMap⁺ :
      xs ≈ ys
      ─────────────────────────────────
      concatMapˢ f xs ≈ concatMapˢ f ys
    ≈ˢ-concatMap⁺ = ≈ˢ-concat⁺ {xss = mapˢ f xs}{mapˢ f ys} ∘ ≈ˢ-map⁺ f {xs}{ys}

-- ** align/zip/partition
module _ {A B C : Type} ⦃ _ : DecEq A ⦄ ⦃ _ : DecEq B ⦄ ⦃ _ : DecEq C ⦄ where
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

module _ {A B : Type} ⦃ _ : DecEq A ⦄ ⦃ _ : DecEq B ⦄ where
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

module _ {A B C : Type} ⦃ _ : DecEq A ⦄ ⦃ _ : DecEq B ⦄ ⦃ _ : DecEq C ⦄ where
  unzip₃ˢ : Set⟨ A × B × C ⟩ → Set⟨ A ⟩ × Set⟨ B ⟩ × Set⟨ C ⟩
  unzip₃ˢ = map₂ unzipˢ ∘ unzipˢ

-- ** sum
sumˢ : Set⟨ ℕ ⟩ → ℕ
sumˢ = sum ∘ to

-- ** bimap

module _ {A A′ B B′ : Type}
  ⦃ _ : DecEq A ⦄ ⦃ _ : DecEq A′ ⦄ ⦃ _ : DecEq B ⦄ ⦃ _ : DecEq B′ ⦄
  where

  bimapˢ : (f : A → A′) (g : B → B′) → Set⟨ A × B ⟩ → Set⟨ A′ × B′ ⟩
  bimapˢ = mapˢ ∘₂ bimap

module _ {A A′ B : Type} ⦃ _ : DecEq A ⦄ ⦃ _ : DecEq A′ ⦄ ⦃ _ : DecEq B ⦄ where
  map₁ˢ  : (A → A′) → Set⟨ A × B ⟩ → Set⟨ A′ × B ⟩
  map₁ˢ = flip bimapˢ id

module _ {A B B′ : Type} ⦃ _ : DecEq A ⦄ ⦃ _ : DecEq B ⦄ ⦃ _ : DecEq B′ ⦄ where
  map₂ˢ : (B → B′) → Set⟨ A × B ⟩ → Set⟨ A × B′ ⟩
  map₂ˢ = bimapˢ id
