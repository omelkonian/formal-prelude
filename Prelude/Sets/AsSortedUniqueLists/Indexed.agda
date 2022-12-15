{-# OPTIONS --with-K #-}
open import Prelude.Init; open SetAsType
open import Prelude.Lists.Dec
open import Prelude.Membership
open import Prelude.DecEq
open import Prelude.ToList
open import Prelude.FromList
open import Prelude.Indexable
open import Prelude.Measurable
open import Prelude.Lists.Indexed hiding (_‼_)
open import Prelude.Decidable
open import Prelude.Ord
open import Prelude.General

open import Data.List.Relation.Binary.Subset.Propositional.Properties using (Any-resp-⊆)
import Relation.Binary.Reasoning.Setoid as BinSetoid

open import Prelude.Sets.AsSortedUniqueLists.Core
open import Prelude.Sets.AsSortedUniqueLists.Extra

module Prelude.Sets.AsSortedUniqueLists.Indexed where

module _ {A : Type} ⦃ _ : DecEq A ⦄ ⦃ _ : Ord⁺⁺ A ⦄ where
  private variable
    x x′ : A; xs xs′ ys zs : Set⟨ A ⟩
    B : Type; P : Pred₀ A

  instance
    Indexable-Set : Indexable Set⟨ A ⟩ A
    Indexable-Set = λ where
      .Ix s → Fin ∣ s ∣
      ._‼_ s i → toList s ‼ i

  Indexˢ = Pred (Set⟨ A ⟩) _ ∋ Ix

  module _ {xs : List A} where postulate
    ‼-sort⁺ : Ix xs → Ix (sort xs)
    ‼-sort⁻ : Ix (sort xs) → Ix xs

  module _ {xs : List A} where
    ‼-from⁺ : Ix xs → Indexˢ (fromList xs)
    ‼-from⁺ = ‼-sort⁺ {xs = nub xs} ∘ ‼-nub⁺ {xs = xs}

    ‼-from⁻ : Indexˢ (fromList xs) → Ix xs
    ‼-from⁻ = ‼-nub⁻ {xs = xs} ∘ ‼-sort⁻ {xs = nub xs}

  ‼-to⁺ : Ix xs → Ix (toList xs)
  ‼-to⁺ = id

  ‼-to⁻ : Ix (toList xs) → Ix xs
  ‼-to⁻ = id

  module _ {B : Type} ⦃ _ : DecEq B ⦄ (xs : Set⟨ A ⟩) (f : A → Ix xs → B) where

    mapWithIxˢ : List B
    mapWithIxˢ = map (λ (i , x) → f x i) (enumerate $ xs ∙toList)

module _ {A : Type} ⦃ _ : DecEq A ⦄ ⦃ _ : Ord⁺⁺ A ⦄
         {B : Type} ⦃ _ : DecEq B ⦄ ⦃ _ : Ord⁺⁺ B ⦄ where

  module _ (f : A → B) {xs : Set⟨ A ⟩} where
    ‼-mapˢ : Ix xs → Ix (mapˢ f xs)
    ‼-mapˢ = ‼-from⁺ {xs = map f (xs ∙toList)}
           ∘ ‼-map⁺ f {xs ∙toList}

  module _ {xs : Set⟨ A ⟩} (f : ∀ {x} → x ∈ˢ xs → B) where

    ‼-mapWith∈ˢ : Ix xs → Ix (mapWith∈ˢ xs f)
    ‼-mapWith∈ˢ = ‼-from⁺ {xs = L.Mem.mapWith∈ (xs ∙toList) _}
                ∘ ‼-mapWith∈ {xs = xs ∙toList}

  module _ xs (f : A → Ix xs → B) where

    ‼-mapWithIx : Ix xs → Ix (mapWithIx xs f)
    ‼-mapWithIx i = ‼-mapWithIx⁺ {xs = xs ∙toList} f i
