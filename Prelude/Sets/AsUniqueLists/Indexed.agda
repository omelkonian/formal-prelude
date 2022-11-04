open import Prelude.Init; open SetAsType
open import Prelude.DecLists
open import Prelude.Membership
open import Prelude.DecEq
open import Prelude.ToList
open import Prelude.FromList
open import Prelude.Indexable
open import Prelude.Measurable
open import Prelude.Lists.Indexed using (‼-map; ‼-mapWith∈)

open import Data.List.Relation.Binary.Subset.Propositional.Properties using (Any-resp-⊆)
import Relation.Binary.Reasoning.Setoid as BinSetoid

open import Prelude.Sets.AsUniqueLists.Core
open import Prelude.Sets.AsUniqueLists.Extra

module Prelude.Sets.AsUniqueLists.Indexed where

module _ {A : Type} ⦃ _ : DecEq A ⦄ where
  private variable
    x x′ : A; xs xs′ ys zs : Set⟨ A ⟩
    B : Type; P : Pred₀ A

  instance
    Indexable-Set : Indexable Set⟨ A ⟩ A
    Indexable-Set = λ where
      .Ix s → Fin ∣ s ∣
      ._‼_ s i → toList s ‼ i

  Indexˢ = Pred (Set⟨ A ⟩) _ ∋ Ix

  ‼-nub⁺ : ∀ {xs : List A} → Ix xs → Ix (nub xs)
  ‼-nub⁺ {x ∷ xs} i with x ∈? xs
  ... | yes x∈ = ‼-nub⁺ {xs} $ L.Any.index x∈
  ... | no  _ = case i of λ where
    fzero    → fzero
    (fsuc j) → fsuc $ ‼-nub⁺ {xs} j

  ‼-nub⁻ : ∀ {xs : List A} → Ix (nub xs) → Ix xs
  ‼-nub⁻ {x ∷ xs} i with x ∈? xs
  ... | yes x∈ = fsuc $ ‼-nub⁻ {xs} i
  ... | no  _ = case i of λ where
    fzero    → fzero
    (fsuc j) → fsuc $ ‼-nub⁻ {xs} j

  ‼-from⁺ : ∀ {xs : List A} → Ix xs → Indexˢ (fromList xs)
  ‼-from⁺ {xs} = ‼-nub⁺ {xs}

  ‼-from⁻ : ∀ {xs : List A} → Indexˢ (fromList xs) → Ix xs
  ‼-from⁻ {xs} = ‼-nub⁻ {xs}

  ‼-to⁺ : Ix xs → Ix (toList xs)
  ‼-to⁺ = id

  ‼-to⁻ : Ix (toList xs) → Ix xs
  ‼-to⁻ = id

module _ {A : Type} ⦃ _ : DecEq A ⦄ {xs : Set⟨ A ⟩} where
  module _ {B : Type} ⦃ _ : DecEq B ⦄ (f : A → B) where
    ‼-mapˢ : Ix xs → Ix (mapˢ f xs)
    ‼-mapˢ = ‼-from⁺ {xs = map f (xs ∙toList)}
           ∘ ‼-map {xs = xs ∙toList}

  module _ {B : Type} ⦃ _ : DecEq B ⦄ (f : ∀ {x} → x ∈ˢ xs → B) where

    ‼-mapWith∈ˢ : Ix xs → Ix (mapWith∈ˢ xs f)
    ‼-mapWith∈ˢ = ‼-from⁺ {xs = L.Mem.mapWith∈ (xs ∙toList) (f ∘ ∈-nub⁻ ∘ ∈ˢ-fromList⁺)}
                ∘ ‼-mapWith∈ {xs = xs ∙toList}
