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

open import Prelude.Lists.Core
open import Prelude.Lists.MapMaybe
open import Prelude.Lists.SetEquality
open import Prelude.Lists.Concat

open import Data.List.Relation.Binary.Subset.Propositional.Properties using (Any-resp-⊆)
import Relation.Binary.Reasoning.Setoid as BinSetoid
open ≈-Reasoning

open import Prelude.Sets.AsUniqueLists.Core
open import Prelude.Sets.AsUniqueLists.Extra

module Prelude.Sets.AsUniqueLists.SetMappings {A : Set} ⦃ _ : DecEq A ⦄ where

private variable
  x x′ : A; xs xs′ ys zs : Set⟨ A ⟩
  B : Type; P : Pred₀ A

infix 0 mk↦_
data _↦′_ : Set⟨ A ⟩ → Pred₀ A → Type where
  mk↦_ : (∀ {x} → x ∈ˢ xs → P x) → xs ↦′ P

unmk↦_ : xs ↦′ P → (∀ {x} → x ∈ˢ xs → P x)
unmk↦ (mk↦ p) = p

map↦ = _↦′_
syntax map↦ xs (λ x → f) = ∀[ x ∈ xs ] f

_↦_ : Set⟨ A ⟩ → Type → Type
xs ↦ B = xs ↦′ const B

dom : xs ↦′ P → Set⟨ A ⟩
dom {xs = xs} _ = xs

codom : ⦃ _ : DecEq B ⦄ → xs ↦ B → Set⟨ B ⟩
codom {xs = xs} (mk↦ f) = mapWith∈ˢ xs f

weaken-↦ : xs ↦′ P → ys ⊆ˢ xs → ys ↦′ P
weaken-↦ (mk↦ f) ys⊆xs = mk↦ f ∘ ys⊆xs

cons-↦ : (x : A) → P x → xs ↦′ P → (x ∷ˢ xs) ↦′ P
cons-↦ {xs = xs} x y (mk↦ f) = mk↦ ∈ˢ-∷⁻ {x′ = x}{xs} >≡> λ where
    (inj₁ refl) → y
    (inj₂ x∈)   → f x∈

uncons-↦ : (x ∷ˢ xs) ↦′ P → xs ↦′ P
uncons-↦ {x = x}{xs} (mk↦ f) = mk↦ f ∘ thereˢ {xs = xs}{x}

_↭ˢ_ : Rel₀ (Set⟨ A ⟩)
_↭ˢ_ = _↭_ on toList

module _ {xs ys} where
  permute-↦ : xs ↭ˢ ys → xs ↦′ P → ys ↦′ P
  permute-↦ xs↭ys (mk↦ xs↦) = mk↦
    xs↦ ∘ ∈ˢ-toList⁺ {xs = xs} ∘ L.Perm.∈-resp-↭ (↭-sym xs↭ys) ∘ ∈ˢ-toList⁻ {xs = ys}

  _∪/↦_ : xs ↦′ P → ys ↦′ P → (xs ∪ ys) ↦′ P
  (mk↦ xs↦) ∪/↦ (mk↦ ys↦) = mk↦ ∈-∪⁻ _ xs ys >≡> λ where
    (inj₁ x∈) → xs↦ x∈
    (inj₂ y∈) → ys↦ y∈

  destruct-∪/↦ : (xs ∪ ys) ↦′ P → (xs ↦′ P) × (ys ↦′ P)
  destruct-∪/↦ (mk↦ xys↦) = (mk↦ xys↦ ∘ ∈-∪⁺ˡ _ xs ys)
                          , (mk↦ xys↦ ∘ ∈-∪⁺ʳ _ xs ys)

  destruct≡-∪/↦ : zs ≡ xs ∪ ys → zs ↦′ P → (xs ↦′ P) × (ys ↦′ P)
  destruct≡-∪/↦ refl = destruct-∪/↦

extend-↦ : zs ↭ˢ (xs ∪ ys) → xs ↦′ P → ys ↦′ P → zs ↦′ P
extend-↦ zs↭ xs↦ ys↦ = permute-↦ (↭-sym zs↭) (xs↦ ∪/↦ ys↦)

cong-↦ : xs ↦′ P → xs′ ≈ xs → xs′ ↦′ P
cong-↦ (mk↦ f) eq = mk↦ f ∘ eq .proj₁
