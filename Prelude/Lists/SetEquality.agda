module Prelude.Lists.SetEquality where

open import Data.List.Relation.Binary.BagAndSetEquality

open import Prelude.Init
open L.Mem
open import Prelude.InferenceRules
open import Prelude.DecLists
open import Prelude.DecEq
open import Prelude.Lists.Core
open import Prelude.Lists.Membership
open import Prelude.General
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (Any-resp-⊆)

private variable
  A : Set ℓ; B : Set ℓ′
  xs ys : List A
  xss yss : List (List A)
  P Q : Pred A ℓ″

_∼[set]_ : Rel (List A) _
_∼[set]_ = _∼[ set ]_

_⊆⊇_ : Rel (List A) _
xs ⊆⊇ ys = (xs ⊆ ys) × (ys ⊆ xs)

⊆⊇-sym : Symmetric (Rel (List A) _ ∋ _⊆⊇_)
⊆⊇-sym = Product.swap

module _ where
  open Fun.Equiv.Equivalence

  ⊆⊇⇒∼set :
    xs ⊆⊇ ys
    ────────────
    xs ∼[set] ys
  ⊆⊇⇒∼set {xs = xs}{ys} (↝ , ↜) = λ where
    .to   → record {_⟨$⟩_ = ↝; cong = λ where refl → refl}
    .from → record {_⟨$⟩_ = ↜; cong = λ where refl → refl}

  ∼set⇒⊆⊇ :
    xs ∼[set] ys
    ────────────
    xs ⊆⊇ ys
  ∼set⇒⊆⊇ {xs = xs}{ys} eq = eq .to .Fun.Eq._⟨$⟩_ , eq .from .Fun.Eq._⟨$⟩_

∼set⇒⊆ :
  xs ∼[set] ys
  ────────────
  xs ⊆ ys
∼set⇒⊆ = proj₁ ∘ ∼set⇒⊆⊇

∼set⇒⊇ :
  xs ∼[set] ys
  ────────────
  ys ⊆ xs
∼set⇒⊇ = proj₂ ∘ ∼set⇒⊆⊇

∼set-sym : xs ∼[set] ys → ys ∼[set] xs
∼set-sym = ⊆⊇⇒∼set ∘ ⊆⊇-sym ∘ ∼set⇒⊆⊇

∼set⇒Any :
  xs ∼[set] ys
  ───────────────────
  Any P xs ↔ Any P ys
∼set⇒Any = ∼set⇒⊆⊇ >≡> λ (xs⊆ , ys⊆) → Any-resp-⊆ xs⊆ , Any-resp-⊆ ys⊆

nub-seteq : ∀ ⦃ _ : DecEq A ⦄ {xs : List A} →
  nub xs ∼[set] xs
nub-seteq = ⊆⊇⇒∼set (∈-nub⁻ , ∈-nub⁺)

lefts-seteq : ∀ {A B : Set} {abs abs′ : List (A ⊎ B)} →
        abs ∼[set] abs′
  ───────────────────────────
  lefts abs ∼[set] lefts abs′
lefts-seteq eq = let ↝ , ↜ = ∼set⇒⊆⊇ eq in
  ⊆⊇⇒∼set (∈-lefts⁺ ∘ ↝ ∘ ∈-lefts⁻ , ∈-lefts⁺ ∘ ↜ ∘ ∈-lefts⁻)

rights-seteq : ∀ {A B : Set} {abs abs′ : List (A ⊎ B)} →
        abs ∼[set] abs′
  ───────────────────────────
  rights abs ∼[set] rights abs′
rights-seteq eq = let ↝ , ↜ = ∼set⇒⊆⊇ eq in
  ⊆⊇⇒∼set (∈-rights⁺ ∘ ↝ ∘ ∈-rights⁻ , ∈-rights⁺ ∘ ↜ ∘ ∈-rights⁻)

∼[set]-concat⁺ :
  xss ∼[set] yss
  ────────────────────────────
  concat xss ∼[set] concat yss
∼[set]-concat⁺ xs~ys = ⊆⊇⇒∼set $
  (L.Any.concat⁺ ∘ ∼set⇒Any xs~ys .proj₁ ∘ ∈-concat⁻ _)
  ,
  (L.Any.concat⁺ ∘ ∼set⇒Any xs~ys .proj₂ ∘ ∈-concat⁻ _)

module _ (f : A → B) where
  ∼[set]-map⁺ :
    xs ∼[set] ys
    ────────────────────────
    map f xs ∼[set] map f ys
  ∼[set]-map⁺ xs~ys = ⊆⊇⇒∼set $
    (∈-map⁻ f >≡> λ where
      (_ , x∈ , refl) → ∈-map⁺ f $ ∼set⇒⊆ xs~ys x∈) ,
    (∈-map⁻ f >≡> λ where
      (_ , x∈ , refl) → ∈-map⁺ f $ ∼set⇒⊇ xs~ys x∈)

module _ (f : A → List B) where
  ∼[set]-concatMap⁺ :
    xs ∼[set] ys
    ────────────────────────────────────
    concatMap f xs ∼[set] concatMap f ys
  ∼[set]-concatMap⁺ = ∼[set]-concat⁺ ∘ ∼[set]-map⁺ f
