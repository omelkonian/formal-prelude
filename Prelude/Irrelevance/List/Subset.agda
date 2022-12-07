open import Data.List.Relation.Unary.First as Fst using (_∷_)

open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.InferenceRules

open import Prelude.Irrelevance.Core
open import Prelude.Irrelevance.Empty
open import Prelude.Irrelevance.List.Membership

module Prelude.Irrelevance.List.Subset {A : Type ℓ} where

infix 4 _·⊆_ -- _·⊇_ _·⊈_ _·⊉_

private
  variable x y : A; xs ys : List A
  pattern 𝟘 = here refl
  pattern 𝟙 = Fst.[ refl ]
  pattern 𝟚 x = x ∷ Fst.[ refl ]

module _ ⦃ _ : DecEq A ⦄ where
  ∈⇒·∈ : x L.Mem.∈ xs → x ·∈ xs
  ∈⇒·∈ (here refl) = 𝟙
  ∈⇒·∈ {x = x} (there {x = y} p)
    with x ≟ y
  ... | yes refl = 𝟙
  ... | no ≢ = ¬⇒·¬ ≢ ∷ ∈⇒·∈ p

data _·⊆_ : Rel (List A) ℓ where

  [] : [] ·⊆ xs

  _∷_ : ∀ (x∈ : x ·∈ ys) →
    xs ·⊆ (ys ─ x∈)
    ───────────────
    (x ∷ xs) ·⊆ ys

instance
  ··⊆ : ·² _·⊆_
  ··⊆ .∀≡ [] [] = refl
  ··⊆ .∀≡ (x∈ ∷ p) (x∈₁ ∷ q) rewrite ∀≡ x∈ x∈₁ | ∀≡ p q = refl

  Dec-·⊆ : ⦃ DecEq A ⦄ → _·⊆_ ⁇²
  Dec-·⊆ {x = []} {ys} .dec = yes []
  Dec-·⊆ {x = x ∷ xs} {ys} .dec
    with ¿ x ·∈ ys ¿
  ... | no x∉ = no λ where (x∈ ∷ _) → ⊥-elim $ x∉ x∈
  ... | yes x∈
    with ¿ xs ·⊆ (ys ─ x∈) ¿
  ... | no ¬IH = no λ where
    (_ ∷ IH) → ⊥-elim $ ¬IH $ subst (λ ◆ → xs ·⊆ (ys ─ ◆)) (∀≡ _ _) IH
  ... | yes IH = yes (x∈ ∷ IH)

·⊆⇒·∈ : xs ·⊆ ys → (∀ x → x ·∈ xs → x ·∈ ys)
·⊆⇒·∈ (x∈ ∷ p) x Fst.[ refl ] = x∈
·⊆⇒·∈ (x∈ ∷ p) x (≢ ∷ x∈′) =
  ·∈-─⁻ x∈ (≢-sym $ ·¬⇒¬ ≢) (·⊆⇒·∈ p x x∈′)

-- ·⊆⇒∈ : xs ·⊆ ys → (∀ x → x ∈ xs → x ∈ ys)
-- ·⊆⇒∈ (x∈ ∷ p) x Fst.[ refl ] = x∈
-- ·⊆⇒∈ (x∈ ∷ p) x (≢ ∷ x∈′) =
--   ·∈-─⁻ x∈ (≢-sym $ ·¬⇒¬ ≢) (·⊆⇒·∈ p x x∈′)

infix 4 _·⊆′_
_·⊆′_ : Rel (List A) _
xs ·⊆′ ys = _·∈ xs ⊆¹ _·∈ ys

·⊆⇒·⊆′ : xs ·⊆ ys → xs ·⊆′ ys
·⊆⇒·⊆′ {x ∷ _} (x∈ ∷ p) {.x} 𝟙 = x∈
·⊆⇒·⊆′ {x ∷ _} (x∈ ∷ p) {y} (≢ ∷ y∈)
  = ·∈-─⁻ _ (≢-sym $ ·¬⇒¬ ≢) $ ·⊆⇒·⊆′ p y∈

·⊆-∷ :
  x ∷ xs ·⊆ x ∷ ys
  ────────────────
  xs ·⊆ ys
·⊆-∷ (𝟙 ∷ p) = p
·⊆-∷ ((x≢x ∷ _) ∷ _) = ·⊥-elim $ x≢x refl

module _ ⦃ _ : DecEq A ⦄ where
  ·⊆⇒⊆ : xs ·⊆ ys → xs ⊆ ys
  ·⊆⇒⊆ {[]} [] = λ ()
  ·⊆⇒⊆ {x ∷ xs}{ys} (x∈ys ∷ p) = λ where
    (here refl) → ·∈⇒∈ x∈ys
    (there x∈′) → ·∈⇒∈
                $ ·∈-─⁻′ x∈ys
                $ ·⊆⇒·∈ p _
                $ ∈⇒·∈ x∈′
