open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.Decidable

open import Prelude.Ord.Core
open import Prelude.Ord.Dec

module Prelude.Ord.Iso {A : Type ℓ} ⦃ _ : Ord A ⦄ {B : Type ℓ} (f : B → A) where

mkOrd≈ : Ord B
mkOrd≈ = λ where
  ._<_ → _<_ on f
  ._≤_ → _≤_ on f

private instance _ = mkOrd≈

module _ ⦃ _ : DecOrd A ⦄ where
  mkDecOrd≈ : DecOrd B
  mkDecOrd≈ = λ where
    .Dec-≤ .dec → _ ≤? _
    .Dec-< .dec → _ <? _

module _ ⦃ _ : OrdLaws A ⦄ (mk≡ : Injective≡ f) (unmk≡ : Congruent≡ f) where
  mkOrdLaws≈ : OrdLaws B
  mkOrdLaws≈ = record
    { ≤-refl = ≤-refl
    ; ≤-trans = ≤-trans
    ; ≤-antisym = mk≡ ∘₂ ≤-antisym
    ; ≤-total = λ _ _ → ≤-total _ _
    ; <-irrefl = <-irrefl ∘ unmk≡
    ; <-trans = <-trans
    ; <-resp₂-≡ = (<-resp₂-≡ .proj₁ ∘ unmk≡) , (<-resp₂-≡ .proj₂ ∘ unmk≡)
    ; <-cmp = λ _ _ → Tri-map id↔ (mk≡ , unmk≡) id↔ (<-cmp _ _)
    ; <⇒≤ = <⇒≤
    ; <⇒≢ = λ p → <⇒≢ p ∘ unmk≡
    ; ≤∧≢⇒< = λ (p , q) → ≤∧≢⇒< (p , q ∘ mk≡)
    }
