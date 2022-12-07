module Prelude.Irrelevance.List.Membership where

open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.InferenceRules

open import Prelude.Irrelevance.Core
open import Prelude.Irrelevance.Empty

-- ** irrelevant version of Data.List.Relation.Binary.Permutation
open import Data.List.Relation.Unary.First as Fst using (First; [_]; _∷_)
private pattern 𝟙 = Fst.[ refl ]; pattern 𝟚 x = x ∷ Fst.[ refl ]
import Data.List.Relation.Unary.First.Properties as Fst

module _ {A : Type ℓ} where

  private variable
    x y : A
    xs ys zs : List A
    P : Pred A ℓ′

  ·Any : Pred A ℓ′ → Pred (List A) _
  ·Any P = First (·¬_ ∘ P) P

  _·∈_ : A → List A → Type ℓ
  x ·∈ xs = ·Any (x ≡_) xs

  ·∈⇒∈ : x ·∈ xs → x L.Mem.∈ xs
  ·∈⇒∈ = Fst.toAny

  module _ ⦃ _ : P ⁇¹ ⦄ where
    ·Any-resp-↭ : ·Any P Respects _↭_
    ·Any-resp-↭ ↭-refl wit         = wit
    ·Any-resp-↭ (↭-prep x p) First.[ px ] = First.[ px ]
    ·Any-resp-↭ (↭-prep x p) (¬px ∷ wit) = ¬px ∷ ·Any-resp-↭ p wit
    ·Any-resp-↭ (↭-swap x y p) First.[ px ]
      with ¿ P y ¿
    ... | yes py = First.[ py ]
    ... | no ¬py = ¬⇒·¬ ¬py ∷ First.[ px ]
    ·Any-resp-↭ (↭-swap x y p) (¬px ∷ First.[ py ]) = First.[ py ]
    ·Any-resp-↭ (↭-swap x y p) (¬px ∷ ¬py ∷ wit) = ¬py ∷ ¬px ∷ ·Any-resp-↭ p wit
    ·Any-resp-↭ (↭-trans p q) wit = ·Any-resp-↭ q $ ·Any-resp-↭ p wit

  module _ ⦃ _ : DecEq A ⦄ where
    ·∈-resp-↭ : ∀ {x : A} → (x ·∈_) Respects _↭_
    ·∈-resp-↭ = ·Any-resp-↭

  module _ {a p} {A : Set a} where
    ·∁ : Pred A ℓ′ → Pred A ℓ′
    (·∁ P) x = ·¬ P x

    import Relation.Nullary.Decidable as Dec
    module _ {P : Pred A p} where
      first? : Decidable¹ P → Decidable¹ (First P (·∁ P))
      first? P? xs = Dec.map′ (Fst.map id ¬⇒·¬) (Fst.map id ·¬⇒¬)
                              (Fst.first? P? xs)

      cofirst? : Decidable¹ P → Decidable¹ (First (·∁ P) P)
      cofirst? P? xs = Dec.map′ (Fst.map ¬⇒·¬ id)  (Fst.map ·¬⇒¬ id)
                                (Fst.cofirst? P? xs)

  instance
    ··∈ : ·² _·∈_
    ··∈ .∀≡ = Fst.irrelevant ·¬⇒¬ ∀≡ ∀≡

    Dec-·∈ : ⦃ DecEq A ⦄ → _·∈_ ⁇²
    Dec-·∈ .dec = cofirst? (_ ≟_) _

  infixl 4 _─_
  _─_ : ∀ xs → x ·∈ xs → List A
  xs ─ x∈ = xs L.Any.─ Fst.toAny x∈

  ·∈-─⁺ :
    ∀ (x∈ : x ·∈ xs) →
    ∙ x ≢ y
    ∙ y ·∈ xs
      ────────────────
      y ·∈ (xs ─ x∈)
  ·∈-─⁺ 𝟙 x≢y 𝟙 = ⊥-elim $ x≢y refl
  ·∈-─⁺ 𝟙 _ (_ ∷ y∈) = y∈
  ·∈-─⁺ (_ ∷ _) _ 𝟙 = 𝟙
  ·∈-─⁺ (_ ∷ x∈) x≢y (≢ ∷ y∈) = ≢ ∷ ·∈-─⁺ x∈ x≢y y∈

  ·∈-─⁻ :
    ∀ (x∈ : x ·∈ xs) →
    ∙ x ≢ y
    ∙ y ·∈ (xs ─ x∈)
      ────────────────
      y ·∈ xs
  ·∈-─⁻ 𝟙 x≢y y∈ = (¬⇒·¬ $ ≢-sym x≢y) ∷ y∈
  ·∈-─⁻ (_ ∷ x∈) x≢y 𝟙 = 𝟙
  ·∈-─⁻ (_ ∷ x∈) x≢y (≢ ∷ y∈) = ≢ ∷ ·∈-─⁻ x∈ x≢y y∈

  module _ ⦃ _ : DecEq A ⦄ where
    ·∈-─⁻′ :
      ∀ (x∈ : x ·∈ xs) →
      ∙ y ·∈ (xs ─ x∈)
        ────────────────
        y ·∈ xs
    ·∈-─⁻′ {x = x} {y = y} 𝟙 y∈
      with y ≟ x
    ... | yes refl = 𝟙
    ... | no ≢ = ¬⇒·¬ ≢ ∷ y∈
    ·∈-─⁻′ (_ ∷ x∈) 𝟙 = 𝟙
    ·∈-─⁻′ (_ ∷ x∈) (≢ ∷ y∈) = ≢ ∷ ·∈-─⁻′ x∈ y∈

  ─∘─ : (x∈ : x ·∈ xs)
      → (y∈ : y ·∈ xs)
      → (x≢y : x ≢ y)
      → (xs ─ x∈ ─ ·∈-─⁺ x∈ x≢y y∈)
      ≡ (xs ─ y∈ ─ ·∈-─⁺ y∈ (≢-sym x≢y) x∈)
  ─∘─ 𝟙 𝟙 _ = refl
  ─∘─ 𝟙 (_ ∷ _) _ = refl
  ─∘─ (_ ∷ _) 𝟙 _ = refl
  ─∘─ (_ ∷ x∈) (_ ∷ y∈) x≢y rewrite ─∘─ x∈ y∈ x≢y = refl
