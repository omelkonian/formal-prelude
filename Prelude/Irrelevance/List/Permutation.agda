module Prelude.Irrelevance.List.Permutation where

open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.InferenceRules

open import Prelude.Irrelevance.Core
open import Prelude.Irrelevance.Empty
open import Prelude.Irrelevance.List.Membership

-- ** irrelevant version of Data.List.Relation.Binary.Permutation
open import Data.List.Relation.Unary.First as Fst using (First; [_]; _∷_)
private pattern 𝟙 = Fst.[ refl ]; pattern 𝟚 x = x ∷ Fst.[ refl ]
import Data.List.Relation.Unary.First.Properties as Fst

module _ {A : Type ℓ} where

  private variable
    x y : A
    xs ys zs : List A
    P : Pred A ℓ′

  infix 3 _·↭_
  data _·↭_ : Rel (List A) ℓ where
    [] :
      ────────
      [] ·↭ []

    _∷_ : ∀ (x∈ : x ·∈ ys) →
      xs ·↭ ys ─ x∈
      ─────────────
      x ∷ xs ·↭ ys

  instance
    ··↭ : ·² _·↭_
    ··↭ .∀≡ []       []        = refl
    ··↭ .∀≡ (x∈ ∷ p) (x∈′ ∷ q) rewrite ∀≡ x∈ x∈′ | ∀≡ p q = refl

  ·↭-prep : ∀ x → xs ·↭ ys → x ∷ xs ·↭ x ∷ ys
  ·↭-prep _ = 𝟙 ∷_

  ·↭-drop-∷ : ∀ x → x ∷ xs ·↭ x ∷ ys → xs ·↭ ys
  ·↭-drop-∷ x (𝟙 ∷ p) = p
  ·↭-drop-∷ x ((x≢x ∷ _) ∷ _) = ·⊥-elim $ x≢x refl

  ·↭-refl : ∀ xs → xs ·↭ xs
  ·↭-refl [] = []
  ·↭-refl (_ ∷ xs) = ·↭-prep _ (·↭-refl xs)

  ·↭-─ : ∀ (x∈ : x ·∈ xs) → x ∷ (xs ─ x∈) ·↭ xs
  ·↭-─ 𝟙 = ·↭-refl _
  ·↭-─ p@(_ ∷ _) = p ∷ ·↭-prep _ (·↭-refl _)

  ↭-─ : ∀ (x∈ : x ·∈ xs) → x ∷ (xs ─ x∈) ↭ xs
  ↭-─ 𝟙 = ↭-refl
  ↭-─ {x}{y ∷ xs} (≢ ∷ x∈) =
    begin
      x ∷ y ∷ (xs ─ x∈)
    ↭⟨ ↭-swap x y ↭-refl ⟩
      y ∷ x ∷ (xs ─ x∈)
    ↭⟨ ↭-prep y $ ↭-─ x∈ ⟩
      y ∷ xs
    ∎ where open PermutationReasoning

  ·↭⇒↭ : xs ·↭ ys → xs ↭ ys
  ·↭⇒↭ {[]} [] = ↭-refl
  ·↭⇒↭ {x ∷ xs}{ys} (x∈ ∷ p) =
    begin
      x ∷ xs
    ↭⟨ ↭-prep _ $ ·↭⇒↭ p ⟩
      x ∷ (ys ─ x∈)
    ↭⟨ ↭-─ x∈ ⟩
      ys
    ∎ where open PermutationReasoning

  Any-resp-·↭ : Any P Respects _·↭_
  Any-resp-·↭ = L.Perm.Any-resp-↭ ∘ ·↭⇒↭

  module _ ⦃ _ : DecEq A ⦄ where
    ·↭-swap : ∀ x y → xs ·↭ ys → x ∷ y ∷ xs ·↭ y ∷ x ∷ ys
    ·↭-swap x y p with x ≟ y
    ... | yes refl = 𝟙 ∷ 𝟙 ∷ p
    ... | no ≢x = 𝟚 (¬⇒·¬ ≢x) ∷ 𝟙 ∷ p

    ·∈-resp-·↭ : (x ·∈_) Respects _·↭_
    ·∈-resp-·↭ = ·∈-resp-↭ ∘ ·↭⇒↭

    ∈-resp-·↭ : (x L.Mem.∈_) Respects _·↭_
    ∈-resp-·↭ = L.Perm.∈-resp-↭ ∘ ·↭⇒↭

    ·↭-∈-resp :
      ∀ (x∈ : x ·∈ xs) →
      ∀ (p : xs ·↭ ys) →
        ───────────────────────────────
        xs ─ x∈ ·↭ ys ─ ·∈-resp-·↭ p x∈
    ·↭-∈-resp {xs = _ ∷ xs}{ys} 𝟙 (x∈ ∷ p) =
      subst (λ ◆ → _ ·↭ _ ─ ◆) (∀≡ x∈ (·∈-resp-·↭ (x∈ ∷ p) 𝟙)) p
    ·↭-∈-resp {x = x}{xs = z ∷ xs}{ys} (z·≢x ∷ x∈xs) (z∈ys ∷ p)
      = z∈
      ∷ QED
      where
        z≢x = ·¬⇒¬ z·≢x

        x∈ys : x ·∈ ys
        x∈ys = ·∈-resp-·↭ (z∈ys ∷ p) (z·≢x ∷ x∈xs)

        z∈ : z ·∈ (ys ─ x∈ys)
        z∈ = ·∈-─ x∈ys z≢x z∈ys

        IH : xs ─ x∈xs ·↭ ys ─ z∈ys ─ ·∈-resp-·↭ p x∈xs
        IH = ·↭-∈-resp x∈xs p

        QED : xs ─ x∈xs ·↭ (ys ─ x∈ys) ─ z∈
        QED = subst (λ ◆ → _ ·↭ ◆) (sym $ ─∘─ x∈ys z∈ys z≢x)
            $ subst (λ ◆ → _ ·↭ _ ─ ◆)
                    (∀≡ (·∈-resp-·↭ p x∈xs) (·∈-─ z∈ys (≢-sym z≢x) x∈ys))
                    IH

    ·↭-trans : xs ·↭ ys → ys ·↭ zs → xs ·↭ zs
    ·↭-trans [] q = q
    ·↭-trans (x∈ ∷ p) q = ·∈-resp-·↭ q x∈
                        ∷ ·↭-trans p (·↭-∈-resp x∈ q)

    ↭⇒·↭ : xs ↭ ys → xs ·↭ ys
    ↭⇒·↭ {[]} p rewrite L.Perm.↭-empty-inv (↭-sym p) = []
    ↭⇒·↭ ↭-refl = ·↭-refl _
    ↭⇒·↭ (↭-prep _ p) = ·↭-prep _ (↭⇒·↭ p)
    ↭⇒·↭ (↭-swap _ _ p) = ·↭-swap _ _ (↭⇒·↭ p)
    ↭⇒·↭ (↭-trans xs↭ ↭zs) = ·↭-trans (↭⇒·↭ xs↭) (↭⇒·↭ ↭zs)

    ·↭-sym : xs ·↭ ys → ys ·↭ xs
    ·↭-sym = ↭⇒·↭ ∘ ↭-sym ∘ ·↭⇒↭

    ·↭-reflexive : _≡_ ⇒² _·↭_
    ·↭-reflexive refl = ·↭-refl _

    ·↭-isEquivalence : IsEquivalence _·↭_
    ·↭-isEquivalence = record {refl = ·↭-refl _; sym = ·↭-sym; trans = ·↭-trans}

    ·↭-setoid : Setoid _ _
    ·↭-setoid = record {isEquivalence = ·↭-isEquivalence}

    module ·↭-Reasoning where

      import Relation.Binary.Reasoning.Setoid as EqReasoning
      private module Base = EqReasoning ·↭-setoid

      open EqReasoning ·↭-setoid public
        hiding (step-≈; step-≈˘)

      infixr 2 step-↭  step-↭˘ step-swap step-prep

      step-↭  = Base.step-≈
      step-↭˘ = Base.step-≈˘

      -- Skip reasoning on the first element
      step-prep : ∀ x xs {ys zs : List A} → (x ∷ ys) IsRelatedTo zs →
                  xs ·↭ ys → (x ∷ xs) IsRelatedTo zs
      step-prep x xs rel xs↭ys = relTo (·↭-trans (·↭-prep x xs↭ys) (begin rel))

      -- Skip reasoning about the first two elements
      step-swap : ∀ x y xs {ys zs : List A} → (y ∷ x ∷ ys) IsRelatedTo zs →
                  xs ·↭ ys → (x ∷ y ∷ xs) IsRelatedTo zs
      step-swap x y xs rel xs↭ys = relTo (·↭-trans (·↭-swap x y xs↭ys) (begin rel))

      syntax step-↭  x y↭z x↭y = x ↭⟨  x↭y ⟩ y↭z
      syntax step-↭˘ x y↭z y↭x = x ↭˘⟨  y↭x ⟩ y↭z
      syntax step-prep x xs y↭z x↭y = x ∷ xs <⟨ x↭y ⟩ y↭z
      syntax step-swap x y xs y↭z x↭y = x ∷ y ∷ xs <<⟨ x↭y ⟩ y↭z

    ·↭-empty-inv : xs ·↭ [] → xs ≡ []
    ·↭-empty-inv = L.Perm.↭-empty-inv ∘ ·↭⇒↭

    ¬x∷xs·↭[] : ¬ ((x ∷ xs) ·↭ [])
    ¬x∷xs·↭[] {x}{xs} = L.Perm.¬x∷xs↭[] {x = x}{xs} ∘ ·↭⇒↭

    ·↭-singleton-inv : xs ·↭ L.[ x ] → xs ≡ L.[ x ]
    ·↭-singleton-inv = L.Perm.↭-singleton-inv ∘ ·↭⇒↭

    ·↭-sym-involutive : (p : xs ·↭ ys) → ·↭-sym (·↭-sym p) ≡ p
    ·↭-sym-involutive _ = ∀≡ _ _

module _ {A B : Type ℓ} ⦃ _ : DecEq B ⦄ (f : A → B) where

  ·↭-map⁺ : ∀ {xs ys} → xs ·↭ ys → map f xs ·↭ map f ys
  ·↭-map⁺ = ↭⇒·↭ ∘ L.Perm.map⁺ f ∘ ·↭⇒↭

  ∈-map-resp-·↭ : ∀ {xs ys} → xs ·↭ ys → map f xs ⊆ map f ys
  ∈-map-resp-·↭ {xs} p = ∈-resp-·↭ (·↭-map⁺ {xs} p)
