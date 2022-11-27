module Prelude.Lists.Irrelevance where

import Data.List.Relation.Unary.AllPairs as AP

open import Prelude.Init; open SetAsType
open L.Perm hiding (↭-trans; ↭-refl)
open L.Mem
open import Prelude.General
open import Prelude.Irrelevance
open import Prelude.Apartness
open import Prelude.DecEq
open import Prelude.Functor
open import Prelude.InferenceRules
open import Prelude.Newtype

private variable
  A : Type ℓ; B : Type ℓ′
  x y : A; xs ys zs : List A
  p r : Level
  P : Pred A p; R : Rel A r

-- ** derived instances of irrelevance
instance
  ·-All : ⦃ ·¹ P ⦄ → ·¹ All P
  ·-All .∀≡ = L.All.irrelevant ∀≡

  ·-AllPairs : ⦃ ·² R ⦄ → ·¹ AllPairs R
  ·-AllPairs .∀≡ = AP.irrelevant ∀≡

-- ** irrelevant version of Data.List.Unary.Unique
private
  ·Distinct : Rel A _
  ·Distinct = ·¬_ ∘₂ _≡_

·Unique : Pred (List A) _
·Unique = AllPairs ·Distinct

private
  _ : · ·Unique xs
  _ = it

·Unique⇒Unique : ·Unique xs → Unique xs
·Unique⇒Unique = AP.map ·⊥⇒⊥

Unique⇒·Unique : Unique xs → ·Unique xs
Unique⇒·Unique = AP.map ⊥⇒·⊥

·Unique⇔Unique : ·Unique xs ↔ Unique xs
·Unique⇔Unique = ·Unique⇒Unique , Unique⇒·Unique

module _ {f : A → B} (f-inj : Injective≡ f) where
  ·Unique-map⁺ : ·Unique xs → ·Unique (map f xs)
  ·Unique-map⁺ = Unique⇒·Unique ∘ L.Uniq.map⁺ f-inj ∘ ·Unique⇒Unique

module _ (P? : Decidable¹ P) where
  ·Unique-filter⁺ : ·Unique xs → ·Unique (filter P? xs)
  ·Unique-filter⁺ = Unique⇒·Unique ∘ L.Uniq.filter⁺ P? ∘ ·Unique⇒Unique

·Unique-++⁺ : ·Unique xs → ·Unique ys → xs ♯ ys → ·Unique (xs ++ ys)
·Unique-++⁺ p q dis =
  Unique⇒·Unique $ L.Uniq.++⁺ (·Unique⇒Unique p) (·Unique⇒Unique q) dis

-- ** irrelevant version of Data.List.Relation.Binary.Permutation
module _ {A : Type ℓ} ⦃ _ : DecEq A ⦄ where
  removeFirst : A → List A → Maybe (List A)
  removeFirst _ [] = nothing
  removeFirst x (y ∷ ys) =
    if x == y then just ys
              else (y ∷_) <$> removeFirst x ys

  infix 3 _·↭_
  _·↭_ : Rel (List A) ℓ
  [] ·↭ ys = ys ≡ []
  (x ∷ xs) ·↭ ys =
    case removeFirst x ys of λ where
      nothing → ·⊥
      (just ys′) → xs ·↭ ys′

  ∀≡↭ : ∀ (xs ys : List A) (p q : xs ·↭ ys) → p ≡ q
  ∀≡↭ [] .[] refl refl = refl
  ∀≡↭ (x ∷ xs) ys p q
    with removeFirst x ys
  ... | nothing  = refl
  ... | just ys′ = ∀≡↭ xs ys′ p q

  -- ** breaks instance resolution (e.g. for ·Unique)
  -- instance
  --   ··↭ : ·² _·↭_
  --   ··↭ {xs} .∀≡ = ∀≡↭ xs _

  ·↭-prep : ∀ x → xs ·↭ ys → x ∷ xs ·↭ x ∷ ys
  ·↭-prep x rewrite ≟-refl x = id

  ·↭-drop-∷ : ∀ x → x ∷ xs ·↭ x ∷ ys → xs ·↭ ys
  ·↭-drop-∷ x rewrite ≟-refl x = id

  ·↭-refl : ∀ xs → xs ·↭ xs
  ·↭-refl [] = refl
  ·↭-refl (_ ∷ xs) = ·↭-prep _ (·↭-refl xs)

  ·↭-swap : ∀ x y → xs ·↭ ys → x ∷ y ∷ xs ·↭ y ∷ x ∷ ys
  ·↭-swap {ys = ys} x y p
    with x ≟ y
  ... | yes refl rewrite ≟-refl x = p
  ... | no _
    with removeFirst x ys
  ... | nothing  rewrite ≟-refl x | ≟-refl y = p
  ... | just ys′ rewrite ≟-refl x | ≟-refl y = p

  removeFirst↭ : ∀ x xs →
    maybe (λ xs′ → (x ∈ xs) × (xs ↭ x ∷ xs′))
          (x ∉ xs)
          (removeFirst x xs)
  removeFirst↭ x [] ()
  removeFirst↭ x (y ∷ ys)
    with x ≟ y
  removeFirst↭ x (y ∷ ys) | no x≢y
    with removeFirst x ys | removeFirst↭ x ys
  ... | nothing | x∉ = λ where
    (here x≡y) → x≢y x≡y
    (there x∈) → x∉ x∈
  ... | just ys′ | x∈ , ys↭
    = there x∈ , ↭-trans (↭-prep y ys↭) (↭-swap y x ↭-refl)
  removeFirst↭ x (.x ∷ ys) | yes refl
    = here refl , ↭-refl

  ·↭⇒↭ : xs ·↭ ys → xs ↭ ys
  ·↭⇒↭ {[]} refl = ↭-refl
  ·↭⇒↭ {x ∷ xs} {y ∷ ys} xs·↭
    with x ≟ y
  ... | yes refl = ↭-prep x (·↭⇒↭ xs·↭)
  ... | no  x≢y
    with removeFirst x ys | removeFirst↭ x ys
  ... | nothing  | x∉ys = ·⊥-elim xs·↭
  ... | just ys′ | x∈ys , ys↭ =
    ↭-trans {xs = x ∷ xs}{x ∷ y ∷ ys′}{y ∷ ys}
            (↭-prep x $ ·↭⇒↭ xs·↭)
    $ ↭-trans {xs = x ∷ y ∷ ys′}{y ∷ x ∷ ys′}{y ∷ ys}
            (↭-swap x y ↭-refl)
            (↭-prep y $ ↭-sym ys↭)

  Any-resp-·↭ : Any P Respects _·↭_
  Any-resp-·↭ = Any-resp-↭ ∘ ·↭⇒↭

  ∈-resp-·↭ : (x ∈_) Respects _·↭_
  ∈-resp-·↭ = ∈-resp-↭ ∘ ·↭⇒↭

  mutual
    ·↭-sym : xs ·↭ ys → ys ·↭ xs
    ·↭-sym {xs} = ↭⇒·↭ {ys = xs} ∘ ↭-sym ∘ ·↭⇒↭

    ·↭-trans : xs ·↭ ys → ys ·↭ zs → xs ·↭ zs
    ·↭-trans {xs} p q = ↭⇒·↭ $ ↭-trans {xs = xs} (·↭⇒↭ p) (·↭⇒↭ q)

    ↭⇒·↭ : xs ↭ ys → xs ·↭ ys
    ↭⇒·↭ {[]} p = ↭-empty-inv (↭-sym p)
    ↭⇒·↭ {xs = x ∷ xs} ↭-refl rewrite ≟-refl x = ·↭-refl xs
    ↭⇒·↭ (↭-prep _ p) = ·↭-prep _ (↭⇒·↭ p)
    ↭⇒·↭ (↭-swap _ _ p) = ·↭-swap _ _ (↭⇒·↭ p)
    ↭⇒·↭ {xs = x ∷ _} (↭-trans {xs = xs}{ys}{zs} xs↭ ↭zs)
      with removeFirst x ys | removeFirst↭ x ys
    ... | nothing  | x∉ys
        = ⊥-elim
        $ x∉ys $ ∈-resp-↭ xs↭ $ here refl
    ... | just ys′ | x∈ys , ys↭
      with removeFirst x zs | removeFirst↭ x zs
    ... | nothing | x∉zs
        = ⊥⇒·⊥ x∉zs
        $ ∈-resp-↭ ↭zs x∈ys
    ... | just zs′ | x∈zs , zs↭
        = ↭⇒·↭ $ drop-∷ {x = x}
        $ ↭-trans xs↭
        $ ↭-trans ↭zs zs↭

  removeFirst·↭ : ∀ x xs →
    maybe (λ xs′ → (x ∈ xs) × (xs ·↭ x ∷ xs′))
          (x ∉ xs)
          (removeFirst x xs)
  removeFirst·↭ x xs
    with removeFirst x xs | removeFirst↭ x xs
  ... | nothing  | x∉ = x∉
  ... | just xs′ | x∈ , xs↭ = x∈ , ↭⇒·↭ xs↭

  ·↭⇔↭ : xs ·↭ ys ↔ xs ↭ ys
  ·↭⇔↭ = ·↭⇒↭ , ↭⇒·↭

  ·↭-empty-inv : xs ·↭ [] → xs ≡ []
  ·↭-empty-inv = ↭-empty-inv ∘ ·↭⇒↭

  ¬x∷xs·↭[] : ¬ ((x ∷ xs) ·↭ [])
  ¬x∷xs·↭[] {x}{xs} = ¬x∷xs↭[] {x = x}{xs} ∘ ·↭⇒↭

  ·↭-singleton-inv : xs ·↭ [ x ] → xs ≡ [ x ]
  ·↭-singleton-inv = ↭-singleton-inv ∘ ·↭⇒↭

  -- ·↭-sym-involutive : (p : xs ·↭ ys) → ·↭-sym (·↭-sym p) ≡ p
  -- ·↭-sym-involutive p = {!!} -- ↭-sym-involutive

  All-resp-·↭ : All P Respects _·↭_
  All-resp-·↭ = All-resp-↭ ∘ ·↭⇒↭

  -- alternative inductive definition (better type inference)
  infix 3 _·↭′_
  data _·↭′_ : Rel (List A) ℓ where
    [] :
      ────────
      [] ·↭′ []

    _∷_ : ∀ x → let ys′ = removeFirst x ys in

      M.Any.Any (xs ·↭′_) ys′
      ───────────────────────────
      x ∷ xs ·↭′ ys

  ·↭⇒·↭′ :
    xs ·↭ ys
    ─────────
    xs ·↭′ ys
  ·↭⇒·↭′ {[]} {.[]} refl = []
  ·↭⇒·↭′ {x ∷ xs} {ys} p
    with removeFirst x ys in eq
  ... | nothing  = ·⊥-elim p
  ... | just ys′ =
   x ∷ subst (M.Any.Any $ xs ·↭′_) (sym eq)
             (M.Any.just $ ·↭⇒·↭′ p)

  ·↭′⇒·↭ :
    xs ·↭′ ys
    ─────────
    xs ·↭ ys
  ·↭′⇒·↭ {[]} {.[]} [] = refl
  ·↭′⇒·↭ {x ∷ xs} {ys} (.x ∷ p)
    with removeFirst x ys | p
  ... | just _ | M.Any.just p = ·↭′⇒·↭ p

  ∀≡↭′ : ∀ (xs ys : List A) (p q : xs ·↭′ ys) → p ≡ q
  ∀≡↭′ .[] .[] [] [] = refl
  ∀≡↭′ (x ∷ xs) _ (.x ∷ p) (.x ∷ q)
    rewrite M.Any.irrelevant (∀≡↭′ xs _) p q
    = refl

  instance
    ··↭′ : ·² _·↭′_
    ··↭′ .∀≡ = ∀≡↭′ _ _

  ·↭′-prep : ∀ x → xs ·↭′ ys → x ∷ xs ·↭′ x ∷ ys
  ·↭′-prep x = ·↭⇒·↭′ ∘ ·↭-prep x ∘ ·↭′⇒·↭

  ·↭′-drop-∷ : ∀ x → x ∷ xs ·↭′ x ∷ ys → xs ·↭′ ys
  ·↭′-drop-∷ x = ·↭⇒·↭′ ∘ ·↭-drop-∷ x ∘ ·↭′⇒·↭

  -- version using newtype (better type inference)
  infix 3 _·↭″_
  _·↭″_ : Rel (List A) ℓ
  _·↭″_ = newtype² _·↭_

  ∀≡↭″ : ∀ (xs ys : List A) (p q : xs ·↭″ ys) → p ≡ q
  ∀≡↭″ xs ys (mk p) (mk q) rewrite ∀≡↭ xs ys p q = refl

  instance
    ··↭″ : ·² _·↭″_
    ··↭″ {xs} .∀≡ = ∀≡↭″ xs _

  ·↭″-prep : ∀ x → xs ·↭″ ys → x ∷ xs ·↭″ x ∷ ys
  ·↭″-prep x = mk ∘ ·↭-prep x ∘ unmk

  ·↭″-drop-∷ : ∀ x → x ∷ xs ·↭″ x ∷ ys → xs ·↭″ ys
  ·↭″-drop-∷ x = mk ∘ ·↭-drop-∷ x ∘ unmk
