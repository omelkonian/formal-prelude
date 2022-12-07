open import Prelude.Init; open SetAsType
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.ToList
open import Prelude.FromList
open import Prelude.Orders
open import Prelude.Ord
open import Prelude.Irrelevance hiding (_─_)
open import Prelude.Lists.Count
open import Prelude.DecLists
open import Prelude.Setoid
open import Prelude.Semigroup
open import Prelude.Apartness
open import Prelude.InferenceRules
open import Prelude.Measurable

module Prelude.Bags.AsSortedLists
  {A : Type ℓ}
  ⦃ _ : DecEq A ⦄
  ⦃ _ : Ord A ⦄ ⦃ _ : OrdLaws A ⦄
  ⦃ _ : ·² _≤_ {A = A} ⦄
  where

Bag : Type _
Bag = Σ (List A) Sorted
syntax Bag {A = A} = Bag⟨ A ⟩

pattern ∅ = [] , []

private variable
  x x′ y y′ z z′ : A
  xs ys zs : List A
  Xs Ys Zs s s′ s″ s₁ s₂ s₃ s₁₂ s₂₃ : Bag
  P : Pred A 0ℓ

instance
  DecEq-Sorted : DecEq (Sorted xs)
  DecEq-Sorted = Irrelevant⇒DecEq ∀≡

  ToList-Bag : ToList Bag A
  ToList-Bag .toList = proj₁

  FromList-Bag : FromList A Bag
  FromList-Bag .fromList xs = sort xs , sort-↗ xs

  Measurable-Set : Measurable Bag
  Measurable-Set = record {∣_∣ = length ∘ toList}

-----------------------------------------------------------------------
-- Lifting from list predicates/relations to set predicates/relations.

private
  record Lift (F : ∀ {ℓ} → Type ℓ → (ℓ′ : Level) → Type (ℓ ⊔ₗ lsuc ℓ′)) : Typeω where
    field ↑ : F (List A) ℓ → F Bag ℓ
  open Lift ⦃...⦄

  instance
    Lift-Pred : Lift Pred
    Lift-Pred .↑ P = P ∘ toList

    Lift-Rel : Lift Rel
    Lift-Rel .↑ _~_ = _~_ on toList

-- e.g. All/Any predicates for sets
All' Any' : Pred A ℓ → Pred Bag ℓ
All' = ↑ ∘ All
Any' = ↑ ∘ Any

infixr 8 _─_
infixr 7 _∩_
infixr 6 _∪_

filter′ : Decidable¹ P → Bag → Bag
filter′ P? (xs , sorted-xs)
  = filter P? xs
  , Sorted-filter⁺ P? sorted-xs

count′ : ∀ {P : Pred A ℓ} → Decidable¹ P → Bag → ℕ
count′ P? = count P? ∘ toList

singleton : A → Bag
singleton a = [ a ] , [-]

mergeWith : Op₂ ℕ → Op₂ Bag
mergeWith _⊗_ (xs , p) (ys , _)
  = bag-mergeWith _⊗_ xs ys
  , Sorted-bag-mergeWith⁺ {ys = ys} _⊗_ p

_∪_ _∩_ _─_ : Op₂ Bag
_∪_ = mergeWith _+_
_∩_ = mergeWith min
_─_ = mergeWith _∸_

⋃ : (A → Bag) → Bag → Bag
⋃ f = foldr _∪_ ∅ ∘ map f ∘ toList

-- ** relational properties
_⊆ˢ_ _⊇ˢ_ _⊈ˢ_ _⊉ˢ_ : Rel Bag _
_⊆ˢ_ = _⊆[bag]_ on toList
s ⊇ˢ s′ = s′ ⊆ˢ s
s ⊈ˢ s′ = ¬ s ⊆ˢ s′
s ⊉ˢ s′ = ¬ s ⊇ˢ s′

⊆ˢ-trans : Transitive _⊆ˢ_
⊆ˢ-trans {i}{j}{k} p q = ⊆[bag]-trans {i = toList i}{toList j}{toList k} p q

_≈ˢ_ = Rel Bag _ ∋ _≡_
_≈?ˢ_ = Decidable² _≈ˢ_ ∋ dec²

≈ˢ-equiv : IsEquivalence _≈ˢ_
≈ˢ-equiv = PropEq.isEquivalence

open IsEquivalence ≈ˢ-equiv public
  renaming (refl to ≈ˢ-refl; sym to ≈ˢ-sym; trans to ≈ˢ-trans)

instance
  Setoid-Bag : ISetoid Bag
  Setoid-Bag = mkISetoid≡

  SetoidLaws-Bag : SetoidLaws Bag
  SetoidLaws-Bag = mkSetoidLaws≡

  Semigroup-Bag : Semigroup Bag
  Semigroup-Bag ._◇_ = _∪_

module ≈ˢ-Reasoning = ≈-Reasoning {A = Bag}
open ≈ˢ-Reasoning
open Alg _≈ˢ_

postulate
  ∪-assocʳ : Associative _∪_
  ∪-comm   : Commutative _∪_
  ∩-comm   : Commutative _∩_

instance
  SemigroupLaws-Bag : SemigroupLaws Bag
  SemigroupLaws-Bag = record {◇-assocʳ = ∪-assocʳ; ◇-comm = ∪-comm}

  Apart-Bag : Bag // Bag
  Apart-Bag ._♯_ s s′ = s ∩ s′ ≈ ∅

_♯?ˢ_ = Decidable² (_♯_ {A = Bag}) ∋ dec²

_[_↦_] : Bag → A → ℕ → Type
m [ k ↦ n ] = count′ (_≟ k) m ≡ n

♯-comm : s ♯ s′ → s′ ♯ s
♯-comm {s}{s′} = ≈-trans (∩-comm s′ s)

⟨_◇_⟩≡_ : 3Rel Bag _
⟨ m ◇ m′ ⟩≡ m″ = (m ∪ m′) ≈ m″

◇≡-comm : Symmetric (⟨_◇_⟩≡ s)
◇≡-comm {s = s}{s₁}{s₂} ≈s = ≈-trans {i = s₂ ∪ s₁}{j = s₁ ∪ s₂}{k = s} (∪-comm s₂ s₁) ≈s

⊆ˢ-◇ˡ : s ⊆ˢ (s ◇ s′)
⊆ˢ-◇ˡ {s}{s′} = ⊆[bag]-mergeWithˡ _+_ Nat.m⊔n≤m+n {toList s}{toList s′}

⊆ˢ-◇ʳ : s′ ⊆ˢ (s ◇ s′)
⊆ˢ-◇ʳ {s′}{s} = ⊆[bag]-mergeWithʳ _+_ Nat.m⊔n≤m+n {toList s}{toList s′}

postulate
  ─-congˡ :
    s ≈ s′
    ────────────────
    s ─ s″ ≈ s′ ─ s″
  ─-congʳ :
    s ≈ s′
    ────────────────
    s″ ─ s ≈ s″ ─ s′
  ◇-─-commute :
    s ⊆ˢ s₁
    ─────────────────────────────
    (s₁ ◇ s₂) ─ s ≈ (s₁ ─ s) ◇ s₂
  ◇-congˡ :
    s₁ ≈ s₂
    ─────────────────────
    (s₁ ◇ s₃) ≈ (s₂ ◇ s₃)

◇-congʳ : s₂ ≈ s₃ → (s₁ ◇ s₂) ≈ (s₁ ◇ s₃)
◇-congʳ {s₂}{s₃}{s₁} s₂≈s₃ =
  begin s₁ ◇ s₂ ≈⟨ ∪-comm s₁ s₂ ⟩
        s₂ ◇ s₁ ≈⟨ ◇-congˡ {s₂}{s₃}{s₁} s₂≈s₃ ⟩
        s₃ ◇ s₁ ≈⟨ ∪-comm s₃ s₁ ⟩
        s₁ ◇ s₃ ∎

◇≈-assocˡ :
  ∙ ⟨ s₁₂ ◇ s₃ ⟩≡ s
  ∙ ⟨ s₁ ◇ s₂  ⟩≡ s₁₂
    ───────────────────
    ⟨ s₁ ◇ (s₂ ◇ s₃) ⟩≡ s
◇≈-assocˡ {s₁₂}{s₃}{s}{s₁}{s₂} ≡s ≡s₁₂ =
  begin s₁ ◇ (s₂ ◇ s₃) ≈˘⟨ ◇-assocʳ s₁ s₂ s₃ ⟩
        (s₁ ◇ s₂) ◇ s₃ ≈⟨ ◇-congˡ {s₁ ◇ s₂}{s₁₂}{s₃} ≡s₁₂ ⟩
        s₁₂ ◇ s₃       ≈⟨ ≡s ⟩
        s              ∎

◇≈-assocʳ :
  ∙ ⟨ s₁ ◇ s₂₃ ⟩≡ s
  ∙ ⟨ s₂ ◇ s₃  ⟩≡ s₂₃
    ─────────────────────
    ⟨ (s₁ ◇ s₂) ◇ s₃ ⟩≡ s
◇≈-assocʳ {s₁}{s₂₃}{s}{s₂}{s₃} ≡s ≡s₂₃ =
  begin (s₁ ◇ s₂) ◇ s₃ ≈⟨ ◇-assocʳ s₁ s₂ s₃ ⟩
        s₁ ◇ (s₂ ◇ s₃) ≈⟨ ◇-congʳ {s₂ ◇ s₃}{s₂₃}{s₁} ≡s₂₃ ⟩
        s₁ ◇ s₂₃       ≈⟨ ≡s ⟩
        s              ∎

Bag⁺ = Σ₀ Bag λ s → ∣ s ∣ > 0
pattern _⊣⁺_ x y = _,₀_ x y
syntax Bag⁺ {A = A} = Bag⁺⟨ A ⟩

instance
  DecEq-Bag⁺ : DecEq Bag⁺
  DecEq-Bag⁺ ._≟_ (s ⊣⁺ _) (s′ ⊣⁺ _) with s ≟ s′
  ... | yes refl = yes refl
  ... | no  ¬eq  = no λ where refl → ¬eq refl

mkSet⁺ : (s : Bag) ⦃ _ : True (∣ s ∣ >? 0) ⦄ → Bag⁺
mkSet⁺ s ⦃ pr ⦄ = s ⊣⁺ toWitness pr

fromList⁺ : (xs : List A) ⦃ _ : True (length xs >? 0) ⦄ → Bag⁺
fromList⁺ xs ⦃ p ⦄ = mkSet⁺ (fromList xs)
  ⦃ fromWitness
  $ subst (_> 0)
          (sym $ L.Perm.↭-length $ sort-↭ xs)
          (toWitness p)
  ⦄

toList'⁺ : Bag⁺ → List⁺ A
toList'⁺ (s ⊣⁺ _) with x ∷ xs ← toList s = x ∷ xs
