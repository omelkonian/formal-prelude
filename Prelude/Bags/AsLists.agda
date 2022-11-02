open import Prelude.Init; open SetAsType
open L.Mem using (∈-filter⁻; ∈-filter⁺; ∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open L.Uniq using (filter⁺; ++⁺; map⁺)
open import Prelude.General
open import Prelude.Lists
open import Prelude.DecLists
open import Prelude.Membership
open import Prelude.DecEq
open import Prelude.Measurable
open import Prelude.Bifunctor
open import Prelude.Decidable
open import Prelude.Apartness
open import Prelude.Ord
open import Prelude.ToList
open import Prelude.FromList
open import Prelude.Semigroup
open import Prelude.InferenceRules
open import Prelude.Setoid

import Relation.Binary.Reasoning.Setoid as BinSetoid

module Prelude.Bags.AsLists {A : Type} ⦃ _ : DecEq A ⦄ where

-- ** basic definitions

-- Bags as lists with no duplicates and a counter for each element.
record Bag : Type where
  constructor mkBag
  field list : List A
open Bag
syntax Bag {A = A} = Set⟨ A ⟩

private variable
  x x′ y y′ z z′ : A
  xs ys zs : List A
  Xs Ys Zs s s′ s″ s₁ s₂ s₃ s₁₂ s₂₃ : Bag
  P : Pred A 0ℓ

-----------------------------------------------------------------------
-- Lifting from list predicates/relations to set predicates/relations.

private
  record Lift (F : Type → Type₁) : Type₁ where
    field ↑ : F (List A) → F Bag
  open Lift ⦃...⦄

  instance
    Lift-Pred : Lift Pred₀
    Lift-Pred .↑ P = P ∘ list

    Lift-Rel : Lift Rel₀
    Lift-Rel .↑ _~_ = _~_ on list

-- e.g. All/Any predicates for sets
All' Any' : Pred₀ A → Pred₀ Bag
All' = ↑ ∘ All
Any' = ↑ ∘ Any

infixr 8 _─_
infixr 6 _∪_
infix 4 _∈ˢ_ _∉ˢ_ _∈ˢ?_ _∉ˢ?_

_∈ˢ_ _∉ˢ_ : A → Bag → Type
o ∈ˢ xs = o ∈ list xs
o ∉ˢ xs = ¬ (o ∈ˢ xs)

_∈ˢ?_ : Decidable² _∈ˢ_
o ∈ˢ? xs = o ∈? list xs

_∉ˢ?_ : Decidable² _∉ˢ_
o ∉ˢ? xs = o ∉? list xs

filter′ : Decidable¹ P → Bag → Bag
filter′ P? (mkBag xs) = mkBag (filter P? xs)

count′ : ∀ {P : Pred A 0ℓ} → Decidable¹ P → Bag → ℕ
count′ P? = count P? ∘ list

∅ : Bag
∅ = mkBag []

singleton : A → Bag
singleton a = mkBag [ a ]

singletonN : A × ℕ → Bag
singletonN (a , n) = mkBag $ L.replicate n a

singleton∈ˢ : x′ ∈ˢ singleton x ↔ x′ ≡ x
singleton∈ˢ = (λ where (here refl) → refl) , (λ where refl → here refl)

_∪_ _─_ : Op₂ Bag
mkBag xs ∪ mkBag ys = mkBag (xs ◇ ys)
mkBag xs ─ mkBag ys = mkBag (xs ∸[bag] ys)


-- ∈-∪⁻ : ∀ x xs ys → x ∈ˢ (xs ∪ ys) → x ∈ˢ xs ⊎ x ∈ˢ ys
-- ∈-∪⁻ x xs ys x∈ = map₂ (∈-─⁻ x ys xs) (∈-++⁻ {v = x} (list xs) {ys = list (ys ─ xs)} x∈)

-- ∈-∪⁺ˡ : ∀ x xs ys → x ∈ˢ xs → x ∈ˢ (xs ∪ ys)
-- ∈-∪⁺ˡ x xs ys x∈ = ∈-++⁺ˡ x∈

-- ∈-∪⁺ʳ : ∀ x xs ys → x ∈ˢ ys → x ∈ˢ (xs ∪ ys)
-- ∈-∪⁺ʳ x xs ys x∈ with x ∈ˢ? xs
-- ... | yes x∈ˢ = ∈-∪⁺ˡ x xs ys x∈ˢ
-- ... | no  x∉  = ∈-++⁺ʳ (list xs) (∈-filter⁺ (_∉ˢ? xs) x∈ x∉)

-- ⋃ : (A → Bag) → Bag → Bag
-- ⋃ f = foldr _∪_ ∅ ∘ map f ∘ list

-- ** relational properties
∉∅ : ∀ x → ¬ x ∈ˢ ∅
∉∅ _ ()

-- ∈-─⁻ : ∀ x xs ys → x ∈ˢ (xs ─ ys) → x ∈ˢ xs
-- ∈-─⁻ x xs ys x∈ = proj₁ (∈-filter⁻ (_∉ˢ? ys) x∈)

-- ∈-─⁺ : ∀ x xs ys → x ∈ˢ xs → ¬ x ∈ˢ ys → x ∈ˢ (xs ─ ys)
-- ∈-─⁺ x xs ys x∈ x∉ = ∈-filter⁺ ((_∉ˢ? ys)) x∈ x∉

_⊆ˢ_ _⊇ˢ_ _⊈ˢ_ _⊉ˢ_ : Rel Bag _
_⊆ˢ_ = _⊆[bag]_ on list
s ⊇ˢ s′ = s′ ⊆ˢ s
s ⊈ˢ s′ = ¬ s ⊆ˢ s′
s ⊉ˢ s′ = ¬ s ⊇ˢ s′

-- ⊆ˢ-trans : Transitive _⊆ˢ_
-- ⊆ˢ-trans ij ji = ji ∘ ij

_≈ˢ_ : Rel₀ Bag
s ≈ˢ s′ = (s ⊆ˢ s′) × (s′ ⊆ˢ s)

_≈?ˢ_ = Decidable² _≈ˢ_ ∋ dec²

postulate ≈ˢ-equiv : IsEquivalence _≈ˢ_
-- ≈ˢ-equiv = record
--   { refl  = {!λ where refl → ?!}
--   ; sym   = {!!}
--   ; trans = {!!}
--   }
open IsEquivalence ≈ˢ-equiv public
  renaming (refl to ≈ˢ-refl; sym to ≈ˢ-sym; trans to ≈ˢ-trans)

≈ˢ-setoid : Setoid 0ℓ 0ℓ
≈ˢ-setoid = record { Carrier = Bag; _≈_ = _≈ˢ_; isEquivalence = ≈ˢ-equiv }

module ≈ˢ-Reasoning = BinSetoid ≈ˢ-setoid
open ≈ˢ-Reasoning
open Alg _≈ˢ_

instance
  Setoid-Bag : ISetoid Bag
  Setoid-Bag = λ where
    .relℓ → 0ℓ
    ._≈_  → _≈ˢ_

  SetoidLaws-Bag : Setoid-Laws Bag
  SetoidLaws-Bag .isEquivalence = ≈ˢ-equiv

  Semigroup-Bag : Semigroup Bag
  Semigroup-Bag ._◇_ = _∪_

∪-assocʳ : Associative _∪_
∪-assocʳ xs ys zs =
  ≈-reflexive $ cong mkBag $ L.++-assoc (list xs) (list ys) (list zs)

postulate ∪-comm : Commutative _∪_

instance
  SemigroupLaws-Bag : SemigroupLaws Bag _≈ˢ_
  SemigroupLaws-Bag = record {◇-assocʳ = ∪-assocʳ; ◇-comm = ∪-comm}

-- ** apartness
instance
  Apart-Bag : Bag // Bag
  Apart-Bag ._♯_ s s′ = ∀ {k} → ¬ (k ∈ˢ s × k ∈ˢ s′)

_♯?ˢ_ = Decidable² (_♯_ {A = Bag}) ∋ dec²

-- _[_↦_] : Bag → A → ℕ → Type
-- m [ k ↦ n ] = m ⁉ k ≡ n

♯-comm : s ♯ s′ → s′ ♯ s
♯-comm elim = elim ∘ Product.swap

⟨_◇_⟩≡_ : 3Rel₀ Bag
⟨ m ◇ m′ ⟩≡ m″ = (m ∪ m′) ≈ m″

◇≡-comm : Symmetric (⟨_◇_⟩≡ s)
◇≡-comm {s = s}{s₁}{s₂} ≈s = ≈-trans {i = s₂ ∪ s₁}{j = s₁ ∪ s₂}{k = s} (∪-comm s₂ s₁) ≈s

postulate
  ◇-congˡ :
    s₁ ≈ s₂
    ───────────────────
    (s₁ ◇ s₃) ≈ (s₂ ◇ s₃)

◇-congʳ : s₂ ≈ s₃ → (s₁ ◇ s₂) ≈ (s₁ ◇ s₃)
◇-congʳ {s₂}{s₃}{s₁} s₂≈s₃ =
  begin s₁ ◇ s₂ ≈⟨ ∪-comm s₁ s₂ ⟩
        s₂ ◇ s₁ ≈⟨ ◇-congˡ {s₂}{s₃} s₂≈s₃ ⟩
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

-- ** list conversion
instance
  ToList-Bag : ToList Bag A
  ToList-Bag .toList = list

  FromList-Bag : FromList A Bag
  FromList-Bag .fromList = mkBag

∈ˢ-fromList : x ∈ xs ↔ x ∈ˢ fromList xs
∈ˢ-fromList = id , id

-- ** decidability of set equality
unquoteDecl DecEq-Bag = DERIVE DecEq [ quote Bag , DecEq-Bag ]
instance
  Measurable-Set : Measurable Bag
  Measurable-Set = record {∣_∣ = length ∘ list}

record Bag⁺ : Type where
  constructor _⊣_
  field set   : Bag
        .set⁺ : ∣ set ∣ > 0
syntax Bag⁺ {A = A} = Bag⁺⟨ A ⟩

instance
  DecEq-Bag⁺ : DecEq Bag⁺
  DecEq-Bag⁺ ._≟_ (s ⊣ _) (s′ ⊣ _) with s ≟ s′
  ... | yes refl = yes refl
  ... | no  ¬eq  = no λ where refl → ¬eq refl

mkSet⁺ : (s : Bag) ⦃ _ : True (∣ s ∣ >? 0) ⦄ → Bag⁺
mkSet⁺ s ⦃ pr ⦄ = s ⊣ toWitness pr

fromList⁺ : (xs : List A) ⦃ _ : True (length xs >? 0) ⦄ → Bag⁺
fromList⁺ = mkSet⁺ ∘ fromList

toList'⁺ : Bag⁺ → List⁺ A
toList'⁺ (s ⊣ _) with x ∷ xs ← list s = x ∷ xs
