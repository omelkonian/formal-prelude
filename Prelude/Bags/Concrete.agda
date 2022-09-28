open import Prelude.Init
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

import Relation.Binary.Reasoning.Setoid as BinSetoid

module Prelude.Bags.Concrete {A : Set} ⦃ _ : DecEq A ⦄ where

-- ** basic definitions

-- Bags as lists with no duplicates and a counter for each element.
record Bag' : Set where
  constructor mkBag
  field list : List A
open Bag'
syntax Bag' {A = A} = Set⟨ A ⟩

private variable
  x x′ y y′ z z′ : A
  xs ys zs : List A
  Xs Ys Zs s s′ s″ : Bag'
  P : Pred A 0ℓ

-----------------------------------------------------------------------
-- Lifting from list predicates/relations to set predicates/relations.

private
  record Lift (F : Set → Set₁) : Set₁ where
    field ↑ : F (List A) → F Bag'
  open Lift ⦃...⦄

  instance
    Lift-Pred : Lift Pred₀
    Lift-Pred .↑ P = P ∘ list

    Lift-Rel : Lift Rel₀
    Lift-Rel .↑ _~_ = _~_ on list

-- e.g. All/Any predicates for sets
All' Any' : Pred₀ A → Pred₀ Bag'
All' = ↑ ∘ All
Any' = ↑ ∘ Any

-- infixr 8 _─_
-- infixr 7 _∩_
-- infixr 6 _∪_
infix 4 _∈ˢ_ _∉ˢ_ _∈ˢ?_ _∉ˢ?_

_∈ˢ_ _∉ˢ_ : A → Bag' → Set
o ∈ˢ xs = o ∈ list xs
o ∉ˢ xs = ¬ (o ∈ˢ xs)

_∈ˢ?_ : Decidable² _∈ˢ_
o ∈ˢ? xs = o ∈? list xs

_∉ˢ?_ : Decidable² _∉ˢ_
o ∉ˢ? xs = o ∉? list xs


-- _∷_∶-_ : (x : A) → (xs : Bag') → ¬ x ∈ˢ xs → Bag'
-- x ∷ (xs ⊣ p) ∶- x∉ = (x ∷ xs) ⊣ (L.All.¬Any⇒All¬ _ x∉ ∷ p)

-- _<$>_∶-_ : (f : A → A) → Bag' → (∀ {x y} → f x ≡ f y → x ≡ y) → Bag'
-- f <$> (xs ⊣ p) ∶- inj = map f xs ⊣ map⁺ inj p

filter′ : Decidable¹ P → Bag' → Bag'
filter′ P? (mkBag xs) = mkBag (filter P? xs)

count′ : ∀ {P : Pred A 0ℓ} → Decidable¹ P → Bag' → ℕ
count′ P? = count P? ∘ list

∅ : Bag'
∅ = mkBag []

singleton : A → Bag'
singleton a = mkBag [ a ]

singletonN : A × ℕ → Bag'
singletonN (a , n) = mkBag $ L.replicate n a

singleton∈ˢ : x′ ∈ˢ singleton x ↔ x′ ≡ x
singleton∈ˢ = (λ where (here refl) → refl) , (λ where refl → here refl)

-- _++_∶-_ : ∀ (s s′ : Bag') → Disjoint (list s) (list s′) → Bag'
-- (xs ⊣ pxs) ++ (ys ⊣ pys) ∶- dsj =
--   (xs ++ ys) ⊣ ++⁺ pxs pys dsj

-- _∪_ _∩_ _─_ : Op₂ Bag'
-- x ∪ y = x ++ y

-- x ─ y = filter′ (_∉ˢ? y) x
-- x ∩ y = filter′ (_∈ˢ? y) x
-- x ∪ y = x ++ (filter′ (_∉ˢ? x) y) ∶- disjoint-─ {xs = list x} {ys = list y}
--   where
--     disjoint-─ : Disjoint xs (filter (_∉? xs) ys)
--     disjoint-─ {xs = xs} {ys = ys} (x∈ , x∈ˢ)
--       = let _ , x∉ = ∈-filter⁻ (_∉? xs) {xs = ys} x∈ˢ
--         in  x∉ x∈

-- ⋃ : (A → Bag') → Bag' → Bag'
-- ⋃ f = foldr _∪_ ∅ ∘ map f ∘ list

-- -- ** relational properties
-- ∉∅ : ∀ x → ¬ x ∈ˢ ∅
-- ∉∅ _ ()

-- ∈-─⁻ : ∀ x xs ys → x ∈ˢ (xs ─ ys) → x ∈ˢ xs
-- ∈-─⁻ x xs ys x∈ = proj₁ (∈-filter⁻ (_∉ˢ? ys) x∈)

-- ∈-─⁺ : ∀ x xs ys → x ∈ˢ xs → ¬ x ∈ˢ ys → x ∈ˢ (xs ─ ys)
-- ∈-─⁺ x xs ys x∈ x∉ = ∈-filter⁺ ((_∉ˢ? ys)) x∈ x∉

-- ∈-∪⁻ : ∀ x xs ys → x ∈ˢ (xs ∪ ys) → x ∈ˢ xs ⊎ x ∈ˢ ys
-- ∈-∪⁻ x xs ys x∈ = map₂ (∈-─⁻ x ys xs) (∈-++⁻ {v = x} (list xs) {ys = list (ys ─ xs)} x∈)

-- ∈-∪⁺ˡ : ∀ x xs ys → x ∈ˢ xs → x ∈ˢ (xs ∪ ys)
-- ∈-∪⁺ˡ x xs ys x∈ = ∈-++⁺ˡ x∈

-- ∈-∪⁺ʳ : ∀ x xs ys → x ∈ˢ ys → x ∈ˢ (xs ∪ ys)
-- ∈-∪⁺ʳ x xs ys x∈ with x ∈ˢ? xs
-- ... | yes x∈ˢ = ∈-∪⁺ˡ x xs ys x∈ˢ
-- ... | no  x∉  = ∈-++⁺ʳ (list xs) (∈-filter⁺ (_∉ˢ? xs) x∈ x∉)

-- ∈-∩⁺ : ∀ x xs ys → x ∈ˢ xs → x ∈ˢ ys → x ∈ˢ (xs ∩ ys)
-- ∈-∩⁺ _ _ ys = ∈-filter⁺ ((_∈ˢ? ys))

-- ∈-∩⁻ : ∀ x xs ys → x ∈ˢ (xs ∩ ys) → (x ∈ˢ xs) × (x ∈ˢ ys)
-- ∈-∩⁻ _ xs ys = ∈-filter⁻ (_∈ˢ? ys) {xs = list xs}

-- ** derived operations
{-# TERMINATING #-}
_⊆ˢ_ _⊇ˢ_ _⊈ˢ_ _⊉ˢ_ : Rel Bag' _
-- s ⊆ˢ s′ = list s ⊆ list s′
(mkBag xs) ⊆ˢ (mkBag ys)
  with xs
... | [] = ⊤
... | x ∷ xs =
  let ♯x  = 1 + count (_≟ x) xs
      xs′ = filter (¬? ∘ (_≟ x)) xs
      ♯x′ = count (_≟ x) ys
      ys′ = filter (¬? ∘ (_≟ x)) ys
  in (♯x ≤ ♯x′)
   × (mkBag xs′ ⊆ˢ mkBag ys′)
s ⊇ˢ s′ = s′ ⊆ˢ s
s ⊈ˢ s′ = ¬ s ⊆ˢ s′
s ⊉ˢ s′ = ¬ s ⊇ˢ s′

-- _⊆?ˢ_ = Decidable² _⊆ˢ_ ∋ dec²

-- ⊆ˢ-trans : Transitive _⊆ˢ_
-- ⊆ˢ-trans ij ji = ji ∘ ij

-- ** algebraic properties
_≈ˢ_ : Rel₀ Bag'
s ≈ˢ s′ = (s ⊆ˢ s′) × (s′ ⊆ˢ s)

-- _≈?ˢ_ = Decidable² _≈ˢ_ ∋ dec²

≈ˢ-equiv : IsEquivalence _≈ˢ_
≈ˢ-equiv = record
  { refl  = {!λ where refl → ?!}
  ; sym   = {!!}
  ; trans = {!!}
  }
open IsEquivalence ≈ˢ-equiv renaming (refl to ≈ˢ-refl; sym to ≈ˢ-sym; trans to ≈ˢ-trans)

≈ˢ-setoid : Setoid 0ℓ 0ℓ
≈ˢ-setoid = record { Carrier = Bag'; _≈_ = _≈ˢ_; isEquivalence = ≈ˢ-equiv }

module ≈ˢ-Reasoning = BinSetoid ≈ˢ-setoid

open Alg _≈ˢ_

open import Prelude.Setoid
instance
  Setoid-Bag' : ISetoid Bag'
  Setoid-Bag' = λ where
    .relℓ → 0ℓ
    ._≈_  → _≈ˢ_

  SetoidLaws-Bag' : Setoid-Laws Bag'
  SetoidLaws-Bag' .isEquivalence = ≈ˢ-equiv

-- ≈ˢ⇒⊆ˢ : s ≈ˢ s′ → s ⊆ˢ s′
-- ≈ˢ⇒⊆ˢ = proj₁

-- ≈ˢ⇒⊆ˢ˘ : s ≈ˢ s′ → s′ ⊆ˢ s
-- ≈ˢ⇒⊆ˢ˘ = proj₂

-- ∅─-identityʳ : RightIdentity ∅ _─_
-- ∅─-identityʳ s rewrite L.filter-all (_∉? []) {xs = list s} All∉[] = ≈ˢ-refl {x = s}

-- ∅∪-identityˡ : LeftIdentity ∅ _∪_
-- ∅∪-identityˡ xs =
--   begin ∅ ∪ xs ≈⟨ ≈ˢ-refl {xs ─ ∅} ⟩
--         xs ─ ∅ ≈⟨ ∅─-identityʳ xs ⟩
--         xs ∎
--   where open ≈ˢ-Reasoning

-- ∩-comm : Commutative _∩_
-- ∩-comm s s′ = uncurry (∈-∩⁺ _ s′ s) ∘ Product.swap ∘ ∈-∩⁻ _ s s′
--             , uncurry (∈-∩⁺ _ s s′) ∘ Product.swap ∘ ∈-∩⁻ _ s′ s

-- ∪-∅ : (Xs ∪ Ys) ≈ˢ ∅ → (Xs ≈ˢ ∅) × (Ys ≈ˢ ∅)
-- ∪-∅ {Xs}{Ys} p = (≈ˢ⇒⊆ˢ {Xs ∪ Ys}{∅} p ∘ ∈-∪⁺ˡ _ Xs Ys , λ ())
--                , (≈ˢ⇒⊆ˢ {Xs ∪ Ys}{∅} p ∘ ∈-∪⁺ʳ _ Xs Ys , λ ())

-- ∪-∅ˡ : (Xs ∪ Ys) ≈ˢ ∅ → Xs ≈ˢ ∅
-- ∪-∅ˡ {Xs}{Ys} = proj₁ ∘ ∪-∅ {Xs}{Ys}

-- ∪-∅ʳ : (Xs ∪ Ys) ≈ˢ ∅ → Ys ≈ˢ ∅
-- ∪-∅ʳ {Xs}{Ys} = proj₂ ∘ ∪-∅ {Xs}{Ys}

-- ∪-∩ : ((Xs ∪ Ys) ∩ Zs) ≈ˢ ((Xs ∩ Zs) ∪ (Ys ∩ Zs))
-- ∪-∩ {Xs}{Ys}{Zs} =
--   (λ x∈ →
--   let x∈∪ , x∈Zs = ∈-∩⁻ _ (Xs ∪ Ys) Zs x∈
--   in  case ∈-∪⁻ _ Xs Ys x∈∪ of λ where
--         (inj₁ x∈Xs) → ∈-∪⁺ˡ _ (Xs ∩ Zs) (Ys ∩ Zs)
--                               (∈-∩⁺ _ Xs Zs x∈Xs x∈Zs)
--         (inj₂ x∈Ys) → ∈-∪⁺ʳ _ (Xs ∩ Zs) (Ys ∩ Zs)
--                               (∈-∩⁺ _ Ys Zs x∈Ys x∈Zs))
--   , (∈-∪⁻ _ (Xs ∩ Zs) (Ys ∩ Zs) >≡> λ where
--        (inj₁ x∈) → let x∈Xs , x∈Zs = ∈-∩⁻ _ Xs Zs x∈
--                    in ∈-∩⁺ _ (Xs ∪ Ys) Zs (∈-∪⁺ˡ _ Xs Ys x∈Xs) x∈Zs
--        (inj₂ x∈) → let x∈Ys , x∈Zs = ∈-∩⁻ _ Ys Zs x∈
--                    in ∈-∩⁺ _ (Xs ∪ Ys) Zs (∈-∪⁺ʳ _ Xs Ys x∈Ys) x∈Zs)

-- ** apartness
instance
  Apart-Bag' : Bag' // Bag'
  Apart-Bag' ._♯_ s s′ = ∀ {k} → ¬ (k ∈ˢ s × k ∈ˢ s′)

_♯?ˢ_ = Decidable² (_♯_ {A = Bag'}) ∋ dec²

-- ♯-comm : ∀ (x y : Bag') → x ♯ y → y ♯ x
-- ♯-comm x y = ≈ˢ-trans {i = y ∩ x}{j = x ∩ y}{k = ∅} (∩-comm y x)

-- ∈-∩⇒¬♯ : x ∈ˢ (Xs ∩ Ys) → ¬ (Xs ♯ Ys)
-- ∈-∩⇒¬♯ {Xs = Xs}{Ys} x∈ xs♯ys = contradict (≈ˢ⇒⊆ˢ {s = Xs ∩ Ys} {s′ = ∅} xs♯ys x∈)

-- ♯-skipˡ : ∀ xs ys (zs : Bag') → (xs ∪ ys) ♯ zs → ys ♯ zs
-- ♯-skipˡ xs ys zs p = ∪-∅ {xs ∩ zs}{ys ∩ zs}
--   (let open ≈ˢ-Reasoning in
--    begin
--     (xs ∩ zs) ∪ (ys ∩ zs)
--    ≈˘⟨ ∪-∩ {xs}{ys}{zs} ⟩
--     (xs ∪ ys) ∩ zs
--    ≈⟨ p ⟩
--      ∅
--    ∎)
--   .proj₂


-- ** list conversion
instance
  ToList-Bag' : ToList Bag' A
  ToList-Bag' .toList = list

  FromList-Bag' : FromList A Bag'
  FromList-Bag' .fromList = mkBag

∈ˢ-fromList : x ∈ xs ↔ x ∈ˢ fromList xs
∈ˢ-fromList = id , id

-- ** decidability of set equality
unquoteDecl DecEq-Bag' = DERIVE DecEq [ quote Bag' , DecEq-Bag' ]
instance
  Measurable-Set : Measurable Bag'
  Measurable-Set = record {∣_∣ = length ∘ list}

record Bag'⁺ : Set where
  constructor _⊣_
  field set   : Bag'
        .set⁺ : ∣ set ∣ > 0
syntax Bag'⁺ {A = A} = Bag⁺⟨ A ⟩

instance
  DecEq-Bag'⁺ : DecEq Bag'⁺
  DecEq-Bag'⁺ ._≟_ (s ⊣ _) (s′ ⊣ _) with s ≟ s′
  ... | yes refl = yes refl
  ... | no  ¬eq  = no λ where refl → ¬eq refl

mkSet⁺ : (s : Bag') ⦃ _ : True (∣ s ∣ >? 0) ⦄ → Bag'⁺
mkSet⁺ s ⦃ pr ⦄ = s ⊣ toWitness pr

fromList⁺ : (xs : List A) ⦃ _ : True (length xs >? 0) ⦄ → Bag'⁺
fromList⁺ = mkSet⁺ ∘ fromList

toList'⁺ : Bag'⁺ → List⁺ A
toList'⁺ (s ⊣ _) with x ∷ xs ← list s = x ∷ xs

instance
  Semigroup-Bag' : ⦃ Semigroup A ⦄ → Semigroup Bag'
  Semigroup-Bag' ._◇_ (mkBag xs) (mkBag ys) = mkBag (xs ◇ ys)

  SemigroupLaws-Bag' : ⦃ _ : Semigroup A ⦄ → SemigroupLaws Bag' _≈ˢ_
  SemigroupLaws-Bag' = record {◇-assocʳ = p; ◇-comm = q}
    where
      p : Associative (_◇_ {A = Bag'})
      p xs ys zs = ≈-reflexive $ cong mkBag $ L.++-assoc (list xs) (list ys) (list zs)

      q : Commutative (_◇_ {A = Bag'})
      q (mkBag []) (mkBag ys) rewrite L.++-identityʳ ys = ≈-refl
      q (mkBag (x ∷ xs)) (mkBag ys) = {!!}
