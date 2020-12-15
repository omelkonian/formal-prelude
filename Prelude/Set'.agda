------------------------------------------------------------------------
-- Sets as unique lists.
------------------------------------------------------------------------
open import Data.List.Properties using (filter-all)
open import Data.List.Membership.Propositional.Properties
  using (∈-filter⁻; ∈-filter⁺; ∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (index)
open import Data.List.Relation.Unary.All.Properties using (¬Any⇒All¬; All¬⇒¬Any)
open import Data.List.Relation.Unary.Unique.Propositional.Properties using (filter⁺; ++⁺; map⁺)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (∈-resp-↭; drop-∷; drop-mid)

open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Measurable
open import Prelude.Bifunctor
open import Prelude.Decidable

module Prelude.Set' {A : Set} {{_ : DecEq A}} where

-- Sets as lists with no duplicates.
record Set' : Set where
  constructor ⟨_⟩∶-_
  field
    list  : List A
    .uniq : Unique list
open Set' public

private
  variable
    x : A
    xs ys zs : List A
    Xs Ys Zs : Set'

-----------------------------------------------------------------------
-- Lifting from list predicates/relations to set predicates/relations.

record Lift (F : Set → Set₁) : Set₁ where
  field
    ↑ : F (List A) → F Set'
open Lift {{...}}

instance
  Lift-Pred : Lift Pred₀
  Lift-Pred .↑ P = P ∘ list

  Lift-Rel : Lift Rel₀
  Lift-Rel .↑ _~_ xs ys = list xs ~ list ys

-- e.g. All/Any predicates for sets
All' Any' : Pred₀ A → Pred₀ Set'
All' = ↑ ∘ All
Any' = ↑ ∘ Any

infix 4 _♯_ _⊆′_
_♯_  _⊆′_ : Rel₀ Set'
_♯_  = ↑ Disjoint
_⊆′_ = ↑ _⊆_

_♯?_ : Decidable² _♯_
xs ♯? ys = disjoint? (list xs) (list ys)

--------------------------------------------
-- Basics.

infix 4 _∈′_ _∉′_ _∈′?_ _∉′?_
_∈′_ _∉′_ : A → Set' → Set
o ∈′ ⟨ os ⟩∶- _ = o ∈ os
o ∉′ ⟨ os ⟩∶- _ = o ∉ os

_∈′?_ : Decidable² _∈′_
o ∈′? ⟨ os ⟩∶- _ = o ∈? os
_∉′?_ : Decidable² _∉′_
o ∉′? ⟨ os ⟩∶- _ = o ∉? os

_∷_∶-_ : (x : A) → (xs : Set') → x ∉′ xs → Set'
x ∷ (⟨ xs ⟩∶- p) ∶- x∉ = ⟨ x ∷ xs ⟩∶- (¬Any⇒All¬ _ x∉ ∷ p)

_<$>_∶-_ : (f : A → A) → Set' → (∀ {x y} → f x ≡ f y → x ≡ y) → Set'
f <$> (⟨ xs ⟩∶- p) ∶- inj = ⟨ map f xs ⟩∶- map⁺ inj p

filter′ : ∀ {P : Pred A 0ℓ} → Decidable¹ P → Set' → Set'
filter′ P? (⟨ xs ⟩∶- p) = ⟨ filter P? xs ⟩∶- filter⁺ P? p

_++_∶-_ : ∀ x y → x ♯ y → Set'
(⟨ xs ⟩∶- pxs) ++ (⟨ ys ⟩∶- pys) ∶- dsj =
  ⟨ xs ++ ys ⟩∶- ++⁺ pxs pys dsj

count′ : ∀ {P : Pred A 0ℓ} → Decidable¹ P → Set' → ℕ
count′ P? = count P? ∘ list

∅ : Set'
∅ = ⟨ [] ⟩∶- []

singleton : A → Set'
singleton a = ⟨ [ a ] ⟩∶- ([] ∷ [])

fromList : List A → Set'
fromList xs = ⟨ nub xs ⟩∶- (nub-unique {xs = xs})

infixr 5 _─_
infixr 4 _∪_ _∩_
_∪_ _∩_ _─_ : Set' → Set' → Set'
x ─ y = filter′ (_∉′? y) x
x ∩ y = filter′ (_∈′? y) x
x ∪ y = x ++ (filter′ (_∉′? x) y) ∶- disjoint-─ {xs = list x} {ys = list y}
  where
    disjoint-─ : Disjoint xs (filter (_∉? xs) ys)
    disjoint-─ {xs = xs} {ys = ys} (x∈ , x∈′)
      = let _ , x∉ = ∈-filter⁻ (_∉? xs) {xs = ys} x∈′
        in  x∉ x∈

⋃ : (A → Set') → Set' → Set'
⋃ f = foldr _∪_ ∅ ∘ map f ∘ list

------------------------------------------------------------------------------------------
-- Disjointness.


------------------------------------------------------------------------
-- Deletion/Non-membership.

_\\_ : List A → List A → List A
xs \\ [] = xs
xs \\ (x ∷ ys) with x ∈? xs
... | no _     = xs \\ ys
... | yes x∈xs = (remove xs (index x∈xs)) \\ ys

\\-left : [] ≡ [] \\ xs
\\-left {[]}     = refl
\\-left {x ∷ ys} with x ∈? []
... | no _ = \\-left {ys}
... | yes ()

\\-head : [] ≡ [ x ] \\ (x ∷ xs)
\\-head {x = x} {xs = xs} with x ∈? [ x ]
... | no ¬p = ⊥-elim (¬p (here refl))
... | yes p with index p
... | 0F = \\-left {xs = xs}
... | fsuc ()

\\-‼ : ∀ {i : Index xs}
     → [] ≡ [ xs ‼ i ] \\ xs
\\-‼ {xs = []} {()}
\\-‼ {xs = x ∷ xs} {0F} with x ∈? [ x ]
... | no ¬p = ⊥-elim (¬p (here refl))
... | yes (here relf) = \\-left {xs = xs}
... | yes (there ())
\\-‼ {xs = x ∷ xs} {fsuc i} with x ∈? [ xs ‼ i ]
... | no ¬p = \\-‼ {xs = xs} {i}
... | yes (here refl) = \\-left {xs = xs}
... | yes (there ())

------------------------------------------------------------------------
-- Permutation relation.

¬[]↭ : ¬ ([] ↭ x ∷ xs)
¬[]↭ (↭-trans {.[]} {[]}     {.(_ ∷ _)} []↭ []↭₁) = ¬[]↭ []↭₁
¬[]↭ (↭-trans {.[]} {x ∷ ys} {.(_ ∷ _)} []↭ []↭₁) = ¬[]↭ []↭

↭-remove : ∀ {x : A} {ys : List A} {x∈ys : x ∈ ys}
         → x ∷ remove ys (index x∈ys) ↭ ys
↭-remove {x} {.(x ∷ _)}       {here refl}          = ↭-refl
↭-remove {x} {(y ∷ x ∷ _)}    {there (here refl)}  = ↭-swap x y ↭-refl
↭-remove {x} {(x₁ ∷ x₂ ∷ ys)} {there (there x∈ys)} = ↭-trans h₁ h₂
  where
    ys′ : List A
    ys′ = remove ys (index x∈ys)

    h₁ : x ∷ x₁ ∷ x₂ ∷ ys′ ↭ x₁ ∷ x₂ ∷ x ∷ ys′
    h₁ = ↭-trans (↭-swap x x₁ ↭-refl) (↭-prep x₁ (↭-swap x x₂ ↭-refl))

    h₂ : x₁ ∷ x₂ ∷ x ∷ ys′ ↭ x₁ ∷ x₂ ∷ ys
    h₂ = ↭-prep x₁ (↭-prep x₂ ↭-remove)

↭-helper : ∀ {x∈ys : x ∈ ys}
         → xs ↭ remove ys (index x∈ys)
         → x ∷ xs ↭ ys
↭-helper {x} {xs} {ys} {x∈ys} h = ↭-trans (↭-prep x h) ↭-remove

↭-helper′ : ∀ {x∈ys : x ∈ ys}
         → x ∷ xs ↭ ys
         → xs ↭ remove ys (index x∈ys)
↭-helper′ {x} {.(x ∷ _)}       {xs} {here refl}          h = drop-∷ h
↭-helper′ {x} {(y ∷ x ∷ _)}    {xs} {there (here refl)}  h = drop-mid [] [ y ] h
↭-helper′ {x} {(x₁ ∷ x₂ ∷ ys)} {xs} {there (there x∈ys)} h = drop-∷ {x = x} (↭-trans h h′)
  where
    ys′ : List A
    ys′ = remove ys (index x∈ys)

    h‴ : ys ↭ x ∷ ys′
    h‴ = ↭-sym ↭-remove

    h″ : x₂ ∷ ys ↭ x ∷ x₂ ∷ ys′
    h″ = ↭-trans (↭-prep x₂ h‴) (↭-swap x₂ x ↭-refl)

    h′ : x₁ ∷ x₂ ∷ ys ↭ x ∷ x₁ ∷ x₂ ∷ ys′
    h′ = ↭-trans (↭-prep x₁ h″) (↭-swap x₁ x ↭-refl)

_↭?_ : (xs : List A) → (ys : List A) → Dec (xs ↭ ys)
[]       ↭? []       = yes ↭-refl
[]       ↭? (x ∷ ys) = no ¬[]↭
(x ∷ xs) ↭? ys       with x ∈? ys
... | no  x∉         = no λ x∷xs↭ → x∉ (∈-resp-↭ x∷xs↭ (here refl))
... | yes x∈         with xs ↭? remove ys (index x∈)
... | no ¬xs↭        = no (¬xs↭ ∘ ↭-helper′)
... | yes xs↭        = yes (↭-helper xs↭)


-----------------------------------------------------
-- Properties

≡-Set' : ∀ .{px : Unique xs} .{py : Unique ys}
       → xs ≡ ys
       → ⟨ xs ⟩∶- px ≡ ⟨ ys ⟩∶- py
≡-Set' refl = refl

All∉[] : All (_∉ []) ys
All∉[] {ys = []}     = []
All∉[] {ys = y ∷ ys} = (λ ()) ∷ All∉[] {ys = ys}

∅─-identityʳ : ∀ {xs} → (xs ─ ∅) ≡ xs
∅─-identityʳ = ≡-Set' $ filter-all _ All∉[]

∅∪-identityˡ : ∀ {xs} → (∅ ∪ xs) ≡ xs
∅∪-identityˡ {xs} rewrite ∅─-identityʳ {xs} = refl -- refl

∅─∅≡∅ : ∅ ─ ∅ ≡ ∅
∅─∅≡∅ = ∅─-identityʳ {∅}

unique-∈ : Unique (x ∷ xs) → x ∉ xs
unique-∈ {xs = []} u ()
unique-∈ {xs = x ∷ xs} ((x≢x ∷ _) ∷ _) (here refl) = x≢x refl
unique-∈ {xs = x ∷ xs} ((_ ∷ p) ∷ _)   (there x∈)  = All¬⇒¬Any p x∈

nub-from∘to : Unique xs → nub xs ≡ xs
nub-from∘to {[]}     _ = refl
nub-from∘to {x ∷ xs} u@(_ ∷ Uxs) with x ∈? xs
... | no  _    = cong (x ∷_) (nub-from∘to Uxs)
... | yes x∈xs = ⊥-elim (unique-∈ u x∈xs)

from↔to : Unique xs → list (fromList xs) ≡ xs
from↔to Uxs rewrite nub-from∘to Uxs = refl

postulate
  nub-⊆⁻ : nub xs ⊆ xs
  nub-⊆⁺ : xs ⊆ nub xs
  \\-⊆ : xs \\ ys ⊆ xs

∈-─ : ∀ {x xs ys}
  → x ∈′ (xs ─ ys)
  → x ∈′ xs
∈-─ {x} {xs} {ys} x∈ = proj₁ (∈-filter⁻ (_∉? list ys) x∈)

∈-∪⁻ : ∀ {x xs ys}
  → x ∈′ (xs ∪ ys)
  → x ∈′ xs ⊎ x ∈′ ys
∈-∪⁻ {x} {xs} {ys} x∈ = map₂ (∈-─ {x} {ys} {xs}) (∈-++⁻ {v = x} (list xs) {ys = list (ys ─ xs)} x∈)

∈-∪⁺ˡ : ∀ {x xs ys}
  → x ∈′ xs
  → x ∈′ (xs ∪ ys)
∈-∪⁺ˡ {x} {xs} {ys} x∈ = ∈-++⁺ˡ x∈

∈-∪⁺ʳ : ∀ {x xs ys}
  → x ∈′ ys
  → x ∈′ (xs ∪ ys)
∈-∪⁺ʳ {x} {xs} {ys} x∈ with x ∈′? xs
... | yes x∈′ = ∈-∪⁺ˡ {x}{xs}{ys} x∈′
... | no  x∉  = ∈-++⁺ʳ (list xs) (∈-filter⁺ (_∉′? xs) x∈ x∉)

∈-∪⁺ : ∀ {x xs ys}
  → (x ∈′ xs) ⊎ (x ∈′ ys)
  → x ∈′ (xs ∪ ys)
∈-∪⁺ {xs = xs}{ys} (inj₁ x∈) = ∈-∪⁺ˡ {xs = xs}{ys} x∈
∈-∪⁺ {xs = xs}{ys} (inj₂ x∈) = ∈-∪⁺ʳ {xs = xs}{ys} x∈

postulate
  ∈-∩⁺ : ∀ {x xs ys}
    → x ∈′ xs
    → x ∈′ ys
    → x ∈′ (xs ∩ ys)

  ∈-∩⁻ : ∀ {x xs ys}
    → x ∈′ (xs ∩ ys)
    → (x ∈′ xs) × (x ∈′ ys)

  ∈-∩⇒¬♯ : ∀ {x xs ys}
    → x ∈′ (xs ∩ ys)
    → ¬ (xs ♯ ys)

  ♯-skipˡ : ∀ {xs ys zs} → (xs ∪ ys) ♯ zs → ys ♯ zs
  ♯-skipʳ : ∀ {xs ys zs} → xs ♯ (ys ∪ zs) → xs ♯ zs

unique-nub-∈ : ∀ {x : A} {xs : List A}
  → Unique xs
  → (x ∈ nub xs) ≡ (x ∈ xs)
unique-nub-∈ uniq rewrite nub-from∘to uniq = refl

∈-nub⁻ : ∀ {x : A} {xs : List A}
  → x ∈ nub xs
  → x ∈ xs
∈-nub⁻ {x = x} {xs = x′ ∷ xs} x∈
  with x′ ∈? xs
... | yes _ = there (∈-nub⁻ x∈)
... | no ¬p
  with x∈
... | (here refl) = here refl
... | (there x∈′) = there (∈-nub⁻ x∈′)

∈-nub⁺ : ∀ {x : A} {xs : List A}
  → x ∈ xs
  → x ∈ nub xs
∈-nub⁺ {x = x} {xs = .x ∷ xs} (here refl)
  with x ∈? xs
... | yes x∈ = ∈-nub⁺ x∈
... | no  _  = here refl
∈-nub⁺ {x = x} {xs = x′ ∷ xs} (there x∈)
  with x′ ∈? xs
... | yes x∈′ = ∈-nub⁺ x∈
... | no  _   = there $ ∈-nub⁺ x∈


-- commutativity

postulate
  ∩-comm : ∀ {xs ys} → (xs ∩ ys) ≡ (ys ∩ xs)
  ∪-comm : ∀ {xs ys} → (xs ∪ ys) ≡ (ys ∪ xs)
  ♯-comm : ∀ {xs ys} → xs ♯ ys → ys ♯ xs

{-
cong' : ∀ {xs ys}
  → list xs ≡ list ys
  → xs ≡ ys
cong' refl = refl

-- ∩-comm {xs = ⟨ xs₀ ⟩∶- _} {ys = ⟨ ys ⟩∶- _}
--   with xs₀
-- ... | []
--   rewrite L.filter-none (_∈′? ∅) {xs = []} []
--        = subst (∅ ≡_) (cong' $ sym $ L.filter-none (_∈′? ∅) {xs = ys} (L.All.tabulate λ _ ())) refl
-- ... | x ∷ xs
--   with x ∈? ys
-- ... | yes x∈ = {!!}
-- ... | no  x∉ = {!!}

-- ∩-comm {xs = ⟨ [] ⟩∶- _} {ys = ⟨ ys ⟩∶- _}
--   rewrite L.filter-none (_∈′? ∅) {xs = []} []
--   = subst (∅ ≡_) (cong' $ sym $ L.filter-none (_∈′? ∅) {xs = ys} (L.All.tabulate λ _ ())) refl
-- ∩-comm {xs = ⟨ x ∷ xs ⟩∶- ._} {ys = ⟨ ys ⟩∶- ._}
--   with x ∈? ys | ys
-- ... | yes x∈ | _
--     -- rewrite L.filter-accept (_∈? ys) {xs = xs} x∈
--     = {!!}
-- ... | no  x∉ | _
--     -- rewrite L.filter-reject (_∈? ys′) {xs = xs} x∉
--     = {!!}
--
-- ♯-comm : ∀ {xs ys} → xs ♯ ys → ys ♯ xs
-- ♯-comm {xs}{ys} = {!sym!} -- subst (_≡ ∅) (∩-comm {xs}{ys})
-}


-----------------------------------------------------
-- Instances
instance
  Measurable-Set : Measurable Set'
  Measurable-Set = record {∣_∣ = length ∘ list}

  DecEq-Set : DecEq Set'
  DecEq-Set ._≟_ s s′
    with list s ≟ list s′
  ... | no ¬p    = no λ{ refl → ¬p refl }
  ... | yes refl = yes refl

  Dec-∈′ : (x ∈′ Ys) ⁇
  Dec-∈′ {x}{Ys} .dec = _∈′?_ x Ys

  Dec-♯ : (Xs ♯ Ys) ⁇
  Dec-♯ {Xs}{Ys} .dec = _♯?_ Xs Ys

-----------------------------------------------------
-- Syntactic sugar
syntax Set' {A = A} = Set⟨ A ⟩
