------------------------------------------------------------------------
-- General utilities
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Prelude.General where

open import Data.Nat.Properties

open import Prelude.Init hiding (_⊆_; _⊈_)
open SetAsType
open Nat.Ord

private variable
  A : Type ℓ₁
  B : Type ℓ₂
  x y x′ y′ : A
  xs ys : List A

-- ** Functions
infix -1 _`→`_ _↔_ _⇔_ _⊢_

_`→`_ : Op₂ Type
A `→` B = A → B

_↔_ : Type ℓ → Type ℓ′ → Type (ℓ ⊔ₗ ℓ′)
A ↔ B = (A → B) × (B → A)

_⇔_ : Type ℓ → Type ℓ′ → Type _
A ⇔ B = (A → B) × (B → A)

_⇀_ : Type ℓ → Type ℓ′ → Type _
A ⇀ B = A → Maybe B

id↔ : ∀ {A : Set ℓ} → A ↔ A
id↔ = id , id

IdFun : ∀ {A : Type ℓ} → Pred (A → A) ℓ
IdFun f = ∀ x → f x ≡ x

IdFun-fmap : ∀ {f : A → A} → IdFun f → IdFun (M.map f)
IdFun-fmap f≗id = λ where
  nothing  → refl
  (just x) → cong just $ f≗id x

module _ {A : Type ℓ} {B : Pred A ℓ′} where
  implicitly : (∀ {x} → B x) → (∀ x → B x)
  implicitly f x = f {x}

  explicitly : (∀ x → B x) → (∀ {x} → B x)
  explicitly f {x} = f x

  automatically : (∀ ⦃ x ⦄ → B x) → (∀ x → B x)
  automatically f x = f ⦃ x ⦄

  manually : (∀ x → B x) → (∀ ⦃ x ⦄ → B x)
  manually f ⦃ x ⦄ = f x

-- ** Products
module _ {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″} {D : Type ℓ‴} where
  map×-injective : ∀ {f : A → B} {g : C → D}
    → Injective≡ f → Injective≡ g
    → Injective≡ (Product.map f g)
  map×-injective inj-f inj-g {_ , _} {_ , _} eq
    with eqˡ , eqʳ ← Product.,-injective eq
    rewrite inj-f eqˡ | inj-g eqʳ = refl

-- ** Equality

≗-sym : ∀ {f g : A → B} → f ≗ g → g ≗ f
≗-sym eq x rewrite eq x = refl

open import Prelude.SubstDSL public

-- ** Predicates

_⊢_ : ∀ {A : Type ℓ} → (A → Type ℓ′) → (A → Type ℓ″) → Type _
P ⊢ Q = ∀ {x} → P x → Q x

_⊣⊢_ : ∀ {A : Type ℓ} → (A → Type ℓ′) → (A → Type ℓ″) → Type _
P ⊣⊢ Q = (P ⊢ Q) × (Q ⊢ P)

module ⊢-Reasoning where
  -- Reasoning newtype (for better type inference).
  record ℝ⟨_⊢_⟩ {A : Type ℓ} (P Q : Pred A ℓ′) : Type (ℓ ⊔ₗ ℓ′) where
    constructor mkℝ_
    field begin_ : P ⊢ Q
    infix -2 begin_
  open ℝ⟨_⊢_⟩ public
  infix  -2 mkℝ_
  infixr -1 _⊢⟨_⟩_ _≡⟨_⟩_ _≗⟨_⟩_ _≡˘⟨_⟩_ _≗˘⟨_⟩_ _≡⟨⟩_
  infix  0  _∎

  private variable Q R : Pred A ℓ

  _⊢⟨_⟩_ : ∀ P → P ⊢ Q → ℝ⟨ Q ⊢ R ⟩ → ℝ⟨ P ⊢ R ⟩
  P ⊢⟨ P⊢Q ⟩ (mkℝ Q⊢R) = mkℝ (Q⊢R ∘ P⊢Q)

  _≡⟨_⟩_ : ∀ P → P ≡ Q → ℝ⟨ Q ⊢ R ⟩ → ℝ⟨ P ⊢ R ⟩
  _ ≡⟨ refl ⟩ p = p

  _≡⟨⟩_ : ∀ P → ℝ⟨ P ⊢ Q ⟩ → ℝ⟨ P ⊢ Q ⟩
  _ ≡⟨⟩ p = p

  _≡˘⟨_⟩_ : ∀ P → Q ≡ P → ℝ⟨ Q ⊢ R ⟩ → ℝ⟨ P ⊢ R ⟩
  P ≡˘⟨ eq ⟩ PlQ = P ≡⟨ sym eq ⟩ PlQ

  _≗⟨_⟩_ : ∀ P → P ≗ Q → ℝ⟨ Q ⊢ R ⟩ → ℝ⟨ P ⊢ R ⟩
  _ ≗⟨ eq ⟩ (mkℝ QlR) = mkℝ (QlR ∘ subst id (eq _))

  _≗˘⟨_⟩_ : ∀ P → Q ≗ P → ℝ⟨ Q ⊢ R ⟩ → ℝ⟨ P ⊢ R ⟩
  P ≗˘⟨ eq ⟩ PlQ = P ≗⟨ ≗-sym eq ⟩ PlQ

  _∎ : ∀ (P : Pred A ℓ) → ℝ⟨ P ⊢ P ⟩
  _∎ _ = mkℝ id

-- ** Binary relations

_Respects˘_ : Rel A ℓ → Pred A ℓ′ → Type _
_~_ Respects˘ P = ∀ {x y} → x ~ y → P x → P y

infix 4 _∈²_ _∉²_

_∈²_ : A × A → Rel A ℓ → Type _
(x , y) ∈² P = P x y

_∉²_ : A × A → Rel A ℓ → Type _
xy ∉² P = ¬ xy ∈² P

∁² : Rel A ℓ → Rel A ℓ
∁² P = ¬_ ∘₂ P

infix 10 ⋃² ⋂²
infixr 7 _∩²_
infixr 6 _∪²_
infix  4 _≬²_

_∪²_ : Rel A ℓ → Rel A ℓ′ → Rel A _
(P ∪² Q) x y = P x y ⊎ Q x y

_∩²_ : Rel A ℓ → Rel A ℓ′ → Rel A _
(P ∩² Q) x y = P x y × Q x y

⋃² : (I : Type ℓ) → (I → Rel A ℓ′) → Rel A _
(⋃² I P) x y = Σ[ i ∈ I ] P i x y
syntax ⋃² I (λ i → P) = ⋃²[ i ∶ I ] P

⋂² : ∀ {i} (I : Type i) → (I → Rel A ℓ′) → Rel A _
(⋂² I P) x y = (i : I) → P i x y
syntax ⋂² I (λ i → P) = ⋂²[ i ∶ I ] P

_≬²_ : Rel A ℓ₁ → Rel A ℓ₂ → Type _
P ≬² Q = ∃ λ x → ∃ λ y → P x y × Q x y

module _
  {a a′ b b′ c c′ : Level}
  {A : Set a} {A′ : Set a′} {B : Set b} {B′ : Set b′} {C : Set c} {C′ : Set c′}
  where
  open Binary

  Tri-map : (A ↔ A′) → (B ↔ B′) → (C ↔ C′) → Tri A B C → Tri A′ B′ C′
  Tri-map (a→ , ←a) (b→ , ←b) (c→ , ←c) = λ where
    (tri< a ¬b ¬c) → tri< (a→ a) (¬b ∘ ←b) (¬c ∘ ←c)
    (tri≈ ¬a b ¬c) → tri≈ (¬a ∘ ←a) (b→ b) (¬c ∘ ←c)
    (tri> ¬a ¬b c) → tri> (¬a ∘ ←a) (¬b ∘ ←b) (c→ c)

-- ** N-ary tuples
_^_ : Type ℓ → ℕ → Type ℓ
A ^ 0     = A
A ^ suc n = A × (A ^ n)

-- ** Bools

private variable b : Bool

true⇒T : b ≡ true → T b
true⇒T refl = tt

T⇒true : T b → b ≡ true
T⇒true {true} tt = refl

false⇒¬T : b ≡ false → ¬ T b
false⇒¬T refl ()

¬T⇒false : ¬ T b → b ≡ false
¬T⇒false {false} p = refl
¬T⇒false {true}  p = ⊥-elim $ p tt

false⇒T∘not : b ≡ false → T (not b)
false⇒T∘not refl = tt

T∘not⇒false : T (not b) → b ≡ false
T∘not⇒false {false} tt = refl

T∘not⇒¬T : T (not b) → ¬ T b
T∘not⇒¬T = false⇒¬T ∘ T∘not⇒false

¬T⇒T∘not : ¬ T b → T (not b)
¬T⇒T∘not = false⇒T∘not ∘ ¬T⇒false

⊥-bool : ¬ ((b ≡ true) × (b ≡ false))
⊥-bool (refl , ())

T-∧ : ∀ {l r} → T (l ∧ r) → T l × T r
T-∧ {true} {true} _ = tt , tt

∧-falseˡ : ∀ {r} → ¬ (T (false ∧ r))
∧-falseˡ {r = true}  ()
∧-falseˡ {r = false} ()

∧-falseʳ : ∀ {l} → ¬ (T (l ∧ false))
∧-falseʳ {l = true}  ()
∧-falseʳ {l = false} ()

∧-falseʳ² : ∀ {x y} → ¬ (T (x ∧ (y ∧ false)))
∧-falseʳ² {x = true}  {y = true}  ()
∧-falseʳ² {x = true}  {y = false} ()
∧-falseʳ² {x = false} {y = true}  ()
∧-falseʳ² {x = false} {y = false} ()

infixr 6 _∧-×_
_∧-×_ : ∀ {x y}
  → x ≡ true
  → y ≡ true
  → x ∧ y ≡ true
refl ∧-× refl = refl

if-true : ∀ {t f : A}
  → b ≡ true
  → (if b then t else f) ≡ t
if-true refl = refl

if-false : ∀ {t f : A}
  → b ≡ false
  → (if b then t else f) ≡ f
if-false refl = refl

if-eta : ∀ (b : Bool) → (if b then true else false) ≡ b
if-eta = λ where
  true  → refl
  false → refl

if-same : ∀ (b : Bool) → (if b then x else x) ≡ x
if-same = λ where
  true  → refl
  false → refl

-- ** Deriving relations from more primitive ones.
module Derive-⊆-from-∈ {A : Type ℓ} {B : Type ℓ′} (_∈_ : A → B → Type ℓ″) where
  infix 4 _⊆_ _⊈_
  _⊆_ _⊈_ _⊇_ _⊉_ : Rel B _
  b ⊆ b′ = ∀ {a} → a ∈ b → a ∈ b′
  b ⊈ b′ = ¬ b ⊆ b′
  b ⊇ b′ = b′ ⊆ b
  b ⊉ b′ = ¬ b ⊇ b′

  ⊆-trans : Transitive _⊆_
  ⊆-trans ij jk = jk ∘ ij

  ⊇-trans : Transitive _⊇_
  ⊇-trans = flip ⊆-trans

-- ** Lists

[]-injective : L.[ x ] ≡ [ y ] → x ≡ y
[]-injective refl = refl

open L.Mem using (_∈_)

singleton→∈ : ∃[ ys ] (xs ≡ x ∷ ys) → x ∈ xs
singleton→∈ (_ , refl) = here refl

mapWith∈⁺ : ∀ {x xs} {f : ∀ {x : A} → x ∈ xs → B}
  → (x∈ : x ∈ xs)
  → ∃[ y ] ( (y ∈ L.Mem.mapWith∈ xs f) × (f {x} x∈ ≡ y) )
mapWith∈⁺ {x = x} {xs = []}      ()
mapWith∈⁺ {x = x} {xs = .x ∷ xs} (here refl) = (_ , here refl , refl)
mapWith∈⁺ {x = x} {xs = x′ ∷ xs} (there x∈) with mapWith∈⁺ x∈
... | y , y∈ , refl = y , there y∈ , refl

filter-singleton : ∀ {P : A → Type} {P? : Decidable¹ P} {px : P x}
  → P? x ≡ yes px
  → filter P? [ x ] ≡ [ x ]
filter-singleton {P? = P?} p rewrite p = refl

case-singleton : ∀ {x} {xs : List A} {f : A → B} {g : B}
  → xs ≡ [ x ]
  → (case xs of λ{ [ x′ ] → f x′
                 ; _      → g }) ≡ f x
case-singleton refl = refl

-- ** Singleton types
data Is {A : Type ℓ} : A → Type ℓ where
  ⟫_ : (x : A) → Is x
infix -100 ⟫_

-- NB: can be used to pattern match on module parameters
private module _ (n : ℕ) where
  f : (n ≡ 0) ⊎ (∃ λ n′ → n ≡ suc n′)
  f with ⟫ n
  ... | ⟫ 0     = inj₁ refl
  ... | ⟫ suc _ = inj₂ $ -, refl

-- ** Testing

-- single case
_ = ∃ (_≤ 3)
  ∋ 3 , ≤-refl

-- syntactic sugar for giving multiple terms of the same type
module MultiTest where
  -- only the first is actually returned, but all are type-checked
  _∋⋮_ : (A : Type ℓ) → List⁺ A → A
  _∋⋮_ _ (x ∷ _) = x
  pattern _⋮_ x xs = x L.NE.∷ xs
  pattern _⋮_ x xs = x ∷ xs
  pattern _⋮∅ x = x ∷ []
  infixl -10 _∋⋮_
  infixr -9  _⋮_
  infix  -8  _⋮∅

  _ = ∃ (_≤ 3)
   ∋⋮ 3 , ≤-refl
    ⋮ 2 , ≤-step ≤-refl
    ⋮ 1 , ≤-step (≤-step ≤-refl)
    ⋮ 0 , ≤-step (≤-step (≤-step ≤-refl))
    ⋮∅
