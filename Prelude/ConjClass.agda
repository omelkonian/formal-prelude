-- ** Conjuctive classes: gather up different instances together
module Prelude.ConjClass where

open import Prelude.Init; open SetAsType

private variable A : Type ℓ; B : Type ℓ′

infixr -100 _⊗_
record _⊗_ (A : Type ℓ) (B : ⦃ A ⦄ → Type ℓ′) : Type (ℓ ⊔ₗ ℓ′) where
  field ⦃ ↜ ⦄ : A
  field ⦃ ↝ ⦄ : B
instance
  mk⊗ : ⦃ A ⦄ → ⦃ _ : B ⦄ → A ⊗ B
  mk⊗ = record {}
open _⊗_ ⦃...⦄ hiding (↜; ↝)

private
  record X (A : Type ℓ) : Type ℓ where
    field x : A
  open X ⦃...⦄
  record Y (A : Type ℓ) : Type ℓ where
    field
      overlap ⦃ super ⦄ : X A
      y : A
      x≡y : x ≡ y
  open Y ⦃...⦄
  record Y′ (A : Type ℓ) ⦃ _ : X A ⦄ : Type ℓ where
    field y′ : A
          x≡y′ : x ≡ y′
  open Y′ ⦃...⦄
  record Z (A : Type ℓ) : Type ℓ where
    field
      overlap ⦃ super ⦄ : X A
      z : A
      x≡z : x ≡ z
  open Z ⦃...⦄

  module _ ⦃ _ : Y A ⦄ ⦃ _ : Y′ A ⦄ ⦃ _ : Z A ⦄ where
    _ : ∃ λ x → ∃ (x ≡_)
    _ = x , y , x≡y
    _ : ∃ λ x → ∃ (x ≡_)
    _ = x , y′ , x≡y′
    _ : ∃ λ x → ∃ (x ≡_)
    _ = x , z , x≡z
  module _ ⦃ _ : Y A ⊗ Y′ A ⊗ Z A ⦄ where
    _ : ∃ λ x → ∃ (x ≡_)
    _ = x , y , x≡y
    _ : ∃ λ x → ∃ (x ≡_)
    _ = x , y′ , x≡y′
    _ : ∃ λ x → ∃ (x ≡_)
    _ = x , z , x≡z
  module _ ⦃ _ : Y A ⦄ ⦃ _ : Y′ A ⦄ ⦃ _ : Z A ⦄ where
    _ : X A
    _ = it
    _ : X A ⊗ Y A
    _ = it
    _ : X A ⊗ Z A
    _ = it
    _ : X A ⊗ Y′ A
    _ = it
    _ : Y A ⊗ Y′ A ⊗ Z A
    _ = it
    _ : X A ⊗ Y A ⊗ Z A
    _ = it
    _ : X A ⊗ Y′ A ⊗ Z A
    _ = it
    _ : X A ⊗ Y A ⊗ Y′ A ⊗ Z A
    _ = it

  -- ** problematic scenario: cannot define `Lawful` short-hands
  -- c.f. issue #6364
  record Semigroup (A : Type ℓ) : Type ℓ where
    field _◇_ : A → A → A
  open Semigroup ⦃...⦄

  record Semigroup-Laws (A : Type ℓ) ⦃ _ : Semigroup A ⦄ : Type ℓ where
    field ◇-assoc : ∀ {x y z : A} → (x ◇ y) ◇ z ≡ x ◇ (y ◇ z)
  open Semigroup-Laws ⦃...⦄

  Lawful-Semigroup : Type ℓ → Type ℓ
  Lawful-Semigroup A = Semigroup A ⊗ Semigroup-Laws A

  module _ {A : Type} ⦃ s : Semigroup A ⦄ ⦃ l : Semigroup-Laws A ⦄ where

    -- ** all of these work
    ✓ : Semigroup A ⊗ Semigroup-Laws A
    ✓ = it -- mk⊗ -- mk⊗ ⦃ s ⦄ ⦃ l ⦄

    -- ** the two types involved are definitionally equal :S
    _ : Lawful-Semigroup A ≡ (Semigroup A ⊗ Semigroup-Laws A)
    _ = refl

    -- ** none of these work
    -- ✖ : Lawful-Semigroup A
    -- ✖ = it
  {-
  No instance of type Lawful-Semigroup A was found in scope.
  when checking that the expression it has type Lawful-Semigroup A
  -}
    -- ✖ = mk⊗
  {-
  Cannot instantiate the metavariable _85 to solution
  Semigroup-Laws A since it contains the variable x
  which is not in scope of the metavariable
  when checking that the expression mk⊗ has type Lawful-Semigroup A
  -}
    -- ✖ = mk⊗ ⦃ s ⦄ ⦃ l ⦄
  {-
  s != x of type Semigroup A
  when checking that the expression mk⊗ ⦃ s ⦄ ⦃ l ⦄ has type
  Lawful-Semigroup A
  -}
    -- ✖ = {!!}
  --- Goal type in the above context context:
  -- ∙ [C-,]         Lawful-Semigroup A
  -- ∙ [C-u C-u C-,] Semigroup A ⊗ Semigroup-Laws A

    -- ** this suprisingly works!
    ✓✓ : Lawful-Semigroup A
    ✓✓ = record {}
