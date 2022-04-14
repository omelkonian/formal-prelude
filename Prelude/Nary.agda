module Prelude.Nary where

open import Prelude.Init
open import Prelude.General
-- NB: re-export Semigroup/Pointed for convenience
open import Prelude.Semigroup public
open import Prelude.Pointed   public

⟦_⟧ : ∀ {n} {A : Set ℓ} {F : Set↑} ⦃ _ : Semigroup (F A) ⦄ ⦃ _ : Pointed F ⦄ → A ^ n → F A
⟦_⟧ {n = zero}  x        = point x
⟦_⟧ {n = suc n} (x , xs) = point x ◇ ⟦ xs ⟧

private
  _ : List ℕ
  _ = ⟦ 1 , 2 , 3 , 4 ⟧

  _ : List⁺ ℕ
  _ = ⟦ 1 , 2 , 3 , 4 ⟧

-- _ : ∃ (Vec ℕ)
-- _ = ⟦ 1 , 2 , 3 , 4 ⟧

module _ where
  open import Function.Nary.NonDependent
  open import Data.Product.Nary.NonDependent

  curry₃ = curryₙ 3
  curry₄ = curryₙ 4
  curry₅ = curryₙ 5

  uncurry₃ = uncurryₙ 3
  uncurry₄ = uncurryₙ 4
  uncurry₅ = uncurryₙ 5

  -- mapOn₁ = mapₙ 1
  -- mapOn₂ = mapₙ 2
  -- mapOn₃ = mapₙ 3
  -- mapOn₄ = mapₙ 4
  -- mapOn₅ = mapₙ 5

  private
    x : ℕ × String × ℕ
    x = 1 , "abc" , 2

    f : ℕ → String → ℕ → ℕ
    f x _ y = x + y

    _ : uncurry₃ f x ≡ 3
    _ = refl

    y : String × ℕ × ℕ × String
    y = "init" , 1 , 2 , "abc"

    -- projₙ : ∀ n {ls} {as : Sets n ls} k → Product n as → Projₙ as k
    select₃ : ∀ {n ls} → let n′ = 3 + n in
          ∀ {as : Sets n′ ls} → Product n′ as → Projₙ as 2F
    select₃ {n = n} = projₙ (3 + n) 2F

    _ : ℕ
    _ = projₙ 3 2F x
    -- _ = select₃ x + select₃ y
    -- [FEATURE] cannot infer implicit {n = 3}

-- [WORKAROUND] define ad-hoc typeclass

private variable A B C D R : Set

record Focus₁_⟪_⟫_ (A : Set) (B : Set) (C : Set) : Set where
  field
    focus₁ : A → B × C
  select₁ = proj₁ ∘ focus₁
  drop₁   = proj₂ ∘ focus₁
open Focus₁_⟪_⟫_ ⦃ ... ⦄ public

instance
  -- works for triplets
  N1 : Focus₁ (A × B) ⟪ A ⟫ B
  N1 .focus₁ (a , b) = a , b

  -- also works for n-tuples for n > 1
  -- N1⁺ : Focus₁ (A × B × C) ⟪ A ⟫ (B × C)
  -- N1⁺ .focus₁ (a , b , c) = a , (b , c)

private
  t₂ = ℕ × ℕ ∋ (1 , 2)
  t₃ = ℕ × ℕ × ℕ ∋ (1 , 2 , 3)
  t₄ = ℕ × ℕ × ℕ × ℕ ∋ (1 , 2 , 3 , 4)

  _ : (select₁ t₂ ≡ 1) × (drop₁ t₂ ≡ 2)
  _ = refl , refl

  _ : (select₁ t₃ ≡ 1) × (drop₁ t₃ ≡ (2 , 3))
  _ = refl , refl

  _ : (select₁ t₄ ≡ 1) × (drop₁ t₄ ≡ (2 , 3 , 4))
  _ = refl , refl

record Focus₂_⟪_⟫_ (A : Set) (B : Set) (C : Set) : Set where
  field
    focus₂ : A → B × C
  select₂ = proj₁ ∘ focus₂
  drop₂ = proj₂ ∘ focus₂
open Focus₂_⟪_⟫_ ⦃ ... ⦄ public

instance
  -- works for triplets
  N2 : Focus₂ (A × B) ⟪ B ⟫ A
  N2 .focus₂ (a , b) = b , a

  -- also works for n-tuples for n > 2
  N2⁺ : Focus₂ (A × B × C) ⟪ B ⟫ (A × C)
  N2⁺ .focus₂ (a , b , c) = b , (a , c)

private
  t₅ = ℕ × ℕ × ℕ × ℕ × ℕ ∋ (1 , 2 , 3 , 4 , 5)

  _ : select₂ t₂ ≡ 2 × (drop₂ t₂ ≡ 1)
  _ = refl , refl

  _ : (select₂ t₃ ≡ 2) × (drop₂ t₃ ≡ (1 , 3))
  _ = refl , refl

  _ : (select₂ t₄ ≡ 2) × (drop₂ t₄ ≡ (1 , 3 , 4))
  _ = refl , refl

  _ : (select₂ t₅ ≡ 2) × (drop₂ t₅ ≡ (1 , 3 , 4 , 5))
  _ = refl , refl

record Focus₃_⟪_⟫_ (A : Set) (B : Set) (C : Set) : Set where
  field
    focus₃ : A → B × C
  select₃ = proj₁ ∘ focus₃
  drop₃ = proj₂ ∘ focus₃
open Focus₃_⟪_⟫_ ⦃ ... ⦄ public

instance
  -- works for triplets
  N3 : Focus₃ (A × B × C) ⟪ C ⟫ (A × B)
  N3 .focus₃ (a , b , c) = c , (a , b)

  -- also works for n-tuples for n > 3
  N3⁺ : Focus₃ (A × B × C × D) ⟪ C ⟫ (A × B × D)
  N3⁺ .focus₃ (a , b , c , d) = c , (a , b , d)

private
  t₆ = ℕ × ℕ × ℕ × ℕ × ℕ × ℕ ∋ (1 , 2 , 3 , 4 , 5 , 6)

  _ : (select₃ t₃ ≡ 3) × (drop₃ t₃ ≡ (1 , 2))
  _ = refl , refl

  _ : (select₃ t₄ ≡ 3) × (drop₃ t₄ ≡ (1 , 2 , 4))
  _ = refl , refl

  _ : (select₃ t₅ ≡ 3) × (drop₃ t₅ ≡ (1 , 2 , 4 , 5))
  _ = refl , refl

  _ : (select₃ t₆ ≡ 3) × (drop₃ t₆ ≡ (1 , 2 , 4 , 5 , 6))
  _ = refl , refl

-- flipping
flip₀ : (A → B → R) → (B → A → R)
flip₀ = flip

flip₁ : (A → B → C → R) → (A → C → B → R)
flip₁ f = flip₀ ∘ f

flip₂ : (A → B → C → D → R) → (A → B → D → C → R)
flip₂ f = flip₁ ∘ f

private
  _ : flip₀ _∸_ 1 2 ≡ 1
  _ = refl

  _ : flip₀ (λ x y z → (x ∸ y) + z) 1 2 0 ≡ 1
  _ = refl

  _ : flip₁ (λ x y z → x + (y ∸ z)) 0 1 2 ≡ 1
  _ = refl

  _ : flip₁ (λ x y z w → x + (y ∸ z) + w) 0 1 2 0 ≡ 1
  _ = refl

  _ : flip₂ (λ x y z w → x + y + (z ∸ w)) 0 0 1 2 ≡ 1
  _ = refl
