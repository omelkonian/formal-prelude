{-# OPTIONS --safe #-}
module Prelude.Monad where

open import Prelude.Init; open SetAsType
open import Prelude.Functor
open import Prelude.Applicative
open import Prelude.General

{-
Monad : (Type ℓ → Type ℓ) → Type (lsuc ℓ)
Monad {ℓ = ℓ} = RawMonad {f = ℓ}
open RawMonad ⦃...⦄ public
  using (return; _>>=_; _>>_; _=<<_; _>=>_; _<=<_; join)
-}

private variable A : Type ℓ; B : Type ℓ′; C : Type ℓ″; M : Type↑

record Monad (M : Type↑) : Typeω where
  infixl 1 _>>=_ _>>_ _≫=_ _≫_ _>=>_
  infixr 1 _=<<_ _=≪_ _<=<_

  field
    overlap ⦃ super ⦄ : Applicative M
    return : A → M A
    _>>=_  : M A → (A → M B) → M B

  _>>_ : M A → M B → M B
  m₁ >> m₂ = m₁ >>= λ _ → m₂

  _=<<_ : (A → M B) → M A → M B
  f =<< c = c >>= f

  _≫=_ = _>>=_; _≫_  = _>>_; _=≪_ = _=<<_

  _>=>_ : (A → M B) → (B → M C) → (A → M C)
  f >=> g = _=<<_ g ∘ f

  _<=<_ : (B → M C) → (A → M B) → (A → M C)
  g <=< f = f >=> g

  join : M (M A) → M A
  join m = m >>= id
open Monad ⦃...⦄ public

record MonadLaws (M : Type↑) ⦃ _ : Monad M ⦄ : Typeω where
  field
    >>=-identityˡ : ∀ {A : Type ℓ} {B : Type ℓ′} {a : A} {h : A → M B} →
      (return a >>= h) ≡ h a
    >>=-identityʳ : ∀ {A : Type ℓ} (m : M A) →
      (m >>= return) ≡ m
    >>=-assoc : ∀ {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″} (m : M A) {g : A → M B} {h : B → M C} →
      ((m >>= g) >>= h) ≡ (m >>= (λ x → g x >>= h))
open MonadLaws ⦃...⦄ public

record Lawful-Monad (M : Type↑) : Typeω where
  field ⦃ isMonad ⦄ : Monad M
        ⦃ hasMonadLaws ⦄ : MonadLaws M
open Lawful-Monad ⦃...⦄ using () public
instance
  mkLawful-Monad : ⦃ _ : Monad M ⦄ → ⦃ MonadLaws M ⦄ → Lawful-Monad M
  mkLawful-Monad = record {}

record Monad′ (M : Type[ ℓ ↝ ℓ′ ]) : Type (lsuc ℓ ⊔ₗ ℓ′) where
  infixl 1 _>>=′_ _>>′_ _≫=′_ _≫′_ _>=>′_
  infixr 1 _=<<′_ _=≪′_ _<=<′_

  field
    return′ : A → M A
    _>>=′_  : M A → (A → M B) → M B

  _>>′_ : M A → M B → M B
  m₁ >>′ m₂ = m₁ >>=′ λ _ → m₂

  _=<<′_ : (A → M B) → M A → M B
  f =<<′ c = c >>=′ f

  _>=>′_ : (A → M B) → (B → M C) → (A → M C)
  f >=>′ g = _=<<′_ g ∘ f

  _<=<′_ : (B → M C) → (A → M B) → (A → M C)
  g <=<′ f = f >=>′ g

  _≫=′_ = _>>=′_; _≫′_ = _>>′_; _=≪′_ = _=<<′_

  -- join : M (M A) → M A
  -- join m = m >>= id

open Monad′ ⦃...⦄ public

record Monad₀ (M : Type↑) : Typeω where
  field ⦃ isMonad ⦄ : Monad M
        ⦃ isApplicative₀ ⦄ : Applicative₀ M
open Monad₀ ⦃...⦄ using () public
instance
  mkMonad₀ : ⦃ Monad M ⦄ → ⦃ Applicative₀ M ⦄ → Monad₀ M
  mkMonad₀ = record {}

record Monad⁺ (M : Type↑) : Typeω where
  field ⦃ isMonad ⦄ : Monad M
        ⦃ isAlternative ⦄ : Alternative M
open Monad⁺ ⦃...⦄ using () public
instance
  mkMonad⁺ : ⦃ Monad M ⦄ → ⦃ Alternative M ⦄ → Monad⁺ M
  mkMonad⁺ = record {}

instance
  Monad-Maybe : Monad Maybe
  Monad-Maybe = λ where
    .return → pure
    ._>>=_ m f → maybe f nothing m

  MonadLaws-Maybe : MonadLaws Maybe
  MonadLaws-Maybe = λ where
    .>>=-identityˡ → refl
    .>>=-identityʳ → λ where
      (just _) → refl
      nothing  → refl
    .>>=-assoc → λ where
      (just _) → refl
      nothing  → refl

  Monad-List : Monad List
  Monad-List = λ where
    .return → pure
    ._>>=_ → flip concatMap

  Monad-TC : Monad Meta.TC
  Monad-TC = record {R}
    where import Reflection as R using (return) renaming (bindTC to _>>=_)

{- ** Id monad: provides us with forward composition as _>=>_,
                but breaks instance-resolution/typeclass-inference
module IdMonad where
  Id : Type ℓ → Type ℓ
  Id = id

  Monad-Id : Monad Id
  Monad-Id .return = id
  Monad-Id ._>>=_ = _|>_
-}

-- ** monadic utilities
module _ ⦃ _ : Monad M ⦄ where
  mapM : (A → M B) → List A → M (List B)
  mapM f []       = return []
  mapM f (x ∷ xs) = ⦇ f x ∷ mapM f xs ⦈

  concatMapM : (A → M (List B)) → List A → M (List B)
  concatMapM f xs = concat <$> mapM f xs

  forM : List A → (A → M B) → M (List B)
  forM []       _ = return []
  forM (x ∷ xs) f = ⦇ f x ∷ forM xs f ⦈

  concatForM : List A → (A → M (List B)) → M (List B)
  concatForM xs f = concat <$> forM xs f

  return⊤ void : M A → M ⊤
  return⊤ k = k ≫ return tt
  void = return⊤

  filterM : (A → M Bool) → List A → M (List A)
  filterM _ [] = return []
  filterM p (x ∷ xs) = do
    b ← p x
    ((if b then [ x ] else []) ++_) <$> filterM p xs

  -- traverse : ∀ {A B : Type} {M : Type → Type} → ⦃ Applicative M ⦄ → ⦃ Monad M ⦄ → (A → M B) → List A → M (List B)
  -- traverse f = λ where
  --   [] → return []
  --   (x ∷ xs) → ⦇ f x ∷ traverse f xs ⦈

do-pure : ∀ {A : Type ℓ} {x : A} {mx : Maybe A} {f : A → Bool}
  → mx ≡ just x
  → f x ≡ true
  → M.fromMaybe false (mx >>= pure ∘ f) ≡ true
do-pure refl f≡ rewrite f≡ = refl

private
  _ : (return 5 >>= just) ≡ just 5
  _ = refl
  _ : (return 5 >>= just) ≡ just 5
  _ = >>=-identityʳ _

  _ : ⦃ _ : Lawful-Monad M ⦄ → (ℕ → M ℕ)
  _ = return

  _ : Lawful-Monad Maybe
  _ = itω
