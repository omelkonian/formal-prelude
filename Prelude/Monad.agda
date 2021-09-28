module Prelude.Monad where

open import Prelude.Init
open import Prelude.Functor
open import Prelude.Applicative

{-
Monad : (Set ℓ → Set ℓ) → Set (lsuc ℓ)
Monad {ℓ = ℓ} = RawMonad {f = ℓ}
open RawMonad ⦃ ... ⦄ public
  using (return; _>>=_; _>>_; _=<<_; _>=>_; _<=<_; join)
-}

private variable A B C : Set ℓ; M : Set↑

record Monad (M : Set↑) : Setω where
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

record Monad′ (M : Set[ ℓ ↝ ℓ′ ]) : Set (lsuc ℓ ⊔ₗ ℓ′) where
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

record Monad₀ (M : Set↑) : Setω where
  field
    ⦃ super-Mon ⦄ : Monad M
    ⦃ super-Ap₀ ⦄ : Applicative₀ M
open Monad₀ ⦃...⦄ public

record Monad⁺ (M : Set↑) : Setω where
  field
    ⦃ super-Mon ⦄ : Monad M
    ⦃ super-Alt ⦄ : Alternative M
open Monad⁺ ⦃...⦄ public

instance
  Monad-Maybe : Monad Maybe
  Monad-Maybe = λ where
    .return → pure
    ._>>=_ m f → maybe f nothing m

  Monad-List : Monad List
  Monad-List = λ where
    .return → pure
    ._>>=_ → flip concatMap

  Monad-TC : Monad Meta.TC
  Monad-TC = record {R}
    where import Reflection as R using (return) renaming (bindTC to _>>=_)

-- provides us with forward composition as _>=>_, but breaks instance-resolution/typeclass-inference
{-
Id : Set ℓ → Set ℓ
Id = id

instance
  Monad-Id : Monad {ℓ} Id
  Monad-Id .return = id
  Monad-Id ._>>=_ = _|>_
-}

{- monadic utilities
-}
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

  -- traverse : ∀ {A B : Set} {M : Set → Set} → ⦃ Applicative M ⦄ → ⦃ Monad M ⦄ → (A → M B) → List A → M (List B)
  -- traverse f = λ where
  --   [] → return []
  --   (x ∷ xs) → ⦇ f x ∷ traverse f xs ⦈
