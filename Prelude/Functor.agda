module Prelude.Functor where

open import Prelude.Init

{-
Functor : (Set ℓ → Set ℓ) → Set (lsuc ℓ)
Functor {ℓ = ℓ} = RawFunctor {ℓ = ℓ} {ℓ′ = ℓ}
open RawFunctor ⦃ ... ⦄ public
-}

private variable A B : Set ℓ

record Functor (F : Set↑) : Setω where
  infixl 4 _<$>_ _<$_
  infixl 1 _<&>_

  field _<$>_ : (A → B) → F A → F B
  fmap = _<$>_

  _<$_ : A → F B → F A
  x <$ y = const x <$> y

  _<&>_ : F A → (A → B) → F B
  _<&>_ = flip _<$>_
open Functor ⦃...⦄ public

-- Id : Set↑
-- Id x = x

instance
  -- Functor-Id : Functor Id
  -- Functor-Id ._<$>_ f x = f x

  Functor-Maybe : Functor Maybe
  Functor-Maybe ._<$>_ = M.map

  Functor-List : Functor List
  Functor-List ._<$>_ = L.map

  Functor-List⁺ : Functor List⁺
  Functor-List⁺ ._<$>_ = L.NE.map

  Functor-Vec : ∀ {n} → Functor (flip Vec n)
  Functor-Vec ._<$>_ = V.map

  Functor-TC : Functor Meta.TC
  Functor-TC = record {R}
    where import Reflection.TypeChecking.Monad.Syntax as R

  Functor-Abs : Functor  Meta.Abs
  Functor-Abs = record {R}
    where import Reflection.Abstraction as R renaming (map to _<$>_)

  Functor-Arg : Functor Meta.Arg
  Functor-Arg = record {R}
    where import Reflection.Argument as R renaming (map to _<$>_)

  Functor-∃Vec : Functor (∃ ∘ Vec)
  Functor-∃Vec ._<$>_ f (_ , xs) = -, (f <$> xs)

private
  _ : fmap suc (just 0) ≡ just 1
  _ = refl

  _ : fmap suc (List ℕ ∋ 0 ∷ 1 ∷ 2 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ [])
  _ = refl

  _ : fmap suc (List⁺ ℕ ∋ 0 ∷ 1 ∷ 2 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ [])
  _ = refl

  _ : fmap suc (Vec ℕ 3 ∋ 0 ∷ 1 ∷ 2 ∷ []) ≡ (1 ∷ 2 ∷ 3 ∷ [])
  _ = refl

  _ : fmap suc (∃ (Vec ℕ) ∋ -, 0 ∷ 1 ∷ 2 ∷ []) ≡ (-, 1 ∷ 2 ∷ 3 ∷ [])
  _ = refl
