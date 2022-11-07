module Prelude.Functor where

open import Prelude.Init; open SetAsType

{-
Functor : (Type ℓ → Type ℓ) → Type (lsuc ℓ)
Functor {ℓ = ℓ} = RawFunctor {ℓ = ℓ} {ℓ′ = ℓ}
open RawFunctor ⦃ ... ⦄ public
-}

private variable
  a b c : Level
  A : Type a; B : Type b; C : Type c

record Functor (F : Type↑) : Typeω where
  infixl 4 _<$>_ _<$_
  infixl 1 _<&>_

  field _<$>_ : (A → B) → F A → F B
  fmap = _<$>_

  _<$_ : A → F B → F A
  x <$ y = const x <$> y

  _<&>_ : F A → (A → B) → F B
  _<&>_ = flip _<$>_
open Functor ⦃...⦄ public

record FunctorLaws (F : Type↑) ⦃ _ : Functor F ⦄ : Typeω where
  field
    -- preserves identity morphisms
    fmap-id : ∀ {A : Type a} (x : F A) →
      fmap id x ≡ x
    -- preserves composition of morphisms
    fmap-∘  : ∀ {A : Type a} {B : Type b} {C : Type c}
                {f : B → C} {g : A → B} (x : F A) →
      fmap (f ∘ g) x ≡ (fmap f ∘ fmap g) x
open FunctorLaws ⦃...⦄ public

-- Id : Type↑
-- Id x = x

instance
  -- Functor-Id : Functor Id
  -- Functor-Id ._<$>_ f x = f x

  Functor-Maybe : Functor Maybe
  Functor-Maybe ._<$>_ = M.map

  FunctorLaws-Maybe : FunctorLaws Maybe
  FunctorLaws-Maybe = λ where
    .fmap-id → λ where (just _) → refl; nothing → refl
    .fmap-∘  → λ where (just _) → refl; nothing → refl

  Functor-List : Functor List
  Functor-List ._<$>_ = L.map

  FunctorLaws-List : FunctorLaws List
  FunctorLaws-List = record {fmap-id = p; fmap-∘ = q}
    where
      p : ∀ {A : Type ℓ} (x : List A) → fmap id x ≡ x
      p = λ where
        [] → refl
        (x ∷ xs) → cong (x ∷_) (p xs)

      q : ∀ {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″} {f : B → C} {g : A → B} (x : List A) →
        fmap (f ∘ g) x ≡ (fmap f ∘ fmap g) x
      q {f = f}{g} = λ where
        [] → refl
        (x ∷ xs) → cong (f (g x) ∷_) (q xs)

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
