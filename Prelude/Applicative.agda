-- T0D0 add indexed version like stdlib
module Prelude.Applicative where

open import Prelude.Init; open SetAsType
open import Prelude.Functor

{-
Applicative : (Type ℓ → Type ℓ) → Type (lsuc ℓ)
Applicative {ℓ = ℓ} = RawApplicative {f = ℓ}
open RawApplicative ⦃ ... ⦄ public
  using (pure)
  renaming ( _⊛_ to _<*>_; _<⊛_ to _<*_ ; _⊛>_ to _*>_)
-}

private variable A B C : Type ℓ; M F : Type↑

record Applicative (F : Type↑) : Typeω where
  infixl 4 _<*>_ _⊛_ _<*_ _<⊛_ _*>_ _⊛>_
  infix  4 _⊗_

  field
    overlap ⦃ super ⦄ : Functor F
    pure : A → F A
    _<*>_  : F (A → B) → F A → F B
  _⊛_ = _<*>_

  _<*_ : F A → F B → F A
  x <* y = const <$> x ⊛ y

  _*>_ : F A → F B → F B
  x *> y = constᵣ <$> x ⊛ y

  _<⊛_ = _<*_; _⊛>_ = _*>_

  _⊗_ : F A → F B → F (A × B)
  x ⊗ y = (_,_) <$> x ⊛ y

  zipWithA : (A → B → C) → F A → F B → F C
  zipWithA f x y = f <$> x ⊛ y

  zipA : F A → F B → F (A × B)
  zipA = zipWithA _,_

open Applicative ⦃...⦄ public

-- record Applicative′ (F : Type ℓ → Type ℓ′) : Type (lsuc ℓ ⊔ₗ ℓ′) where
--   infixl 4 _<*>′_ _⊛′_ _<*′_ _<⊛′_ _*>′_ _⊛>′_
--   infix  4 _⊗′_

--   field
--     overlap ⦃ super ⦄ : Functor F
--     pure′ : A → F A
--     _<*>′_  : F (A → B) → F A → F B
--   _⊛′_ = _<*>′_

--   _<*′_ : F A → F B → F A
--   x <*′ y = const <$> x ⊛′ y

--   _*>′_ : F A → F B → F B
--   x *>′ y = constᵣ <$> x ⊛′ y

--   _<⊛′_ = _<*′_; _⊛>′_ = _*>′_

--   _⊗′_ : F A → F B → F (A × B)
--   x ⊗′ y = (_,_) <$> x ⊛′ y

--   zipWithA′ : (A → B → C) → F A → F B → F C
--   zipWithA′ f x y = f <$> x ⊛′ y

--   zipA′ : F A → F B → F (A × B)
--   zipA′ = zipWithA′ _,_

-- open Applicative′ ⦃...⦄ public

instance
  Applicative-Maybe : Applicative Maybe
  Applicative-Maybe = λ where
    .pure → just
    ._<*>_ → maybe fmap (const nothing)

  Applicative-List : Applicative List
  Applicative-List = λ where
    .pure → [_]
    ._<*>_ → flip $ concatMap ∘ _<&>_

  Applicative-List⁺ : Applicative List⁺
  Applicative-List⁺ = λ where
    .pure → [_]⁺
    ._<*>_ → flip $ L.NE.concatMap ∘ _<&>_

  Applicative-Vec : ∀ {n} → Applicative (flip Vec n)
  Applicative-Vec = λ where
    .pure → V.replicate
    ._<*>_ → V._⊛_

  Applicative-TC : Applicative Meta.TC
  Applicative-TC = record {R}
    where import Reflection.TypeChecking.Monad.Syntax as R

  -- Applicative-∃Vec : Applicative (∃ ∘ Vec)
  -- Applicative-∃Vec = λ where
  --   .pure x → 1 , pure x
  --   ._<*>_ (n , xs) (m , ys) → {! (n ⊔ m) , zipWith _$_ xs ys  -- (+ zipWith-⊔ lemma) !}

record Applicative₀ (F : Type↑) : Typeω where
  field
    overlap ⦃ super ⦄ : Applicative F
    ε₀ : F A
open Applicative₀ ⦃...⦄ public

instance
  Applicative₀-Maybe : Applicative₀ Maybe
  Applicative₀-Maybe .ε₀ = nothing

  Applicative₀-List : Applicative₀ List
  Applicative₀-List .ε₀ = []

  Applicative₀-Vec : Applicative₀ (flip Vec 0)
  Applicative₀-Vec .ε₀ = []


record Alternative (F : Type↑) : Typeω where
  infixr 3 _<|>_
  field _<|>_ : F A → F A → F A
    -- overlap ⦃ ap₀ ⦄ : Applicative₀ F

open Alternative ⦃...⦄ {- hiding (ap₀) -} public

infix -1 ⋃⁺_ ⋃_

⋃⁺_ : ⦃ Alternative F ⦄ → List⁺ (F A) → F A
⋃⁺_ = L.NE.foldr₁ _<|>_

⋃_ : ⦃ Applicative₀ F ⦄ → ⦃ Alternative F ⦄ → List (F A) → F A
⋃_ = foldr _<|>_ ε₀

instance
  Alternative-Maybe : Alternative Maybe
  Alternative-Maybe ._<|>_ = M._<∣>_

  Alternative-List : Alternative List
  Alternative-List ._<|>_ = _++_

  Alternative-TC : Alternative Meta.TC
  Alternative-TC ._<|>_ = M._<|>_
    where import Reflection.TypeChecking.Monad.Syntax as M
