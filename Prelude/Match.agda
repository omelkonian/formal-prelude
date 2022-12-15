{-# OPTIONS --with-K #-}
module Prelude.Match where

open import Prelude.Init
open Meta
open import Prelude.Generics
  hiding (`_; Hole)
open import Prelude.DecEq
open import Prelude.Applicative

Hole = Maybe
pattern ∗   = nothing
pattern ` x = just x

-- This typeclass connects types A with their "holed" variation A∗.
record _-matches-_ (A∗ : Set) (A : Set) : Set where
  field
    _~_ : A → A∗ → Bool

  _≁_ : A → A∗ → Bool
  x ≁ x∗ = not (x ~ x∗)
open _-matches-_ ⦃...⦄ public

match : ∀ {A : Set} ⦃ _ : DecEq A ⦄ → A → Maybe A → Bool
match a mx = M.fromMaybe true ⦇ pure a == mx ⦈

-- convert a function type `A → B → ⋯ → R` to `Maybe A → Maybe B → ‌⋯ → R`
macro
  holify : Term → Term → TC ⊤
  holify ty hole = unify hole (argumentWise toMaybe ty)
    where
      toMaybe : Type → Type
      toMaybe ty = quote Hole ∙⟦ ty ⟧

_ : holify (ℕ → ℕ → Bool) ≡ (Maybe ℕ → Maybe ℕ → Bool)
_ = refl

private

  data X : Set where
    mkX[_,_] : ℕ → String → X
  unquoteDecl DecEq-X = DERIVE DecEq [ quote X , DecEq-X ]

  -- we can of course check exact equality
  _ : T $ mkX[ 1 , "one" ] == mkX[ (0 + 1) , (Str.fromList $ 'o' ∷ 'n' ∷ 'e' ∷ []) ]
  _ = tt

  -- ... but we have to introduce a "holed" variant to model semi-equality
  data X∗ : Set where
    mkX[_,_] : holify (ℕ → String → X∗)
  unquoteDecl DecEq-X∗ = DERIVE DecEq [ quote X∗ , DecEq-X∗ ]

  -- and now we can connect them using `match`
  instance
    MatchX : X∗ -matches- X
    MatchX ._~_ mkX[ n , s ] mkX[ hn , hs ] = match n hn ∧ match s hs

  _ : T $ mkX[ 1 , "one" ] ~ mkX[ ` 1 , ∗ ]
  _ = tt

  _ : T $ mkX[ 1 , "one" ] ≁ mkX[ ` 2 , ∗ ]
  _ = tt
