module Prelude.Monad where

open import Prelude.Init
import Reflection as R

Monad : (Set ℓ → Set ℓ) → Set (lsuc ℓ)
Monad {ℓ = ℓ} = RawMonad {f = ℓ}
open RawMonad ⦃ ... ⦄ public
  using (return; _>>=_; _>>_; _=<<_; _>=>_; _<=<_; join)
_≫=_ = _>>=_
_≫_  = _>>_
_=≪_ = _=<<_

instance
  Monad-Maybe : Monad {ℓ} Maybe
  Monad-Maybe = M.Cat.monad

  Monad-List : Monad {ℓ} List
  Monad-List = L.Cat.monad

  Monad-TC : Monad {ℓ} Meta.TC
  Monad-TC = record {return = R.return; _>>=_ = R.bindTC}

-- provides us with forward composition as _>=>_, but breaks instance-resolution/typeclass-inference
{-
Id : Set ℓ → Set ℓ
Id = id

instance
  Monad-Id : Monad {ℓ} Id
  Monad-Id .return = id
  Monad-Id ._>>=_ = _|>_
-}
