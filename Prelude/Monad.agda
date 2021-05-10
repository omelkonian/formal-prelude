module Prelude.Monad where

open import Prelude.Init
import Reflection as R

private variable ℓ : Level

Monad : (Set ℓ → Set ℓ) → Set (lsuc ℓ)
Monad {ℓ = ℓ} = RawMonad {f = ℓ}
open RawMonad ⦃ ... ⦄ public
  using (return; _>>=_; _>>_; _=<<_; _>=>_; _<=<_; join)

instance
  Monad-Maybe : Monad {ℓ} Maybe
  Monad-Maybe = M.Cat.monad

  Monad-List : Monad {ℓ} List
  Monad-List = L.Cat.monad

  Monad-TC : Monad {ℓ} Meta.TC
  Monad-TC = record {return = R.return; _>>=_ = R.bindTC}
