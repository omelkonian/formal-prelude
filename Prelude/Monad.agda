module Prelude.Monad where

open import Prelude.Init

private
  variable
    ℓ : Level

Monad : (Set ℓ → Set ℓ) → Set (lsuc ℓ)
Monad {ℓ = ℓ} = RawMonad {f = ℓ}
open RawMonad {{...}} public
  renaming (_⊛_ to _<*>_)

instance
  Monad-Maybe : Monad {ℓ} Maybe
  Monad-Maybe = M.Cat.monad

  Monad-List : Monad {ℓ} List
  Monad-List = L.Cat.monad

  Monad-TC : Monad {ℓ} Meta.TC
  Monad-TC = record {return = Meta.return; _>>=_ = Meta.bindTC}
