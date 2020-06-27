module Prelude.Applicative where

open import Prelude.Init

private
  variable
    ℓ : Level

Applicative : (Set ℓ → Set ℓ) → Set (lsuc ℓ)
Applicative {ℓ = ℓ} = RawApplicative {f = ℓ}
open RawApplicative {{...}} public
  renaming (_⊛_ to _<*>_)

instance
  Applicative-Maybe : Applicative {ℓ} Maybe
  Applicative-Maybe = M.Cat.applicative

  Applicative-List : Applicative {ℓ} List
  Applicative-List = L.Cat.applicative
