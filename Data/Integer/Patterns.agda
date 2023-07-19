------------------------------------------------------------------------
-- The Agda standard library
--
-- Patterns for Integer
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Integer.Patterns where

open import Data.Integer.Base using (+0; +[1+_]; -[1+_])

------------------------------------------------------------------------
-- Constants

pattern 0ℤ = +0
pattern 1ℤ = +[1+ 0 ]
pattern 2ℤ = +[1+ 1 ]
pattern 3ℤ = +[1+ 2 ]
pattern 4ℤ = +[1+ 3 ]
pattern 5ℤ = +[1+ 4 ]
pattern 6ℤ = +[1+ 5 ]
pattern 7ℤ = +[1+ 6 ]
pattern 8ℤ = +[1+ 7 ]
pattern 9ℤ = +[1+ 8 ]
pattern -1ℤ = -[1+ 0 ]
pattern -2ℤ = -[1+ 1 ]
pattern -3ℤ = -[1+ 2 ]
pattern -4ℤ = -[1+ 3 ]
pattern -5ℤ = -[1+ 4 ]
pattern -6ℤ = -[1+ 5 ]
pattern -7ℤ = -[1+ 6 ]
pattern -8ℤ = -[1+ 7 ]
pattern -9ℤ = -[1+ 8 ]
