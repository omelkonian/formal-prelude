module Prelude.Main where

-- ** Re-exporting basic builtin/stdlib types
open import Prelude.Init

-- ** General properties of standard types
open import Prelude.General

-- ** List utilities
open import Prelude.Lists

-- ** Metaprogramming utilities
open import Prelude.Generics

-- ** Typeclasses
open import Prelude.Default
open import Prelude.ToN
open import Prelude.Show
open import Prelude.DecEq
open import Prelude.Measurable
open import Prelude.Collections

open import Prelude.Functor
open import Prelude.Bifunctor
open import Prelude.Applicative
open import Prelude.Monad
open import Prelude.Monoid

-- ** Sets as unique lists
open import Prelude.Set'

-- ** Unsafe operations
open import Prelude.Unsafe

-- ** Utilities for working with irrelevance
open import Prelude.Irrelevance
