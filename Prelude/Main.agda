module Prelude.Main where

-- ** Re-exporting basic builtin/stdlib types
open import Prelude.Init

-- ** General properties of standard types
open import Prelude.General

-- ** Metaprogramming utilities
open import Prelude.Generics
open import Prelude.Match

-- ** Decidability
open import Prelude.DecEq
open import Prelude.Decidable

-- ** Typeclasses
open import Prelude.Functor
open import Prelude.Bifunctor
open import Prelude.PointedFunctor
open import Prelude.Semigroup
open import Prelude.Monoid
open import Prelude.Foldable
open import Prelude.Applicative
open import Prelude.Traversable
open import Prelude.Monad

open import Prelude.Nary

open import Prelude.Default
open import Prelude.Show
open import Prelude.Measurable

open import Prelude.ToN
open import Prelude.ToList

open import Prelude.Orders
open import Prelude.Ord

open import Prelude.Setoid
open import Prelude.Equivalence

open import Prelude.Collections
open import Prelude.Membership

open import Prelude.Coercions

open import Prelude.Validity

-- ** Closures
open import Prelude.Closures
open import Prelude.Traces

-- ** Data structures
open import Prelude.Lists
open import Prelude.Sets
open import Prelude.Maps

-- ** Utilities for cryptography.
open import Prelude.Bitstring

-- ** Unsafe operations
open import Prelude.Unsafe

-- ** Utilities for working with irrelevance
open import Prelude.Irrelevance
