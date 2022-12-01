module Prelude.Main where

-- ** Ternary relations
open import Relation.Ternary

-- ** Re-exporting basic builtin/stdlib types
open import Prelude.Init

-- ** General properties of standard types
open import Prelude.General
open import Prelude.Lift
open import Prelude.SubstDSL
open import Prelude.Newtype

-- ** Convenient syntax for inference rules
open import Prelude.InferenceRules

-- ** Metaprogramming utilities
open import Prelude.Generics
open import Prelude.Match

-- ** Decidability
open import Prelude.DecEq
open import Prelude.Decidable

-- ** Utilities for working with irrelevance
open import Prelude.Irrelevance

-- ** Typeclasses
open import Prelude.ConjClass

open import Prelude.Functor
open import Prelude.Bifunctor
open import Prelude.Pointed
open import Prelude.PointedFunctor
open import Prelude.Semigroup
open import Prelude.PartialSemigroup
open import Prelude.Monoid
open import Prelude.PartialMonoid
open import Prelude.Group
open import Prelude.Foldable
open import Prelude.Applicative
open import Prelude.Traversable
open import Prelude.Monad

open import Prelude.Default
open import Prelude.Show
open import Prelude.Measurable

open import Prelude.ToN
open import Prelude.FromN
open import Prelude.ToList
open import Prelude.Enumerable
open import Prelude.InfEnumerable
open import Prelude.Indexable

open import Prelude.Allable
open import Prelude.Anyable

open import Prelude.Orders
open import Prelude.Ord
open import Prelude.Ord.Tests

open import Prelude.Setoid
open import Prelude.CongSetoid

open import Prelude.Membership
open import Prelude.Apartness

open import Prelude.Nary
open import Prelude.Coercions
open import Prelude.Validity
open import Prelude.Accessors
open import Prelude.Split
open import Prelude.Null

open import Prelude.Views

-- ** Closures
open import Prelude.Closures
open import Prelude.Traces

-- ** Data structures
open import Prelude.Lists
open import Prelude.Lists.Collections

open import Prelude.Sets
open import Prelude.Sets.Examples
open import Prelude.Sets.Collections

open import Prelude.Maps
open import Prelude.Maps.Examples

open import Prelude.Bags
open import Prelude.Bags.Examples

-- ** Utilities for cryptography
open import Prelude.Serializable
open import Prelude.Bitstring
open import Prelude.SerializableBitstring

-- ** Unsafe operations
open import Prelude.Unsafe

-- ** Tactics
open import Prelude.Tactics

-- ** Automatical solvers
open import Prelude.Solvers

-- ** Lenses
open import Prelude.Lenses
