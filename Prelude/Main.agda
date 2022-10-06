module Prelude.Main where

-- ** Ternary relations
open import Relation.Ternary

-- ** Re-exporting basic builtin/stdlib types
open import Prelude.Init

-- ** General properties of standard types
open import Prelude.General
open import Prelude.SubstDSL

-- ** Convenient syntax for inference rules
open import Prelude.InferenceRules

-- ** Metaprogramming utilities
open import Prelude.Generics
open import Prelude.Match

-- ** Decidability
open import Prelude.DecEq
open import Prelude.Decidable

-- ** Typeclasses
open import Prelude.Functor
open import Prelude.Bifunctor
open import Prelude.Pointed
open import Prelude.PointedFunctor
open import Prelude.Semigroup
open import Prelude.Monoid
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
open import Prelude.Indexable

open import Prelude.Orders
open import Prelude.Ord

open import Prelude.Setoid

open import Prelude.Collections
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

open import Prelude.Sets
open import Prelude.Sets.Example
open import Prelude.Sets.Concrete
open import Prelude.Sets.Concrete.Example
open import Prelude.Sets.Concrete.Extra
open import Prelude.Sets.Concrete.Abstract
open import Prelude.Sets.Concrete.Abstract.Example

open import Prelude.Maps
open import Prelude.Maps.Example
open import Prelude.Maps.Concrete
open import Prelude.Maps.Concrete.Example

-- ** Utilities for cryptography
open import Prelude.Serializable
open import Prelude.Bitstring
open import Prelude.SerializableBitstring

-- ** Unsafe operations
open import Prelude.Unsafe

-- ** Utilities for working with irrelevance
open import Prelude.Irrelevance

-- ** Tactics
open import Prelude.Tactics

-- ** Automatical solvers
open import Prelude.Solvers

-- ** Lenses
open import Prelude.Lenses
