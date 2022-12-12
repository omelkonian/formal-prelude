module Prelude.Ord where

open import Prelude.Ord.Core public
open import Prelude.Ord.Dec public
open import Prelude.Ord.Irrelevant public

open import Prelude.Ord.MinMax public
open import Prelude.Ord.Sort public
open import Prelude.Ord.Iso public

open import Prelude.Ord.Instances public
open import Prelude.Ord.List public
open import Prelude.Ord.Sum public
-- T0D0: cannot export these without breaking instance resolution
open import Prelude.Ord.Product -- public
open import Prelude.Ord.Maybe -- public

open import Prelude.Ord.Derive public
