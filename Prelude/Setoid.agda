{-# OPTIONS --safe #-}
module Prelude.Setoid where

open import Prelude.Setoid.Core public
open import Prelude.Setoid.Dec public
-- T0D0: cannot export these without breaking instance resolution
open import Prelude.Setoid.Maybe -- public
