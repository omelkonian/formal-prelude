{-# OPTIONS --with-K #-}
open import Prelude.Init; open SetAsType

module Prelude.Maps {K V : Type} where

open import
  -- ** pick implementation to export
  -- Prelude.Maps.AsPartialFunctions
  Prelude.Maps.AsSets
    {K = K} {V = V}
  public
