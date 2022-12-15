------------------------------------------------------------------------
-- Unsafe utilities (for Haskell primitives)
------------------------------------------------------------------------

{-# OPTIONS --with-K #-}
module Prelude.Unsafe where

open import Function.Definitions using (Injective)

open import Data.Char    using (toℕ; fromℕ)
open import Data.String  using (toList; fromList)

open import Relation.Binary.PropositionalEquality         using (_≡_)
open import Relation.Binary.PropositionalEquality.TrustMe using (trustMe)

fromℕ∘toℕ : ∀ c → fromℕ (toℕ c) ≡ c
fromℕ∘toℕ c = trustMe

toℕ∘fromℕ : ∀ c → toℕ (fromℕ c) ≡ c
toℕ∘fromℕ c = trustMe

fromList∘toList : ∀ s → fromList (toList s) ≡ s
fromList∘toList s = trustMe

toList∘fromList : ∀ cs → toList (fromList cs) ≡ cs
toList∘fromList s = trustMe
