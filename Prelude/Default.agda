------------------------------------------------------------------------
-- Typeclass for types with default values.
------------------------------------------------------------------------

module Prelude.Default where

open import Function using (const)

open import Data.Unit     using (⊤; tt)
open import Data.Product  using (_×_; _,_)
open import Data.Sum      using (_⊎_; inj₁)
open import Data.Maybe    using (Maybe; nothing)
open import Data.Bool     using (Bool; true)
open import Data.Nat      using (ℕ; zero; suc)
open import Data.Integer  using (ℤ)
open import Data.Fin      using (Fin) renaming (zero to fzero)
open import Data.List     using (List; [])

record Default (A : Set) : Set where
  constructor ⌞_⌟
  field
    def : A
open Default {{...}} public

instance
  Default-⊤ : Default ⊤
  Default-⊤ = ⌞ tt ⌟

  Default-× : ∀ {A B : Set} {{_ : Default A}} → {{_ : Default B}} → Default (A × B)
  Default-× = ⌞ def , def ⌟

  Default-⊎ : ∀ {A B : Set} {{_ : Default A}} → Default (A ⊎ B)
  Default-⊎ = ⌞ inj₁ def ⌟

  Default-Maybe : ∀ {A : Set} → Default (Maybe A)
  Default-Maybe = ⌞ nothing ⌟

  Default-Bool : Default Bool
  Default-Bool = ⌞ true ⌟

  Default-ℕ : Default ℕ
  Default-ℕ = ⌞ zero ⌟

  Default-ℤ : Default ℤ
  Default-ℤ = ⌞ ℤ.pos def ⌟

  Default-Fin : ∀ {n : ℕ} → Default (Fin (suc n))
  Default-Fin = ⌞ fzero ⌟

  Default-List : ∀ {A : Set} → Default (List A)
  Default-List = ⌞ [] ⌟

  Default-→ : ∀ {A B : Set} {{_ : Default B}} → Default (A → B)
  Default-→ = ⌞ const def ⌟
