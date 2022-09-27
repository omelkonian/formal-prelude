module Prelude.Bitstring where

open import Data.Digit as D public using (Bit)

open import Prelude.Init
open Nat renaming (suc to 1+_)
open F using () renaming (suc to 1+_)
open import Prelude.DecEq
open import Prelude.Applicative
open import Prelude.Semigroup
open import Prelude.Nary
open import Prelude.Functor
open import Prelude.InferenceRules
open import Prelude.Measurable
open import Prelude.Monad
open import Prelude.ToN
open import Prelude.FromN

Bin⁺ : Set
Bin⁺ = List Bit

infix 8 _1#

data Bin : Set where
  0#  : Bin
  _1# : (bs : Bin⁺) → Bin
unquoteDecl DecEq-Bin = DERIVE DecEq [ quote Bin , DecEq-Bin ]

Bitstring = Bin

--

pattern 0b = 0F
pattern 1b = 1F
pattern ⊥b = 1+ 1+ ()

toBits : Bin → List Bit
toBits 0#      = [ 0b ]
toBits (bs 1#) = bs ++ [ 1b ]

instance
  Measurable-Bin : Measurable Bin
  Measurable-Bin .∣_∣ = length ∘ toBits

  Toℕ-Bin : Toℕ Bin
  Toℕ-Bin .toℕ = D.fromDigits ∘ toBits

fromBits : List Bit → Bin
fromBits []        = 0#
fromBits (b  ∷ bs) with fromBits bs
fromBits (b  ∷ bs) | bs′ 1# = (b ∷ bs′) 1#
fromBits (0b ∷ bs) | 0#     = 0#
fromBits (1b ∷ bs) | 0#     = [] 1#
fromBits (⊥b ∷ bs) | _

instance
  Semigroup-Bin : Semigroup Bin
  Semigroup-Bin ._◇_ b b′ = fromBits (toBits b ◇ toBits b′)

private
  pattern 2+_ n = 1+ 1+ n

  ntoBits′ : ℕ → ℕ → List Bit
  ntoBits′     0      _  = []
  ntoBits′     1      0  = 0b ∷ 1b ∷ []
  ntoBits′     1      1  = 1b ∷ []
  ntoBits′ (2+ k)     0  = 0b ∷ ntoBits′ (1+ k) k
  ntoBits′ (2+ k)     1  = 1b ∷ ntoBits′ (1+ k) (1+ k)
  ntoBits′ (1+ k) (2+ n) = ntoBits′ k n

  ntoBits : ℕ → List Bit
  ntoBits n = ntoBits′ n n

instance
  Fromℕ-Bin : Fromℕ Bin
  Fromℕ-Bin .fromℕ n = fromBits $ ntoBits n

postulate
  fromℕ-injective : Injective≡ (fromℕ {A = Bin})
  fromℕ∘toℕ : ∀ m → fromℕ {A = Bin} (toℕ m) ≡ m
  toℕ∘fromℕ : ∀ n → toℕ (fromℕ {A = Bin} n) ≡ n
  -- toℕ-fromℕ : ∀ bs n →
  --   toℕ bs ≡ n
  --   ════════════
  --   bs ≡ fromℕ n
