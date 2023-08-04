{-# OPTIONS --safe #-}
module Prelude.Str where

open import Prelude.Init; open SetAsType
open import Prelude.FromList; open import Prelude.ToList
open import Prelude.Lists.Singletons

record FromStr (A : Type ℓ) : Type (lsuc ℓ) where
  field
    Constraint : Pred String ℓ
    fromStr    : (s : String) → ⦃ Constraint s ⦄ → A
open FromStr ⦃...⦄ public using (fromStr)
{-# BUILTIN FROMSTRING fromStr #-}
{-# DISPLAY FromStr.fromStr _ n = fromStr n #-}

open FromStr using (Constraint)

private variable A : Set; x : A; xs : List A

instance
  FromStr-String : FromStr String
  FromStr-String = λ where
    .Constraint _ → ⊤
    .fromStr    s → s

  FromStr-Char : FromStr Char
  FromStr-Char .Constraint = Singleton ∘ toList
  FromStr-Char .fromStr s with [ c ] ← toList s = c

_ = String ∋ "sth"
_ = Char   ∋ "s"
