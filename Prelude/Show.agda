module Prelude.Show where

open import Data.String using (_<+>_; parensIfSpace)

open import Prelude.Init
open import Prelude.General
open import Prelude.Lists
open import Prelude.Monoid
open import Prelude.ToN

open Meta hiding (module Show)

private variable A B : Set

record Show (A : Set) : Set where
  field show : A → String
open Show ⦃...⦄ public

private
  -- add appropriate parens depending on the given visibility
  visibilityParen : Visibility → String → String
  visibilityParen visible   s = parensIfSpace s
  visibilityParen hidden    s = braces s
  visibilityParen instance′ s = braces (braces s)

instance
  Show-⊤ : Show ⊤
  Show-⊤ .show tt = "tt"

  Show-Char : Show Char
  Show-Char .show = Ch.show

  Show-String : Show String
  Show-String .show x = x

  Show-Bool : Show Bool
  Show-Bool .show = B.show

  Show-ℕ : Show ℕ
  Show-ℕ .show = Nat.show

  Show-Fin : ∀ {n} → Show (Fin n)
  Show-Fin .show = ("# " ◇_) ∘ show ∘ toℕ

  Show-Float : Show Float
  Show-Float .show = Float.show

  Show-× : ⦃ Show A ⦄ → ⦃ Show B ⦄ → Show (A × B)
  Show-× .show (x , y) = parens $ show x <> " , " <> show y

  Show-List : ⦃ Show A ⦄ → Show (List A)
  Show-List .show = braces ∘ Str.intersperse ", " ∘ map show

  Show-Name : Show Name
  Show-Name .show = removeQualifiers ∘ showName

  Show-Meta : Show Meta
  Show-Meta .show = showMeta

  ShowLiteral : Show Literal
  ShowLiteral . show = λ where
    (nat x)    → show x
    (word64 x) → show (toℕ x)
    (float x)  → show x
    (char x)   → show x
    (string x) → show x
    (name x)   → show x
    (meta x)   → show x

  Show-Arg : ⦃ Show A ⦄ → Show (Arg A)
  Show-Arg .show = show ∘ unArg

  mutual
    {-# TERMINATING #-}
    Show-Term : Show Term
    Show-Term .show = λ where
      (var x args)         → "var" <+> show x <+> show args
      (con c args)         → show c <+> show args
      (def f args)         → show f <+> show args
      (lam v (abs s x))    → "λ" <+> visibilityParen v s <+> "→" <+> show x
      (pat-lam cs args)    → "λ {" <+> show cs <+> "}" <+> show args
      (Π[ x ∶ arg i a ] b) → "Π (" Str.++ visibilityParen (Meta.Argument.visibility i) x <+> ":"
                         <+> parensIfSpace (show a) Str.++ ")" <+> parensIfSpace (show b)
      (sort s)             → show s
      (lit l)              → show l
      (meta x args)        → show x <+> show args
      unknown              → "unknown"

    Show-Clause : Show Clause
    Show-Clause .show = λ where
      (clause ps t)      → show ps <+> "→" <+> show t
      (absurd-clause ps) → show ps

    Show-Sort : Show Sort
    Show-Sort .show = λ where
      (set t) → "Set" <+> parensIfSpace (show t)
      (lit n) → "Set" Str.++ show n -- no space to disambiguate from set t
      unknown → "unknown"

    ShowPattern : Show Pattern
    ShowPattern .show = λ where
      (Pattern.con c []) → show c
      (Pattern.con c ps) → parens (show c <+> show ps)
      Pattern.dot        → "._"
      (Pattern.var s)    → s
      (Pattern.lit l)    → show l
      (Pattern.proj f)   → show f
      Pattern.absurd     → "()"

  open import Reflection.Definition
  Show-Definition : Show Definition
  Show-Definition .show = λ where
    (function cs)       → "function" <+> braces (show cs)
    (data-type pars cs) → "datatype" <+> show pars <+> braces (intersperse ", " (map show cs))
    (record′ c fs)      → "record" <+> show c <+> braces (intersperse ", " (map (show ∘′ unArg) fs))
    (constructor′ d)    → "constructor" <+> show d
    axiom               → "axiom"
    primitive′          → "primitive"
