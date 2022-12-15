-- {-# OPTIONS --safe #-}
module Prelude.Show where

open import Data.String using (_<+>_; parensIfSpace)

open import Prelude.Init
open import Prelude.General
open import Prelude.Bifunctor
open import Prelude.Semigroup
open import Prelude.Monoid
open import Prelude.ToN

open Meta hiding (module Show)

record Show (A : Set ℓ) : Set ℓ where
  field show : A → String
open Show ⦃...⦄ public

private
  -- add appropriate parens depending on the given visibility
  visibilityParen : Visibility → String → String
  visibilityParen visible   s = parensIfSpace s
  visibilityParen hidden    s = braces s
  visibilityParen instance′ s = braces (braces s)

private variable A : Set ℓ; B : Set ℓ′

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

  Show-Maybe : ⦃ Show A ⦄ → Show (Maybe A)
  Show-Maybe .show = λ where
    nothing → "nothing"
    (just x) → "just " ◇ show x

  {-# TERMINATING #-}
  Show-Name : Show Name
  Show-Name .show = removeQualifiers ∘ showName
    where
      String∗ = List Char

      apply∗ : (String∗ → String∗) → (String → String)
      apply∗ f = Str.fromList ∘ f ∘ Str.toList

      words∗ : String∗ → List (String∗ × String∗)
      words∗ [] = []
      words∗ s  =
        let
          ws , s′ = L.span (T? ∘ Ch.isSpace) s
          w , s″ = L.span (T? ∘ not ∘ Ch.isSpace) s′
        in
          (ws , w) ∷ words∗ s″
      words = map (map₁₂ Str.fromList) ∘ words∗ ∘ Str.toList

      unwords∗ : List (String∗ × String∗) → String∗
      unwords∗ = concatMap (uncurry _++_)

      _ : words "a horse  and a    sheep" ≡
        ( ("" , "a")
        ∷ (" " , "horse")
        ∷ ("  " , "and")
        ∷ (" " , "a")
        ∷ ("    " , "sheep")
        ∷ [])
      _ = refl

      mapWords∗ : (String∗ → String∗) → String∗ → String∗
      mapWords∗ f = unwords∗ ∘ map (map₂ f) ∘ words∗

      mapWords : (String∗ → String∗) → String → String
      mapWords = apply∗ ∘ mapWords∗

      removeQualifiers∗ : String∗ → String∗
      removeQualifiers∗ = L.reverse ∘ go ∘ L.reverse
        where
          go : String∗ → String∗
          go s = case takeWhile (¬? ∘ ('.' Ch.≟_)) s of λ where
            []         → s
            s′@(_ ∷ _) → s′

      removeQualifiers : String → String
      removeQualifiers = mapWords removeQualifiers∗

      _ : removeQualifiers "open import Agda.Builtin.Char public -- hmm..."
        ≡ "open import Char public -- hmm..."
      _ = refl


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

  Show-Vis : Show Visibility
  Show-Vis .show = λ where visible → "𝕧"; hidden → "𝕙"; instance′ → "𝕚"

  Show-Arg : ⦃ Show A ⦄ → Show (Arg A)
  Show-Arg .show (arg (arg-info v _) x) = show v ◇ show x
  -- Show-Arg .show = show ∘ unArg

  Show-Abs : ⦃ Show A ⦄ → Show (Abs A)
  Show-Abs .show (abs s x) = "abs " ◇ show s ◇ " " ◇ show x

  mutual
    {-# TERMINATING #-}
    Show-Term : Show Term
    Show-Term .show = λ where
      (var x args)         → "var" <+> show x <+> show args
      (con c args)         → show c <+> show args
      (def f args)         → show f <+> show args
      (lam v (abs s x))    → "λ" <+> visibilityParen v s <+> "→" <+> show x
      (pat-lam cs args)    → "λ {" <+> show cs <+> "}" <+> show args
      (Π[ x ∶ arg i a ] b) → "Π (" ◇ visibilityParen (Meta.Argument.visibility i) x <+> ":"
                         <+> parensIfSpace (show a) ◇ ")" <+> parensIfSpace (show b)
      (sort s)             → show s
      (lit l)              → show l
      (meta x args)        → show x <+> show args
      unknown              → "unknown"

    Show-Clause : Show Clause
    Show-Clause .show = λ where
      (clause _ ps t)      → show ps <+> "→" <+> show t
      (absurd-clause _ ps) → show ps

    Show-Sort : Show Sort
    Show-Sort .show = λ where
      (set t)     → "Set" <+> parensIfSpace (show t)
      (lit n)     → "Set" ◇ show n -- no space to disambiguate from set t
      (prop t)    → "Prop" <+> parensIfSpace (show t)
      (propLit n) → "Prop" ◇ show n -- no space to disambiguate from prop t
      (inf n)     → "Setω" ◇ show n
      unknown     → "unknown"

    ShowPattern : Show Pattern
    ShowPattern .show = λ where
      (Pattern.con c []) → show c
      (Pattern.con c ps) → parens (show c <+> show ps)
      (Pattern.dot t)    → "." ◇ parens (show t)
      (Pattern.var x)    → "pat-var" <+> show x
      (Pattern.lit l)    → show l
      (Pattern.proj f)   → show f
      (Pattern.absurd _) → "()"

  open import Reflection.Definition
  Show-Definition : Show Definition
  Show-Definition .show = λ where
    (function cs)       → "function" <+> braces (show cs)
    (data-type pars cs) → "datatype" <+> show pars <+> braces (intersperse ", " (map show cs))
    (record′ c fs)      → "record" <+> show c <+> braces (intersperse ", " (map (show ∘′ unArg) fs))
    (constructor′ d)    → "constructor" <+> show d
    axiom               → "axiom"
    primitive′          → "primitive"
