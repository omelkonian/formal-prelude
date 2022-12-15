-------------------------------------------------
-- ** Errors, debugging

-- {-# OPTIONS --safe #-}
module Prelude.Generics.Debug where

open import Prelude.Init; open Meta
open import Prelude.Monad
open import Prelude.Nary
open import Prelude.Semigroup
open import Prelude.Functor
open import Prelude.Bifunctor
open import Prelude.Applicative
open import Prelude.Foldable
open import Prelude.Traversable
open import Prelude.Show
open import Prelude.Lists.Indexed

open import Prelude.Generics.Core

private variable A : Set ℓ

error : String → TC A
error s = typeError [ strErr s ]

_IMPOSSIBLE_ : TC A
_IMPOSSIBLE_ = error "IMPOSSIBLE"

module Debug (v : String × ℕ) where
  -- i.e. set {-# OPTIONS -v v₁:v₂ #-} to enable such messages in the **debug** buffer.

  print printLn : String → TC ⊤
  print s = debugPrint (v .proj₁) (v .proj₂) [ strErr s ]
  printLn = print ∘ (_<> "\n")
  printLns = print ∘ Str.unlines

  printS : ⦃ _ : Show A ⦄ → A → TC ⊤
  printS = print ∘ show
    where open import Prelude.Show

  errorP : String → TC A
  errorP s = printLn s >> error s

  Ap₀-TC : Applicative₀ TC
  Ap₀-TC = λ where .ε₀ → errorP "∅ alternative"

  infix -1 ⋃∗_
  ⋃∗_ : List (TC A) → TC A
  ⋃∗_ = foldr _<|>_ ε₀
    where instance ap₀ = Ap₀-TC

  printTerm : String → Term → TC ⊤
  printTerm s t = do
    ty ← inferType t
    printLns
      ⟦ s ◇ ": {"
      , show ty
      , " ∋ "
      , show t
      , "}\n"
      ⟧

  showTermClauses : Term → String
  showTermClauses = λ where
    (pat-lam cs []) → "\n" ◇ Str.unlines (flip map cs $ λ c → "  " ◇ show c)
    e → show e

  printContext : Context → TC ⊤
  printContext ctx = do
    print "\t----CTX----"
    void $ traverseM go (enumerate ctx)
    where
      go : Index ctx × String × Arg Type → TC ⊤
      go (i , s , ty) = print $ "\t[" ◇ show i ◇ "] " ◇ s ◇ " : " ◇ show ty

  printCurrentContext : TC ⊤
  printCurrentContext = printContext =<< getContext

  -- ** definitions
  genDef : Arg Name → Type → Term → TC ⊤
  genDef an ty e = do
    let n = unArg an
    print $ "Generaring" ◇ (if ⌊ isInstance? an ⌋ then " instance" else "") ◇ "..."
    declareDef an ty
    print $ "```\n" ◇ show n ◇ " : " ◇ " " ◇ show ty
    defineFun n [ clause [] [] e ]
    print $ show n ◇ " = " ◇ showTermClauses e
    print "```"

  genSimpleDef genSimpleInstance : Name → Type → Term → TC ⊤
  genSimpleDef      = genDef ∘ vArg
  genSimpleInstance = genDef ∘ iArg

module DebugI (v : String) where
  -- i.e. set {-# OPTIONS -v ⟨v⟩:0 #-} to enable messages in the **info** buffer.
  open Debug (v , 0) public

-- set {-# OPTIONS -v trace:100 #-} when tracing
macro
  trace : ∀ {A : Set} ⦃ _ : Show A ⦄ → A → Term → Term → TC ⊤
  trace x t hole = print ("trace: " ◇ show x) >> unify hole t
    where open Debug ("trace" , 100)
