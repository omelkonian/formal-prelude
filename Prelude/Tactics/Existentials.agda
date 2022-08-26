module Prelude.Tactics.Existentials where

open import Prelude.Init
open import Prelude.Functor
open import Prelude.Monad

open import Prelude.Generics
open Meta

mkExistential : ℕ → Name → TC Term
mkExistential lvl t = do
  ty ← getType t
  let n = length (argTys ty) ∸ lvl
  return $ go n n
  where
    go : ℕ → ℕ → Term
    go n₀ 0       = def t (map (λ n → vArg (♯ n)) (L.reverse $ upTo n₀))
    go n₀ (suc n) = quote ∃ ∙⟦ (`λ "_" ⇒ go n₀ n) ⟧

macro
  mk∃[nest:_] : ℕ → Name → Tactic
  mk∃[nest:_] lvl t hole = mkExistential lvl t >>= unify hole

  mk∃ : Name → Tactic
  mk∃ t hole = mkExistential 0 t >>= unify hole

private
  data X : ℕ → String → ℕ → Set where
    mkX : X 0 "" 1

  _ : mk∃ X
  _ = 0 , "" , 1 , mkX

  module _ (n : ℕ) where
    data Y : String → ℕ → Set where
      mkY : Y "" 1

    _ : mk∃[nest: 1 ] Y
    _ = "" , 1 , mkY

    module _ (s : String) where

      data Z : ℕ → Set where
        mkZ : Z 1

      _ : mk∃[nest: 2 ] Z
      _ = 1 , mkZ

    _ : mk∃[nest: 1 ] Z
    _ = "sth" , 1 , mkZ

  _ : mk∃ Y
  _ = 42 , "" , 1 , mkY

  _ : mk∃ Z
  _ = 0 , "sth" , 1 , mkZ
