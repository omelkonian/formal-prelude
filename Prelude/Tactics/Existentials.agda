module Prelude.Tactics.Existentials where

open import Prelude.Init
open import Prelude.Functor
open import Prelude.Monad

open import Prelude.Generics
open Meta

mkExistential : Name → TC Term
mkExistential t = do
  ty ← getType t
  let n = length (argTys ty)
  return $ go n n
  where
    go : ℕ → ℕ → Term
    go n₀ 0       = def t (map (λ n → vArg (♯ n)) (L.reverse $ upTo n₀))
    go n₀ (suc n) = quote ∃ ∙⟦ (`λ "_" ⇒ go n₀ n) ⟧

macro
  mk∃ : Name → Tactic
  mk∃ t hole = mkExistential t >>= unify hole

private
  data X : ℕ → String → ℕ → Set where
    mkX : X 0 "" 1

  _ : mk∃ X
  _ = 0 , "" , 1 , mkX

  module _ (n : ℕ) where
    data Y : String → ℕ → Set where
      mkY : Y "" 1

    _ : mk∃ Y
    _ = "" , 1 , mkY

    module _ (s : String) where

      data Z : ℕ → Set where
        mkZ : Z 1

      _ : mk∃ Z
      _ = 1 , mkZ

    _ : mk∃ Z
    _ = "sth" , 1 , mkZ

  _ : mk∃ Y
  _ = 42 , "" , 1 , mkY

  _ : mk∃ Z
  _ = 0 , "sth" , 1 , mkZ
