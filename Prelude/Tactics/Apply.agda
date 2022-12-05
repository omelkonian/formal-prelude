-- Smart application that works for multiple hidden/visible configurations.
module Prelude.Tactics.Apply where

open import Prelude.Init; open Meta
open import Prelude.Generics; open Debug ("apply" , 100)
open import Prelude.Monad

{-
f {x = y} x y
↝
⊚ f {x = y} x y
-}
postulate viewApplication : Term → TC $ Maybe (Term × Args Term)

searchValidApps : Term → Args Term → TC (List Term)
searchValidApps f as = {!!}

infix -100 ⊚_
macro
  ⊚_ : Term → Hole → TC ⊤
  (⊚ t) hole = do
    holeTy ← inferType hole
    let thole = hole , holeTy
    just (f , as) ← viewApplication t
      where nothing → error "apply: not an application"
    ts ← searchValidApps f as
    unifyStricts thole ts
