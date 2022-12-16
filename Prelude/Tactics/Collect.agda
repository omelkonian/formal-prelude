{-# OPTIONS --with-K #-}
{-# OPTIONS -v collect:100 #-}
module Prelude.Tactics.Collect where

open import Agda.Builtin.Reflection using (getInstances)

open import Prelude.Init
open Meta
open import Prelude.Generics
open Debug ("collect" , 100)
open import Prelude.Monad
open import Prelude.Show
open import Prelude.Semigroup
open import Prelude.Functor
open import Prelude.DecEq
open import Prelude.Foldable
open import Prelude.Traversable
open import Prelude.Membership
open import Prelude.Lists.Dec

{-# TERMINATING #-}
names : Term → List Name
names = go where go = λ where
  (var x as) → concatMap (go ∘ unArg) as
  (con c as) → c ∷ concatMap (go ∘ unArg) as
  (def f as) → f ∷ concatMap (go ∘ unArg) as
  (lam v t)  → go (unAbs t)
  (pi a b) → go (unArg a) ++ go (unAbs b)
  _ → []

-- using hard-coded (static) list of collection functions
module Collect (fs : List Name) where macro
  collect : Tactic
  collect hole = do
    goal ← inferType hole -- >>= reduce
    print $ "Retrieving collection for: " ◇ show goal
    let ns = names goal
    print $ "Names: " ◇ show ns
    just f ← L.head ∘ concat <$> forM fs λ f → do
      ty ← getType f
      return $ if ⌊ ns ⊆? names ty ⌋ then [ f ] else []
     where _ → error $ "no implementation found in: " ◇ show fs
    unify hole (f ∙)

f : ℕ → List ℤ
f n = [ + n ]
g : ℕ → Vec ℤ 1
g n = V.[ + n ]

open Collect (quote f ∷ quote g ∷ [])

ex : ℕ → List ℤ
ex = collect

_ = ex 5 ≡ [ + 5 ]
  ∋ refl

ex′ : ℕ → Vec ℤ 1
ex′ = collect

_ = ex′ 5 ≡ V.[ + 5 ]
  ∋ refl

-- DOES NOT WORK: expects List to the right of _≡_
-- _ = collect 5 ≡ V.[ + 5 ]
--   ∋ refl

-- DOES NOT WORK: expects List to the left of _≡_
-- _ = V.[ + 5 ] ≡ collect 5
--   ∋ refl

-- ** using (internal) instance search
record Collectible (A : Set) : Set where
  constructor give_
  field collectName : Name
open Collectible ⦃...⦄ public

-- instance
--   collect-f = Collectible (ℕ → List ℤ) ∋ give quote f
--   collect-g = Collectible (ℕ → Vec ℤ 1) ∋ give quote g

REGISTER : List (Name × Name) → TC ⊤
REGISTER ns = void $ forM ns λ (n , n′) → do
  ty ← getType n
  `n ← quoteTC n
  genSimpleInstance n′
    (quote Collectible ∙⟦ ty ⟧)
    (quote give_ ◆⟦ `n ⟧)

unquoteDecl collect-f collect-g = REGISTER
  ( (quote f , collect-f)
  ∷ (quote g , collect-g)
  ∷ []
  )

macro
  collectI : Tactic
  collectI hole = do
    goal ← inferType hole
    print $ "Goal: " ◇ show goal
    let ns = names goal
    print $ "Names in goal: " ◇ show ns
    (meta m _) ← newMeta (quote Collectible ∙⟦ goal ⟧)
      where _ → _IMPOSSIBLE_
    is ← getInstances m
    print $ "Collectible instances: " ◇ show is
    just f ← return (L.head is)
      where _ → error $ "no implementation found"
    print $ "Found implementation : " ◇ show f
    n ← unquoteTC {A = Name} (def (quote collectName) [ iArg f ])
    unify hole (n ∙)

iex : ℕ → List ℤ
iex = collectI

_ = iex 5 ≡ [ + 5 ]
  ∋ refl

iex₂ : ℕ → Vec ℤ 1
iex₂ = collectI

_ = iex₂ 5 ≡ V.[ + 5 ]
  ∋ refl

-- DOES NOT WORK: thinks we're expecting List to the right of _≡_
-- _ = collectI 5 ≡ V.[ + 5 ]
--   ∋ refl

_ = V.[ + 5 ] ≡ collectI 5
  ∋ refl
