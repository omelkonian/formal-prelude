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

private
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

private
  f : ℕ → List ℤ
  f n = [ + n ]
  g : ℕ → Vec ℤ 1
  g n = V.[ + n ]
  fs : String → List ℤ
  fs _ = [ + 0 ]

  open Collect (quote f ∷ quote g ∷ quote fs ∷ [])

  -- DOES NOT WORK: expects List to the right of _≡_
  -- _ = collect 5 ≡ V.[ + 5 ] ∋ refl

  -- DOES NOT WORK: expects List to the left of _≡_
  -- _ = V.[ + 5 ] ≡ collect 5 ∋ refl

  ex-f : ℕ → List ℤ
  ex-f = collect
  _ = ex-f 5 ≡ [ + 5 ] ∋ refl

  ex-g : ℕ → Vec ℤ 1
  ex-g = collect
  _ = ex-g 5 ≡ V.[ + 5 ] ∋ refl

  ex-fs : String → List ℤ
  ex-fs = collect
  _ = ex-fs "sth" ≡ [ + 0 ] ∋ refl

-- ** using (internal) instance search
private
  record Collectible (A : Set) : Set where
    constructor give_
    field collectName : Name
  open Collectible ⦃...⦄

REGISTER : List (Name × Name) → TC ⊤
REGISTER ns = void $ forM ns λ (n , n′) → do
  ty ← getType n
  `n ← quoteTC n
  genSimpleInstance n′
    (quote Collectible ∙⟦ ty ⟧)
    (quote give_ ◆⟦ `n ⟧)

collectBase : Type → TC Term
collectBase goal = do
  print $ "Retrieving collections for: " ◇ show goal
  (meta m _) ← newMeta (quote Collectible ∙⟦ goal ⟧)
    where _ → _IMPOSSIBLE_
  just f ← L.head <$> getInstances m
    where _ → error "no implementation found"
  print $ "Found collectible implementation : " ◇ show f
  n ← unquoteTC {A = Name} (def (quote collectName) [ iArg f ])
  return (n ∙)

record ToTerm (A : Set ℓ) : Set ℓ where
  field toTerm : A → TC Term
open ToTerm ⦃...⦄
instance
  ToTerm-Term : ToTerm Term
  ToTerm-Term .toTerm = return

  ToTerm-Name : ToTerm Name
  ToTerm-Name .toTerm n = return $ def n []

  ToTerm-Set : ToTerm (Set ℓ)
  ToTerm-Set .toTerm = quoteTC

collectSource : {A : Set ℓ} → ⦃ ToTerm A ⦄ → A → Tactic
collectSource As hole = do
  As ← toTerm As
  (X ∷ _) ← vArgs ∘ argTys <$> inferType hole
    where _ → error "expected goal of the form: X → As"
  unify hole =<< collectBase (vΠ[ "_" ∶ X ] As)

_∘collectSource_ : {P : Set ℓ} {A : Set ℓ′} → ⦃ ToTerm P ⦄ → ⦃ ToTerm A ⦄
  → P → A → Tactic
(f ∘collectSource As) hole = do
  As ← toTerm As
  f ← toTerm f
  (X ∷ _) ← vArgs ∘ argTys <$> inferType hole
    where _ → error "expected goal of the form: X → As"
  t ← collectBase (vΠ[ "_" ∶ X ] As)
  unify hole (quote _∘_ ∙⟦ f ∣ t ⟧)

macro collectI = λ hole → unify hole =<< collectBase =<< inferType hole

private
  -- instance
  --   collect-f = Collectible (ℕ → List ℤ)  ∋ give quote f
  --   collect-g = Collectible (ℕ → Vec ℤ 1) ∋ give quote g
  unquoteDecl collect-f collect-g collect-fs = REGISTER
    ( (quote f , collect-f)
    ∷ (quote g , collect-g)
    ∷ (quote fs , collect-fs)
    ∷ []
    )

  -- DOES NOT WORK: thinks we're expecting List to the right of _≡_
  -- _ = collectI 5 ≡ V.[ + 5 ] ∋ refl

  _ = V.[ + 5 ] ≡ collectI 5 ∋ refl

  iex-f : ℕ → List ℤ
  iex-f = collectI
  _ = iex-f 5 ≡ [ + 5 ] ∋ refl

  iex-g : ℕ → Vec ℤ 1
  iex-g = collectI
  _ = iex-g 5 ≡ V.[ + 5 ] ∋ refl

  iex-fs : String → List ℤ
  iex-fs = collect
  _ = iex-fs "sth" ≡ [ + 0 ] ∋ refl

  macro ints = collectSource (List ℤ)
        nats = quote ints→nats ∘collectSource (List ℤ)
          where ints→nats = map {A = ℤ} (const 42)

  z-f : ℕ → List ℤ
  z-f = ints
  _ = z-f 0 ≡ [ + 0 ] ∋ refl

  z-fs : String → List ℤ
  z-fs = ints
  _ = z-fs "sth" ≡ [ + 0 ] ∋ refl

  n-fs : String → List ℕ
  n-fs = nats
  _ = n-fs "sth" ≡ [ 42 ] ∋ refl
