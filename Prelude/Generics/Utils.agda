-------------------------------------------------
-- ** Utility macros

module Prelude.Generics.Utils where

open import Prelude.Init; open Meta
open import Prelude.Monad
open import Prelude.Functor
open import Prelude.Bifunctor
open import Prelude.Applicative
open import Prelude.Semigroup
open import Prelude.Show
open import Prelude.ToN
open import Prelude.Lists.Indexed
open import Prelude.DecEq.Core

-- private variable A B : Set ℓ

open import Prelude.Generics.Core
open import Prelude.Generics.Debug

{-# TERMINATING #-}
mapVariables : (ℕ → ℕ) → (Pattern → Pattern)
mapVariables f (Pattern.var n)      = Pattern.var (f n)
mapVariables f (Pattern.con c args) = Pattern.con c $ map (λ{ (arg i p) → arg i (mapVariables f p) }) args
mapVariables _ p                    = p

-- alternative view of function types as a pair of a list of arguments and a return type
TypeView = List (Abs (Arg Type)) × Type

viewTy : Type → TypeView
viewTy (Π[ s ∶ a ] ty) = Product.map₁ ((abs s a) ∷_) (viewTy ty)
viewTy ty              = [] , ty

tyView : TypeView → Type
tyView ([] , ty) = ty
tyView (abs s a ∷ as , ty) = Π[ s ∶ a ] tyView (as , ty)

argumentWise : (Type → Type) → Type → Type
argumentWise f ty =
  let
    as , r = viewTy ty
    as′ = map (fmap $ fmap f) as
  in tyView (as′ , r)

viewTy′ : Type → Args Type × Type
viewTy′ (Π[ _ ∶ a ] ty) = Product.map₁ (a ∷_) (viewTy′ ty)
viewTy′ ty              = [] , ty

-- mkTy : Args Type × Type → Type
-- mkTy ([] , ty) = ty
-- mkTy (a ∷ as , ty) = Π[ _ ∶ a ] mkTy (as , ty)

argTys : Type → Args Type
argTys = proj₁ ∘ viewTy′

resultTy : Type → Type
resultTy = proj₂ ∘ viewTy′

tyTele : Type → Telescope
tyTele = λ where
  (Π[ s ∶ a ] ty) → (s , a) ∷ tyTele ty
  _ → []

tyName : Type → Maybe Name
tyName (con n _) = just n
tyName (def n _) = just n
tyName _         = nothing

args : Term → Args Term
args (var _ xs)  = xs
args (def _ xs)  = xs
args (con _ xs)  = xs
args _           = []

args′ : Term → List Term
args′ = unArgs ∘ args


module _ (f : ℕ → ℕ) where

  _⁇_ : ℕ → ℕ → ℕ
  bound ⁇ x = if ⌊ bound Nat.≤? x ⌋ then f x else x

  mutual
    mapFreeVars : ℕ → (Term → Term)
    mapFreeVars bound = λ where
      (var x as)
        → var (bound ⁇ x) (mapFreeVars∗ bound as)
      (def c as)
        → def c (mapFreeVars∗ bound as)
      (con c as)
        → con c (mapFreeVars∗ bound as)
      (lam v (abs x t))
        → lam v (abs x (mapFreeVars (suc bound) t))
      (pat-lam cs as)
        → pat-lam (mapFreeVarsᶜ∗ bound cs) (mapFreeVars∗ bound as)
      (pi (arg i t) (abs x t′))
        → pi (arg i (mapFreeVars bound t)) (abs x (mapFreeVars (suc bound) t′))
      (agda-sort s)
        → agda-sort (mapFreeVarsˢ bound s)
      (meta x as)
        → meta x (mapFreeVars∗ bound as)
      t → t
    mapFreeVars∗ : ℕ → (Args Term → Args Term)
    mapFreeVars∗ b = λ where
      [] → []
      (arg i t ∷ ts) → arg i (mapFreeVars b t) ∷ mapFreeVars∗ b ts

    mapFreeVarsᵖ : ℕ → (Pattern → Pattern)
    mapFreeVarsᵖ b = λ where
      (con c ps) → con c (mapFreeVarsᵖ∗ b ps)
      (dot t)    → dot (mapFreeVars b t)
      (absurd x) → absurd (b ⁇ x)
      p → p
    mapFreeVarsᵖ∗ : ℕ → (Args Pattern → Args Pattern)
    mapFreeVarsᵖ∗ b = λ where
      [] → []
      (arg i p ∷ ps) → arg i (mapFreeVarsᵖ b p) ∷ mapFreeVarsᵖ∗ (suc b) ps

    mapFreeVarsᵗ : ℕ → (Telescope → Telescope)
    mapFreeVarsᵗ b = λ where
      [] → []
      ((s , arg i t) ∷ ts) → (s , arg i (mapFreeVars b t)) ∷ mapFreeVarsᵗ (suc b) ts

    mapFreeVarsᶜ : ℕ → (Clause → Clause)
    mapFreeVarsᶜ b = λ where
      -- (tel : List (Σ String λ _ → Arg Type)) (ps : List (Arg Pattern)) (t : Term)
      (clause tel ps t) → clause (mapFreeVarsᵗ b tel) (mapFreeVarsᵖ∗ b ps) (mapFreeVars (length tel + b) t)
      -- (tel : List (Σ String λ _ → Arg Type)) (ps : List (Arg Pattern))
      (absurd-clause tel ps) → absurd-clause (mapFreeVarsᵗ b tel) (mapFreeVarsᵖ∗ b ps)
    mapFreeVarsᶜ∗ : ℕ → (List Clause → List Clause)
    mapFreeVarsᶜ∗ b = λ where
      [] → []
      (c ∷ cs) → mapFreeVarsᶜ b c ∷ mapFreeVarsᶜ∗ b cs

    mapFreeVarsˢ : ℕ → (Sort → Sort)
    mapFreeVarsˢ b = λ where
      (set t) → set (mapFreeVars b t)
      (prop t) → prop (mapFreeVars b t)
      s → s

  mapVars : Term → Term
  mapVars = mapFreeVars 0

-- mapVars′ : (ℕ → ℕ) → Args Type → Args Type

-- mapVars f (var x args) = var (f x) (mapVars′ f args)
-- mapVars f (def c args) = def c (mapVars′ f args)
-- mapVars f (con c args) = con c (mapVars′ f args)
-- mapVars f (lam v (abs x t)) = lam v (abs x t′)
-- mapVars _ ty           = ty

-- mapVars′ f []              = []
-- mapVars′ f (arg i ty ∷ xs) = arg i (mapVars f ty) ∷ mapVars′ f xs

varsToUnknown : Type → Type
varsToUnknown′ : Args Type → Args Type

varsToUnknown (var _ _)  = unknown
varsToUnknown (def c xs) = def c (varsToUnknown′ xs)
varsToUnknown (con c xs) = con c (varsToUnknown′ xs)
varsToUnknown ty         = ty

varsToUnknown′ []              = []
varsToUnknown′ (arg i ty ∷ xs) = arg i (varsToUnknown ty) ∷ varsToUnknown′ xs

∀indices⋯ : Telescope → (Type → Type)
∀indices⋯ = λ where
  [] → id
  ((s , i) ∷ is) → Π[ s ∶ hide i ]_ ∘ ∀indices⋯ is

apply⋯ : Telescope → Name → Type
apply⋯ is n = def n
            $ remove-iArgs
            $ map (λ{ (n ,  _ , arg i _) → arg i (♯ (length is ∸ suc (toℕ n)))})
                  (enumerate is)

withHole : Type → Tactic → TC Hole
withHole ty k = do
  hole′ ← newMeta ty
  k hole′
  return hole′

-- ** records
mkRecord : List (Name × Term) → Term
mkRecord fs = pat-lam (map (λ where (fn , e) → clause [] [ vArg (proj fn) ] e) fs) []

updateField : List Name → Term → Name → Term → Term
updateField fs rexp fn fexp =
  pat-lam (flip map fs $ λ f →
    if f == fn then
      clause [] [ vArg (proj fn) ] fexp
    else
      clause [] [ vArg (proj f) ] (f ∙⟦ rexp ⟧)
    ) []

-- ** patterns
module _ (toDrop : ℕ) {- module context -} where
  mkPattern : Name → TC
    ( Args Type           -- ^ type arguments of given constructor
    × ℕ                   -- ^ # of introduced variables
    × List (ℕ × Arg Type) -- ^ generated variables along with their type
    × Pattern             -- ^ generated pattern for given constructor
    )
  mkPattern c = do
    ty ← reduce =<< getType c
    let tys  = drop toDrop (argTys ty)
        n    = length tys
        vars = map (map₁ toℕ) (enumerate tys)
    return
      $ tys
      , n
      , vars
      , Pattern.con c (map (λ{ (i , arg x _) → arg x (` i) }) vars)

fresh-level : TC Level
fresh-level = unquoteTC =<< newMeta (quote Level ∙)

-- newMeta_⦅ctx=_⦆ : Type → Context → TC Term
-- newMeta ty ⦅ctx= ctx ⦆ = do
--   hole@(meta m _) ← newMeta ty
--     where _ → _IMPOSSIBLE_
--   return $ meta m ctx

apply : Type → Term → List (Arg Term) → TC (Type × Term)
apply A t []       = return (A , t)
apply A t (a ∷ as) = do
  A ← reduce A
  A , t ← apply₁ A t a
  apply A t as
  where
    apply₁ : Type → Term → Arg Term → TC (Type × Term)
    apply₁ (pi (arg i₁@(arg-info k _) A) B) t₁ (arg i₂ t₂) = do
      a ← fresh-level
      b ← fresh-level
      A ← unquoteTC {A = Set a} A
      B ← unquoteTC {A = A → Set b} (lam visible B)
      t₂ ← unquoteTC {A = A} t₂
      Bt₂ ← quoteTC (B t₂)
      case k of λ where
        visible → do
          t₁ ← unquoteTC {A = ∀ (x : A) → B x} t₁
          Bt₂ ,_ <$> quoteTC (t₁ t₂)
        hidden → do
          t₁ ← unquoteTC {A = ∀ {x : A} → B x} t₁
          Bt₂ ,_ <$> quoteTC (t₁ {x = t₂})
        instance′ → do
          t₁ ← unquoteTC {A = ∀ ⦃ x : A ⦄ → B x} t₁
          Bt₂ ,_ <$> quoteTC (t₁ ⦃ x = t₂ ⦄)
    apply₁ (meta x _) _ _ = blockOnMeta x
    apply₁ A          _ _ = error "apply: not a Π-type"

_-∙-_ : Term → Term → TC Term
f -∙- x = do
  ty ← inferType f
  proj₂ <$> apply ty f [ vArg x ]
{-
_-∙-_ : Term → Term → TC Term
f -∙- x = case f of λ where
  (var x as) → return $ var x (as ∷v)
  (con c as) → return $ con c (as ∷v)
  (def f as) → return $ def f (as ∷v)
  (meta x as) → return $ meta x (as ∷v)
  (lam visible (abs _ t)) → go t
  _ → error $ "cannot apply terms " ◇ show f ◇ " -∙- " ◇ show x
   where
     _∷v = _∷ʳ vArg x
     go = λ where
       (var x′ as) → return $ var x (as ∷v)
       (con c as) → return $ con c (as ∷v)
       (def f as) → return $ def f (as ∷v)
       (meta x as) → return $ meta x (as ∷v)
       (lam visible (abs x t)) → go t
-}

_-∗-_ : Term → List Term → TC Term
f -∗- []       = return f
f -∗- (x ∷ xs) = f -∙- x >>= _-∗- xs

private
  macro
    test : Hole → TC ⊤
    test hole = unify hole =<<
      (proj₂ <$> apply (quoteTerm (ℕ → ℕ)) (quoteTerm suc) [ vArg (quoteTerm 5) ])

  _ : test ≡ 6
  _ = refl


instantiate : Hole → TC Term
-- instantiate  = reduce >=> onlyReducecDefs [] -- T0D0 added on v2.6.2
instantiate = reduce >=> normalise

module _ where -- ** unification
  open Debug ("Generics.unifyStrict", 100)

  ensureNoMetas : Term → TC ⊤
  ensureNoMetas = λ where
    (var x args) → noMetaArgs args
    (con c args) → noMetaArgs args
    (def f args) → noMetaArgs args
    (lam v (abs _ t)) → ensureNoMetas t
    (pat-lam cs args) → noMetaClauses cs *> noMetaArgs args
    (pi a b) → noMetaArg a *> noMetaAbs b
    (agda-sort s) → noMetaSort s
    (lit l) → pure _
    -- (meta x _) → errorP "meta found!"
    (meta x _) → blockOnMeta x
    unknown → pure _
     where
      noMetaArg : Arg Term → TC ⊤
      noMetaArg (arg _ v) = ensureNoMetas v

      noMetaArgs : List (Arg Term) → TC ⊤
      noMetaArgs [] = pure _
      noMetaArgs (v ∷ vs) = noMetaArg v *> noMetaArgs vs

      noMetaClause : Clause → TC ⊤
      noMetaClause (clause _ ps t) = ensureNoMetas t
      noMetaClause (absurd-clause _ ps) = pure _

      noMetaClauses : List Clause → TC ⊤
      noMetaClauses [] = pure _
      noMetaClauses (c ∷ cs) = noMetaClause c *> noMetaClauses cs

      noMetaAbs : Abs Term → TC ⊤
      noMetaAbs (abs _ v) = ensureNoMetas v

      noMetaSort : Sort → TC ⊤
      noMetaSort (set t) = ensureNoMetas t
      noMetaSort _       = pure _

  {-
  {-# TERMINATING #-}
  isSolved : Hole → Bool
  isSolved = λ where
    (meta _ _) → false
    unknown    → false
    (var _ xs) → all isSolved (unArgs xs)
    (con _ xs) → all isSolved (unArgs xs)
    (def _ xs) → all isSolved (unArgs xs)
    (lam _ (abs _ t)) → isSolved t
    (pat-lam cs xs) → all isSolved (unArgs xs)
    (pi (arg _ t) (abs _ t′)) → isSolved t ∧ isSolved t′
    _ → true
  -}

  module NewMeta where
    unifyStrict : THole → Term → TC ⊤
    unifyStrict (hole , ty) x = do
      printLn $ show hole ◇ " :=? " ◇ show x
      m ← newMeta ty
      noConstraints $
        unify m x >> unify hole m
      printLn $ show hole ◇ " := " ◇ show x

  module NoMeta where
    unifyStrict : THole → Term → TC ⊤
    unifyStrict (hole , ty) x = do
      -- unify hole x
      -- instantiate hole >>= ensureNoMetas

      print "———————————————————————————————————————"
      printTerm "x" x
      unify hole x
      hole ← normalise hole
      printTerm "hole′" hole
      -- (x ∷ hole ∷ []) ← mapM instantiate (x ∷ hole ∷ [])
      --   where _ → _IMPOSSIBLE_
      -- printTerm "x′" x
      ensureNoMetas hole
      printLn "No metas found :)"

  open NewMeta public
  -- open NoMeta public

  unifyStricts : THole → List Term → TC ⊤
  unifyStricts ht = L.NE.foldl₁ _<|>_
                  ∘ (L.NE._∷ʳ error "∅")
                  ∘ fmap ({-noConstraints ∘ -}unifyStrict ht)

-----------------------------------------------------------------------


{- experiment to allow subst syntax ⟪ x + ◆ ⟫ x≡ ~: ...
private
  open Debug ("rewrite" , 10)

  {-# TERMINATING #-}
  rewrite◆ : Term → TC Term
  rewrite◆ t = do
    let t′ = go 0 t
    print $ show t ◇ " ———→ " ◇ show t′
    return t′
    where
      go : ℕ → Term → Term
      go λs (lam v e) = lam v $ fmap (go (suc λs)) e
      go λs (def n xs) = def n $ map (fmap $ go λs) xs
      go λs (var n xs) = var n $ map (fmap $ go λs) xs
      go λs (meta m xs) = meta m $ map (fmap $ go λs) xs
      go λs (pi a b) = pi (fmap (go λs) a) (fmap (go λs) b)
      -- go λs (var n xs) =
      --   if n Nat.≡ᵇ 666 then
      --     ♯ λs
      --   else
      --     var n (map (fmap $ go λs) xs)
      go λs e@(lit (char c)) =
        if c Ch.== '◆' then
          ♯ λs
        else
          e
      -- go λs (lit (char '◆')) = ♯ λs
      go _ e = e

  macro
    λ◆ : Term → Term → TC ⊤
    λ◆ t hole = do
      t′ ← normalise t
      t″ ← rewrite◆ t′
      return tt
      -- unify hole (`λ "◆" ⇒ t′)

  import Reflection.Literal as Lit

  ∣◆∣ : Term
  -- ∣◆∣ = ♯ 666
  ∣◆∣ = Meta.lit (Lit.char '◆')

  f : ℕ → ℕ
  -- f = λ ◆ → ◆ + 1
  f = λ◆ (quote _+_ ∙⟦ ∣◆∣ ∣ Meta.lit (Lit.nat 1) ⟧)
-}
