{-# OPTIONS -v AltIso:100 #-}
module Prelude.Lists.AltIso where

open import Prelude.Init
open Meta
open import Prelude.Generics
open Debug ("AltIso" , 100)
open import Prelude.Show
open import Prelude.Semigroup
open import Prelude.Monad
open import Prelude.DecEq

variable
  A B : Set
  f : A → B
  g : A → B
  xs : List A

open import Prelude.Tactics.Rewrite

viewEq′ : Term → TC (Term × Term)
viewEq′ eq = do
  (def (quote _≡_) args) ← inferType eq >>= normalise
    where _ → error "Can only write with equalities `x ≡ y`."
  case vArgs args of λ where
    (x ∷ y ∷ []) → return (x , y)
    _ → error "Malformed arguments to _≡_."

subs : Term × Term → Op₁ Term
subs (x , x′) = go
  where mutual
    goArgs : Args Term → Args Term
    goArgs [] = []
    goArgs (arg i a ∷ as) = arg i (go a) ∷ goArgs as

    goTel : Telescope → Telescope
    goTel [] = []
    goTel ((s , arg i t) ∷ ts) = (s , arg i (go t)) ∷ goTel ts

    goP : Pattern → Pattern
    goP = λ where
      (con c ps) → con c (goPs ps)
      (dot t) → dot (go t)
      p → p

    goPs : Args Pattern → Args Pattern
    goPs [] = []
    goPs (arg i p ∷ ps) = arg i (goP p) ∷ goPs ps

    goC : Clause → Clause
    goC = λ where
      (clause tel ps t) → clause (goTel tel) (goPs ps) (go t)
      (absurd-clause tel ps) → absurd-clause (goTel tel) (goPs ps)

    goCs : List Clause → List Clause
    goCs [] = []
    goCs (c ∷ cs) = goC c ∷ goCs cs

    go : Term → Term
    go t =
      if (x == t) then
        x′
      else case t of λ where
        (con c as) → con c (goArgs as)
        (def s as) → def s (goArgs as)
        (lam v (abs s a)) → lam v (abs s (go a))
        (pat-lam cs as) → pat-lam (goCs cs) (goArgs as)
        (pi (arg i a) (abs s P)) → pi (arg i (go a)) (abs s (go P))
        _ → t

transport : Term → A → Tactic
transport {A = A} eq `t hole = do
  ty ← quoteTC A
  print $ "Ty: " ◇ show ty
  t  ← quoteTC (A ∋ `t)
  print $ "t " ◇ show t
  -- holeTy ← inferType hole
  -- print $ "Hole: " ◇ show holeTy
  print $ "Eq: " ◇ show eq
  x , y ← viewEq′ eq
  print $ "Eq≡: " ◇ show x ◇ " ≡ " ◇ show y
  let t′ = subs (x , y) t
  print $ "t′: " ◇ show t′
  unify hole t′

macro
  transportM = transport

-- ** catMaybes
catMaybes : List (Maybe A) → List A
catMaybes [] = []
catMaybes (nothing ∷ xs) = catMaybes xs
catMaybes (just x ∷ xs)  = x ∷ catMaybes xs

Any-catMaybes⁺ : ∀ {P : Pred A ℓ} {xs : List (Maybe A)}
  → Any (M.Any.Any P) xs → Any P (catMaybes xs)
Any-catMaybes⁺ {xs = just x ∷ xs} = λ where
  (here (M.Any.just px)) → here px
  (there x∈)             → there $ Any-catMaybes⁺ x∈
Any-catMaybes⁺ {xs = nothing ∷ xs} (there x∈) = Any-catMaybes⁺ x∈

module _ {A B : Set} (f : A → Maybe B) where
  mapMaybe′ : List A → List B
  mapMaybe′ = catMaybes ∘ map f

  mapMaybe≗mapMaybe′ : mapMaybe′ ≗ mapMaybe f
  mapMaybe≗mapMaybe′ [] = refl
  mapMaybe≗mapMaybe′ (x ∷ xs) with f x
  ... | nothing = mapMaybe≗mapMaybe′ xs
  ... | just _  = cong (_ ∷_) (mapMaybe≗mapMaybe′ xs)

  -- module _ {P : Pred₀ B} where
  --   Any-mapMaybe′⁺ : Any (M.Any.Any P ∘ f) xs → Any P (mapMaybe′ xs)
  --   Any-mapMaybe′⁺ = Any-catMaybes⁺ ∘ L.Any.map⁺

  --   -- unquoteDecl Any-mapMaybe⁺ = transportDef mapMaybe≗mapMaybe′ (quote Any-mapMaybe′⁺)
  --   Any-mapMaybe⁺ : transport mapMaybe≗mapMaybe′ (Any (M.Any.Any P ∘ f) xs → Any P (mapMaybe f xs))
  --   Any-mapMaybe⁺ = transport mapMaybe≗mapMaybe′ (Any-catMaybes⁺ ∘ L.Any.map⁺)
  --   -- Any-mapMaybe′⁺ {xs = xs} rewrite mapMaybe≗mapMaybe′ f xs = Any-mapMaybe⁺

private

  toM : ℕ → Maybe String
  toM = λ where
    0 → just "zero"
    _ → nothing

  postulate ns : List ℕ
  -- ns = 1 ∷ 2 ∷ 0 ∷ []

  _ : mapMaybe′ toM ns ≡ transportM (mapMaybe≗mapMaybe′ toM ns) (mapMaybe toM ns)
  _ = refl
