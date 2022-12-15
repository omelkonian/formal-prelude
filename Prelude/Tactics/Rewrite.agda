{-# OPTIONS -v rewrite:100 #-}
{-# OPTIONS --with-K #-}
module Prelude.Tactics.Rewrite where

open import Prelude.Init
open Meta
open import Prelude.Generics
open Debug ("rewrite" , 100)

open import Prelude.DecEq
open import Prelude.General

open import Prelude.Functor
open import Prelude.Bifunctor
open import Prelude.Applicative
open import Prelude.Monad
open import Prelude.Semigroup
open import Prelude.Show
open import Prelude.Ord
open import Prelude.Membership
open import Prelude.Nary

private variable A : Set ℓ

viewEq : Term → TC (Term × Term)
viewEq eq = do
  (def (quote _≡_) (_ ∷ _ ∷ vArg x ∷ vArg y ∷ [])) ← inferType eq
    where _ → error "Can only write with equalities `x ≡ y`."
  return (x , y)

module _ (apply⁇ : ℕ → Bool) where

  getFocus : Term → Term → Term
  getFocus x = `λ "◆" ⇒_ ∘ proj₂ ∘ go 0 0
    where
      go : ℕ → ℕ → Term → Bool × Term
      go k n t =
        if (x == t) then
          true , (if apply⁇ k then (var n []) else x)
        else case t of λ where
          (con c as) → map₂ (con c) (goArgs k as)
          (def s as) → let b , as′ = goArgs k as
                      in b , def s as′
          (lam v (abs s a)) →
            let b , a′ = go k (suc n) a
            in b , lam v (abs s a′)
          (pat-lam cs as) →
            let b , cs′  = goCs k cs
                k′       = if b then suc k else k
                b′ , as′ = goArgs k′ as
            in  b ∨ b′ , pat-lam cs′ as′
          (pi (arg i a) (abs s P)) →
            let b , a′  = go k n a
                k′      = if b then suc k else k
                b′ , P′ = go k′ (suc n) P
            in (b ∨ b′) , pi (arg i a′) (abs s P′)
          _ → false , t
        where
          goArgs : ℕ → Args Term → Bool × Args Term
          goArgs _ []       = false , []
          goArgs k (arg i a ∷ as) =
            let b , a′   = go k n a
                k′       = if b then suc k else k
                b′ , as′ = goArgs k′ as
            in b ∨ b′ , arg i a′ ∷ as′

          goTel : ℕ → Telescope → Bool × Telescope
          goTel _ []       = false , []
          goTel k ((s , arg i t) ∷ ts) =
            let b , t′   = go k n t
                k′       = if b then suc k else k
                b′ , ts′ = goTel k′ ts
            in b ∨ b′ , (s , arg i t′) ∷ ts′

          mutual
            goP : ℕ → Pattern → Bool × Pattern
            goP k = λ where
              (con c ps) → map₂ (con c) (goPs k ps)
              (dot t) → map₂ dot $ go k n t
              p → false , p

            goPs : ℕ → Args Pattern → Bool × Args Pattern
            goPs _ []       = false , []
            goPs k (arg i p ∷ ps) =
              let b , p′   = goP k p
                  k′       = if b then suc k else k
                  b′ , ps′ = goPs k′ ps
              in b ∨ b′ , arg i p′ ∷ ps′

          goC : ℕ → Clause → Bool × Clause
          goC k = λ where
            (clause tel ps t) →
              let b , tel′  = goTel k tel
                  k′        = if b then suc k else k
                  b′ , ps′  = goPs k′ ps
                  k″        = if b′ then suc k′ else k′
                  b″ , t′   = go k″ n t
              in b ∨ b′ ∨ b″ , clause tel′ ps′ t′
            (absurd-clause tel ps) →
              let b , tel′  = goTel k tel
                  k′        = if b then suc k else k
                  b′ , ps′  = goPs k′ ps
              in b ∨ b′ , absurd-clause tel′ ps′

          goCs : ℕ → List Clause → Bool × List Clause
          goCs _ []       = false , []
          goCs k (c ∷ cs) =
            let b , c′   = goC k c
                k′       = if b then suc k else k
                b′ , cs′ = goCs k′ cs
            in b ∨ b′ , c′ ∷ cs′

  `subst `subst˘ : Type → Term → Term → Term → Term
  `subst  ty x eq t = quote subst ∙⟦ getFocus x ty ∣ eq ∣ t ⟧
  `subst˘ ty x eq t = `subst ty x (quote sym ∙⟦ eq ⟧) t

  rw : (Term → Term → Term → Term) → Term → A → Tactic
  rw {A = A} sub eq `t hole = do
    t ← quoteTC (A ∋ `t)
    x , y ← viewEq eq
    print $ "Rewriting: " ◇ show x ◇ " ≡ " ◇ show y
          ◇ "\n\t in:" ◇ show t
    let t′ = sub x eq t
    print $ " ⇒⇒⇒ " ◇ show t′
    unify hole t′

  rwAt : A → Term → Tactic
  rwAt {A = A} `t eq hole = do
    ty ← quoteTC A
    rw (`subst ty) eq `t hole

  rwBy : Term → A → Tactic
  rwBy eq `t hole = do
    ty ← inferType hole
    rw (`subst˘ ty) eq `t hole

∗ : ℕ → Bool
∗ = const true

macro
  ⟪_⟫_≈:_ = rwBy
  ⟪_⟫_:≈_ = rwAt
  _≈:_    = rwBy ∗
  _:≈_    = rwAt ∗

  ⟪[_]⟫_≈:_ : ∀ {n} → ℕ ^ n → Term → A → Tactic
  ⟪[ is ]⟫ eq ≈: t = rwBy (_∈ᵇ ⟦_⟧ {F = List} is) eq t

  ⟪[_]⟫_:≈_ : ∀ {n} → ℕ ^ n → A → Term → Tactic
  ⟪[ is ]⟫ t :≈ eq = rwAt (_∈ᵇ ⟦_⟧ {F = List} is) t eq

private
  rw-just : ∀ {m} {n : ℕ} → m ≡ just n → Is-just m
  rw-just eq
    -- rewrite eq = M.Any.just tt
    -- = subst Is-just (sym eq) (M.Any.just tt)
    = eq ≈: M.Any.just tt
    -- = M.Any.just tt :≈ eq -- does not work

  postulate
    X : Set
    a b : X
    eq : a ≡ b

    P : Pred₀ X
    Pa : P a

  open MultiTest

  _ = P b
   ∋⋮ subst (λ x → P x) eq Pa
    ⋮ Pa :≈ eq
    ⋮ sym eq ≈: Pa
    ⋮∅

  _ = P a ≡ P b
   ∋⋮ subst (λ x → P a ≡ P x) eq refl
    ⋮ subst (λ x → P x ≡ P b) (sym eq) refl
    ⋮ eq ≈: refl
    ⋮ sym eq ≈: refl
    ⋮ ⟪ _== 1 ⟫ refl {x = P a} :≈ eq
    ⋮ ⟪[ 1 , 2 , 3 ]⟫ refl {x = P a} :≈ eq
    ⋮∅

  postulate
    P² : Rel₀ X
    P²a : P² a a

  _ = P² b b
   ∋⋮ subst (λ x → P² x x) eq P²a
    ⋮ P²a :≈ eq
    ⋮ sym eq ≈: P²a
    ⋮∅

  postulate
    P³ : 3Rel₀ X
    P³a : P³ a b a

  _ = P³ b a a
   ∋⋮ ⟪[ 1 ]⟫ (⟪[ 0 ]⟫ P³a :≈ eq) :≈ sym eq
    ⋮ ⟪[ 0 ]⟫ eq ≈: ⟪[ 0 ]⟫ P³a :≈ eq
    ⋮∅

  postulate g : P b → X

  _ = (∃ λ (A : Set) → A)
   ∋⋮ (-, g (Pa :≈ eq))
    ⋮ (-, g (sym eq ≈: Pa))
    ⋮∅

  postulate
    f : P a ≡ P b → X
    f′ : (P a ≡ P b) × (P b ≡ P a) → X

  rw-in-argument : X
  rw-in-argument = f Pa≡Pb
    where Pa≡Pb : P a ≡ P b
          Pa≡Pb rewrite eq = refl

  _ = X
   ∋⋮ f $ subst (λ x → P a ≡ P x) eq refl
    ⋮ f $ subst (λ x → P x ≡ P b) (sym eq) refl
    ⋮ (f $ ⟪ _== 1 ⟫ refl {x = P a} :≈ eq)
    ⋮ f $ eq ≈: refl
    ⋮∅

  _ = X
   ∋⋮ f′ $ eq     ≈: (refl , refl)
    ⋮ f′ $ sym eq ≈: (refl , refl)
    ⋮∅
