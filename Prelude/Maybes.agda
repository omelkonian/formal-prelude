------------------------------------------------------------------------
-- Utilities for Maybe.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Prelude.Maybes where

open import Prelude.Init; open SetAsType
open Maybe
open import Prelude.Applicative
open import Prelude.Functor
open import Prelude.Bifunctor

private variable A : Type ℓ; B : Type ℓ′

toMaybe : List A → Maybe A
toMaybe []      = nothing
toMaybe (x ∷ _) = just x

toMaybe-≡ : ∀ {x : A} {xs : List A}
  → toMaybe xs ≡ just x
  → ∃[ ys ] (xs ≡ x ∷ ys)
toMaybe-≡ {xs = _ ∷ _} refl = _ , refl

ap-nothing : ∀ {A : Type ℓ} {B : Type ℓ′} {r : B} {m : Maybe (A → B)} → (m <*> nothing) ≢ just r
ap-nothing {m = nothing} ()
ap-nothing {m = just _ } ()

Any-just : ∀ {x : A} {mx : Maybe A} {P : A → Type}
 → mx ≡ just x
 → M.Any.Any P mx
 → P x
Any-just refl (M.Any.just p) = p

Any⇒Is-just : ∀ {mx : Maybe A} {P : A → Type}
 → M.Any.Any P mx
 → Is-just mx
Any⇒Is-just {mx = .(just _)} (M.Any.just _) = M.Any.just tt

module _ {A : Type ℓ} where
  is-nothing? : Decidable¹ (T ∘ M.is-nothing {A = A})
  is-nothing? = T? ∘ M.is-nothing

  is-just? : Decidable¹ (T ∘ M.is-just {A = A})
  is-just? = T? ∘ M.is-just

  is-just≡ : ∀ {mx : Maybe A} → T (M.is-just mx) → ∃ λ x → mx ≡ just x
  is-just≡ {mx = just _} _ = -, refl

  ¬is-just≡ : ∀ {mx : Maybe A} → ¬ T (M.is-just mx) → mx ≡ nothing
  ¬is-just≡ {mx = just _}  p = ⊥-elim $ p tt
  ¬is-just≡ {mx = nothing} _ = refl

  Is-just? : (mx : Maybe A) → Dec (Is-just mx)
  Is-just? = M.Any.dec λ _ → yes tt

  Is-just⇒≢nothing : ∀ {mx : Maybe A} → Is-just mx → mx ≢ nothing
  Is-just⇒≢nothing {mx = nothing} () _
  Is-just⇒≢nothing {mx = just _} _ ()

  Is-nothing≡ : ∀ {mx : Maybe A} → Is-nothing mx → mx ≡ nothing
  Is-nothing≡ {mx = nothing} _ = refl
  Is-nothing≡ {mx = just _} (M.All.just ())

  ¬Is-just⇒Is-nothing : ∀ {mx : Maybe A} → ¬ Is-just mx → Is-nothing mx
  ¬Is-just⇒Is-nothing {mx = nothing} _ = M.All.nothing
  ¬Is-just⇒Is-nothing {mx = just _}  p = ⊥-elim $ p (M.Any.just tt)

  destruct-Is-just : ∀ {mx : Maybe A}
    → Is-just mx
    → ∃ λ x → mx ≡ just x
  destruct-Is-just {mx = nothing} ()
  destruct-Is-just {mx = just _}  _ = _ , refl

  MAll⇒¬MAny : ∀ {m : Maybe A} → M.All.All (const ⊥) m → ¬ M.Any.Any (const ⊤) m
  MAll⇒¬MAny {m = nothing} M.All.nothing ()

  mk-Is-just : ∀ {mx : Maybe A} {x : A} → mx ≡ just x → Is-just mx
  mk-Is-just refl = M.Any.just tt
