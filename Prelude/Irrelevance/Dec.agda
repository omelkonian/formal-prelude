{-# OPTIONS --safe #-}
module Prelude.Irrelevance.Dec where

import Relation.Nullary.Decidable as Dec

open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.Decidable
open import Prelude.DecEq.Core

open import Prelude.Irrelevance.Core
open import Prelude.Irrelevance.Empty

private variable b b′ : Bool; P : Type ℓ; Q : Type ℓ′

·⇒DecEq : ⦃ · P ⦄ → DecEq P
·⇒DecEq = Irrelevant⇒DecEq ∀≡

data ·Reflects (P : Type ℓ) : Bool → Type ℓ where
  ofʸ : ( p :    P) → ·Reflects P true
  ofⁿ : (¬p : ·¬ P) → ·Reflects P false

·of : if b then P else ·¬ P → ·Reflects P b
·of {b = false} ¬p = ofⁿ ¬p
·of {b = true }  p = ofʸ p

·invert : ·Reflects P b → if b then P else ·¬ P
·invert (ofʸ  p) = p
·invert (ofⁿ ¬p) = ¬p

·fromEquivalence : (·T b → P) → (P → ·T b) → ·Reflects P b
·fromEquivalence {b = true}  sound complete = ofʸ (sound _)
·fromEquivalence {b = false} sound complete = ofⁿ complete

·det : ·Reflects P b → ·Reflects P b′ → b ≡ b′
·det (ofʸ  p) (ofʸ  p′) = refl
·det (ofʸ  p) (ofⁿ ¬p′) = ·⊥-elim (¬p′ p)
·det (ofⁿ ¬p) (ofʸ  p′) = ·⊥-elim (¬p p′)
·det (ofⁿ ¬p) (ofⁿ ¬p′) = refl

record ·Dec (P : Type ℓ) : Type ℓ where
  constructor _because_
  field does  : Bool
        proof : ·Reflects P does
open ·Dec public
pattern yes p =  true because ofʸ  p
pattern no ¬p = false because ofⁿ ¬p

·Reflects⇔Reflects : ·Reflects P ⊣⊢ Nullary.Reflects P
·Reflects⇔Reflects
  = (λ where (ofʸ p) → ofʸ p; (ofⁿ ¬p) → ofⁿ (·¬⇒¬ ¬p))
  , (λ where (ofʸ p) → ofʸ p; (ofⁿ ¬p) → ofⁿ (¬⇒·¬ ¬p))

·Reflects⇒Reflects : ·Reflects P ⊆¹ Nullary.Reflects P
·Reflects⇒Reflects = ·Reflects⇔Reflects .proj₁

Reflects⇒·Reflects : Nullary.Reflects P ⊆¹ ·Reflects P
Reflects⇒·Reflects = ·Reflects⇔Reflects .proj₂

·Dec⇔Dec : ·Dec P ↔ Dec P
·Dec⇔Dec = (λ where (b because p) → b because ·Reflects⇒Reflects p)
         , (λ where (b because p) → b because Reflects⇒·Reflects p)

·Dec⇒Dec : ·Dec P → Dec P
·Dec⇒Dec = ·Dec⇔Dec .proj₁

Dec⇒·Dec : Dec P → ·Dec P
Dec⇒·Dec = ·Dec⇔Dec .proj₂

·isYes : ·Dec P → Bool
·isYes ( true because _) = true
·isYes (false because _) = false

·isYes≗does : (P? : ·Dec P) → ·isYes P? ≡ does P?
·isYes≗does ( true because _) = refl
·isYes≗does (false because _) = refl

·⌊_⌋ = isYes

·isNo : ·Dec P → Bool
·isNo = not ∘ ·isYes

·True : Pred₀ (·Dec P)
·True Q = ·T (·isYes Q)

·False : Pred₀ (·Dec P)
·False Q = ·T (·isNo Q)

·toWitness : {Q : ·Dec P} → ·True Q → P
·toWitness {Q = true  because [p]} _  = ·invert [p]
·toWitness {Q = false because  _ } ()

·fromWitness : {Q : ·Dec P} → P → ·True Q
·fromWitness {Q = true  because   _ } = const _
·fromWitness {Q = false because [¬p]} = ·invert [¬p]

·toWitnessFalse : {Q : ·Dec P} → ·False Q → ·¬ P
·toWitnessFalse {Q = true  because   _ } ()
·toWitnessFalse {Q = false because [¬p]} _  = ·invert [¬p]

·fromWitnessFalse : {Q : ·Dec P} → ·¬ P → ·False Q
·fromWitnessFalse {Q = true  because [p]} = flip _$_ (·invert [p])
·fromWitnessFalse {Q = false because  _ } = const _

module _ {P : Type ℓ} where

  ·From-yes : Pred (·Dec P) ℓ
  ·From-yes (true  because _) = P
  ·From-yes (false because _) = Lvl.Lift _ ⊤

  ·from-yes : (p : ·Dec P) → ·From-yes p
  ·from-yes (true  because [p]) = ·invert [p]
  ·from-yes (false because _ ) = _

  ·From-no : Pred (·Dec P) ℓ
  ·From-no (false because _) = ·¬ P
  ·From-no (true  because _) = Lvl.Lift _ ⊤

  ·from-no : (p : ·Dec P) → ·From-no p
  ·from-no (false because [¬p]) = ·invert [¬p]
  ·from-no (true  because   _ ) = _

·dec-true : (p? : ·Dec P) → P → does p? ≡ true
·dec-true (true  because   _ ) p = refl
·dec-true (false because [¬p]) p = ·⊥-elim (·invert [¬p] p)

·dec-false : (p? : ·Dec P) → ·¬ P → does p? ≡ false
·dec-false (false because  _ ) ¬p = refl
·dec-false (true  because [p]) ¬p = ·⊥-elim (¬p (·invert [p]))

·dec-yes : (p? : ·Dec P) → P → ∃ λ p′ → p? ≡ yes p′
·dec-yes p? p with ·dec-true p? p
·dec-yes (yes p′) p | refl = p′ , refl

·dec-no : (p? : ·Dec P) → ·¬ P → Σ (·¬ P) λ ¬p′ → p? ≡ no ¬p′
·dec-no p? ¬p with ·dec-false p? ¬p
·dec-no (no ¬p′) ¬p | refl = ¬p′ , refl

·dec-yes-irr : (p? : ·Dec P) → Irrelevant P → (p : P) → p? ≡ yes p
·dec-yes-irr p? irr p with ·dec-yes p? p
... | p′ , eq rewrite irr p p′ = eq

·map′ : (P → Q) → (Q → P) → ·Dec P → ·Dec Q
does  (·map′ P→Q Q→P p?)                   = does p?
proof (·map′ P→Q Q→P (true  because  [p])) = ofʸ (P→Q (·invert [p]))
proof (·map′ P→Q Q→P (false because [¬p])) = ofⁿ (·invert [¬p] ∘ Q→P)

module _ ⦃ _ : P ⁇ ⦄ where

  ·dec : ·Dec P
  ·dec = Dec⇒·Dec dec

  ·auto : ⦃ ·True ·dec ⦄ → P
  ·auto ⦃ pr ⦄ = ·toWitness pr

  ·contradict : ∀ {X : Type} {pr : ·False ·dec} → P → X
  ·contradict {pr = pr} = ·⊥-elim ∘ ·toWitnessFalse pr

·¿_¿ : ∀ (X : Type ℓ) → ⦃ X ⁇ ⦄ → ·Dec X
·¿ _ ¿ = ·dec

private variable A : Type ℓ; B : Type ℓ′; C : Type ℓ″

·Decidable¹ : Pred (Pred A ℓ) _
·Decidable¹ P = ∀ x → ·Dec (P x)

·dec¹ : ∀ {A : Type ℓ} {P : Pred A ℓ′} → ⦃ P ⁇¹ ⦄ → ·Decidable¹ P
·dec¹ _ = ·dec

·¿_¿¹ : ∀ {A : Type ℓ} (P : Pred A ℓ′) → ⦃ P ⁇¹ ⦄ → ·Decidable¹ P
·¿ _ ¿¹ = ·dec¹

·Decidable² : Pred (REL A B ℓ) _
·Decidable² R = ∀ x y → ·Dec (R x y)

·dec² : ∀ {A B : Type ℓ} {_~_ : REL A B ℓ′} → ⦃ _~_ ⁇² ⦄ → ·Decidable² _~_
·dec² _ _ = ·dec

·¿_¿² : ∀ {A B : Type ℓ} (_~_ : REL A B ℓ′) → ⦃ _~_ ⁇² ⦄ → ·Decidable² _~_
·¿ _ ¿² = ·dec²

·Decidable³ : Pred (3REL A B C ℓ) _
·Decidable³ R = ∀ x y z → ·Dec (R x y z)

·dec³ : ∀ {A B C : Type ℓ} {_~_~_ : 3REL A B C ℓ′} → ⦃ _~_~_ ⁇³ ⦄ → ·Decidable³ _~_~_
·dec³ _ _ _ = ·dec

·¿_¿³ : ∀ {A B C : Type ℓ} (_~_~_ : 3REL A B C ℓ′) → ⦃ _~_~_ ⁇³ ⦄ → ·Decidable³ _~_~_
·¿ _ ¿³ = ·dec³

infix -100 ·auto∶_
·auto∶_ : ∀ (X : Type ℓ) → ⦃ X ⁇ ⦄ → Type
·auto∶_ A = ·True ·¿ A ¿
