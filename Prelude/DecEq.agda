module Prelude.DecEq where

open import Function using (_∘_; _$_; case_of_; _∋_)

open import Data.Unit
  renaming (_≟_ to _≟⊤_)
open import Data.Product
  hiding (map)
open import Data.Product.Properties
  renaming (≡-dec to _≟×_)
open import Data.Sum
  hiding (map)
open import Data.Sum.Properties
  renaming (≡-dec to _≟⊎_)
open import Data.Bool
  renaming (_≟_ to _≟𝔹_)
open import Data.Nat
  renaming (_≟_ to _≟ℕ_)
open import Data.Integer
  renaming (_≟_ to _≟ℤ_)
open import Data.String
  renaming (_≟_ to _≟s_)
open import Data.List
  hiding (intersperse)
open import Data.List.Properties

open import Relation.Nullary using (yes; no; _because_; ofʸ; ofⁿ)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Prelude.Generics

record DecEq (A : Set) : Set where
  field
    _≟_ : Decidable {A = A} _≡_

open DecEq {{...}} public

private
  variable
    A B : Set

instance
  DecEq-⊤ : DecEq ⊤
  _≟_ {{DecEq-⊤}} = _≟⊤_

  DecEq-× : {{_ : DecEq A}} {{_ : DecEq B}} → DecEq (A × B)
  _≟_ {{DecEq-×}} = _≟_ ≟× _≟_

  DecEq-⊎ : {{_ : DecEq A}} {{_ : DecEq B}} → DecEq (A ⊎ B)
  _≟_ {{DecEq-⊎}} = _≟_ ≟⊎ _≟_

  DecEq-Bool : DecEq Bool
  _≟_ {{DecEq-Bool}} = _≟𝔹_

  DecEq-ℕ : DecEq ℕ
  _≟_ {{DecEq-ℕ}} = _≟ℕ_

  DecEq-ℤ : DecEq ℤ
  _≟_ {{DecEq-ℤ}} = _≟ℤ_

  DecEq-String : DecEq String
  _≟_ {{DecEq-String}} = _≟s_

  DecEq-List : {{_ : DecEq A}} → DecEq (List A)
  _≟_ {{DecEq-List}} = ≡-dec _≟_

open import Reflection hiding (_≟_)

-- e.g. Decidable {A = X} _≡_ ↝ X
extractName : Type → TC Name
extractName (def _ (arg _ _ ∷ arg _ (def x _) ∷ _)) = return x
extractName _ = error "impossible"

deriveEq : Definition → TC Term
deriveEq (record-type _ fs) =
  return $ `λ⟦ "r" ∣ "r′" ⟧⇒ go fs
  where
    pattern `yes x  = quote _because_ ◆⟦ quote true ◆  ∣ quote ofʸ ◆⟦ x ⟧ ⟧
    pattern ``yes x = quote _because_ ◇⟦ quote true ◇  ∣ quote ofʸ ◇⟦ x ⟧ ⟧
    pattern `no x   = quote _because_ ◆⟦ quote false ◆ ∣ quote ofⁿ ◆⟦ x ⟧ ⟧
    pattern ``no x  = quote _because_ ◇⟦ quote false ◇ ∣ quote ofⁿ ◇⟦ x ⟧ ⟧

    go : List (Arg Name) → Term
    go [] = `yes (quote refl ◆)
    go (arg (arg-info _ irrelevant) _ ∷ args) = go args
    go (arg (arg-info _ relevant)   n ∷ args) =
      quote case_of_
        ∙⟦ quote _≟_ ∙⟦ n ∙⟦ # 1 ⟧ ∣ n ∙⟦ # 0 ⟧ ⟧
         ∣ `λ⟦ ``no (Pattern.var "¬p")
             ⇒ `no (`λ⟦ (quote refl ◇) ⇒ (# 0 ⟦ quote refl ◆ ⟧) ⟧)
             ∣ ``yes (quote refl ◇)
             ⇒ go args
             ⟧
         ⟧

deriveEq _ = error "impossible"

macro
  {- *** Recursively decides equality of each record field, i.e.
     R := record {f₁ = _; ... fₙ = _}
     λ (r : R) (r′ : R) →
       case R.f₁ r ≟ R.f₁ r′ of λ
         { (no ¬p)    → no λ{ refl → ¬p refl }
         ; (yes refl) → ⋯
           ⋮
           case R.fₙ r ≟ R.fₙ r′ of λ
             { (no ¬p) → no λ{ refl → ¬p refl }
             ; (yes refl) → yes refl } }
  -}
  derive-DecEq : Term → TC ⊤
  derive-DecEq hole = do
    goal ← inferType hole
    n ← extractName goal
    print⊤ (showName n)
    d ← getDefinition n
    print⊤ (showDefinition d)
    t ← deriveEq d
    print⊤ (showTerm t)
    unify hole t

-- ** Example
private
  record R⁰ : Set where

  record R¹ : Set where
    field
      x : ℕ

  record R² : Set where
    field
      x : ℕ × ℤ
      y : ⊤ ⊎ Bool

  instance
    f : DecEq R⁰
    f ._≟_ = derive-DecEq

    g : DecEq R¹
    g ._≟_ = derive-DecEq

    h : DecEq R²
    h ._≟_ = derive-DecEq
