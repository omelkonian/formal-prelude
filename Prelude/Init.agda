module Prelude.Init where

-- ** Universes
open import Level public
  using (Level; 0ℓ)
  renaming (suc to lsuc; _⊔_ to _⊔ₗ_)
1ℓ = lsuc 0ℓ
2ℓ = lsuc 1ℓ
3ℓ = lsuc 2ℓ
4ℓ = lsuc 3ℓ
variable ℓ ℓ′ ℓ″ ℓ‴ ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

-- ** Functions
open import Function public
  using ( id; const
        ; _∘_; flip; _$_; _$!_; _$-; _|>_; case_return_of_
        ; _∘′_; _$′_; _$!′_; _|>′_; case_of_
        ; _∋_; _on_; typeOf; it
        )
-- forward composition (= kleene composition of `Monad Id`)
_>≡>_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} → (A → B) → (B → C) → A → C
f >≡> g = g ∘ f

open import Function.Definitions public
  using (Injective)
open import Function.Bundles public
  using (module Injection; _↣_)
module Fun where
  open import Function public
  module Inv where
    open import Function.Inverse public
  module Eq where
    open import Function.Equality public
  module Equiv where
    open import Function.Equivalence public


-- ** Categories
open import Category.Functor public
  using (RawFunctor)
open import Category.Applicative public
  using (RawApplicative)
open import Category.Monad public
  using (RawMonad)

-- ** Data
open import Data.Empty public
  using (⊥; ⊥-elim)

open import Data.Unit public
  using (⊤; tt)
module Unit where
  open import Data.Unit public
  open import Data.Unit.Properties public

open import Data.Product public
  using (_×_; _,_; proj₁; proj₂; ∃; ∃-syntax; Σ; Σ-syntax; <_,_>; curry; uncurry; -,_; swap)
module Product where
  open import Data.Product public
  open import Data.Product.Properties public

open import Data.Sum public
  using (_⊎_; inj₁; inj₂; isInj₁; isInj₂)
module Sum where
  open import Data.Sum public
  open import Data.Sum.Properties public

open import Data.Bool  public
  using (Bool; true; false; not; if_then_else_; _∧_; _∨_; T)
open import Data.Bool.Properties public
  using (T?)
module B where
  open import Data.Bool  public
  open import Data.Bool.Properties public
  open import Data.Bool.Show public

open import Data.Nat public
  using ( ℕ; suc; zero; _+_; _*_; _∸_; _⊔_; _⊓_
        ; _≤_; s≤s; z≤n; _<_; _≥_; _>_; _≤?_; _<?_; _≥?_; _>?_ )
open import Data.Nat.Properties public
  using (module ≤-Reasoning)
module Nat where
  open import Data.Nat public
  open import Data.Nat.Properties public
  open import Data.Nat.Show public

open import Data.Integer public
  using (ℤ; +_)
module Integer where
  open import Data.Integer public
  open import Data.Integer.Properties public

open import Data.Fin public
  using (Fin; #_)
  renaming (suc to fsuc; zero to fzero)
open import Data.Fin.Patterns public
  using (0F; 1F; 2F; 3F; 4F; 5F; 6F; 7F; 8F; 9F)
module F where
  open import Data.Fin public
  open import Data.Fin.Properties public

open import Data.Char public
  using (Char)
module Ch where
  open import Data.Char public
  open import Data.Char.Properties public

open import Data.String public
  using (String; intersperse; parens; braces)
module Str where
  open import Data.String public

open import Data.Maybe public
  using (Maybe; just; nothing; Is-just; Is-nothing; maybe; maybe′)
module M where
  open import Data.Maybe public
  open import Data.Maybe.Properties public
  module All where
    open import Data.Maybe.Relation.Unary.All public
    open import Data.Maybe.Relation.Unary.All.Properties public
  module Any where
    open import Data.Maybe.Relation.Unary.Any public
    -- open import Data.Maybe.Relation.Unary.Any.Properties public
  module Cat where
    open import Data.Maybe.Categorical public

open import Data.Vec public
  using (Vec; _∷_; [])
module V where
  open import Data.Vec public
  open import Data.Vec.Properties public
  module All where
    open import Data.Vec.Relation.Unary.All public
    open import Data.Vec.Relation.Unary.All.Properties public
  module Any where
    open import Data.Vec.Relation.Unary.Any public
    open import Data.Vec.Relation.Unary.Any.Properties public
  module Cat where
    open import Data.Vec.Categorical public
  module Mem where
    open import Data.Vec.Membership.Propositional public
    open import Data.Vec.Membership.Propositional.Properties public
    -- open import Data.Vec.Membership.DecPropositional public

open import Data.List public
  using ( List; _∷_; []; [_]; _∷ʳ_; map; filter; concat; concatMap; length; _++_; take; drop; foldl; foldr
        ; upTo; applyUpTo; mapMaybe; all; any; and; or; partitionSums; zip; unzip; sum; null; allFin )
module L where
  open import Data.List public
  open import Data.List.Properties public
  module NE where
    open import Data.List.NonEmpty public
    open import Data.List.NonEmpty.Properties public
    module Cat where
      open import Data.List.NonEmpty.Categorical public
  module All where
    open import Data.List.Relation.Unary.All public
    open import Data.List.Relation.Unary.All.Properties public
  module Any where
    open import Data.List.Relation.Unary.Any public
    open import Data.List.Relation.Unary.Any.Properties public
  module Cat where
    open import Data.List.Categorical public
  module Mem where
    open import Data.List.Membership.Propositional public
    -- module Dec where
    --   open import Data.List.Membership.DecPropositional public
    open import Data.List.Membership.Propositional.Properties public
  module Uniq where
    open import Data.List.Relation.Unary.Unique.Propositional public
    open import Data.List.Relation.Unary.Unique.Propositional.Properties public
  module Perm where
    open import Data.List.Relation.Binary.Permutation.Propositional public
    open import Data.List.Relation.Binary.Permutation.Propositional.Properties public

open import Data.List.NonEmpty public
  using (List⁺; _∷_; _∷⁺_; _⁺++_; _++⁺_; _⁺++⁺_)
  renaming ([_] to [_]⁺)
open import Data.List.Membership.Propositional public
  using ({-mapWith∈;-} find; lose)
open import Data.List.Relation.Unary.Any public
  using (Any; here; there)
  renaming (any to any?)
open import Data.List.Relation.Unary.All public
  using (All; _∷_; [])
  renaming (all to all?)
open import Data.List.Relation.Unary.AllPairs public
  using (AllPairs; _∷_; []; allPairs?)
open import Data.List.Relation.Unary.Unique.Propositional public
  using (Unique)
open import Data.List.Relation.Binary.Subset.Propositional public
  using (_⊆_; _⊈_)
open import Data.List.Relation.Binary.Subset.Propositional.Properties public
  using (module ⊆-Reasoning)
open import Data.List.Relation.Binary.Disjoint.Propositional public
  using (Disjoint)
open import Data.List.Relation.Binary.Permutation.Propositional public
  using (_↭_; ↭-reflexive; ↭-sym; module PermutationReasoning)
  renaming (refl to ↭-refl; prep to ↭-prep; swap to ↭-swap; trans to ↭-trans)
open import Data.List.Relation.Binary.Pointwise public
  using (Pointwise; []; _∷_)
open import Data.List.Relation.Binary.Prefix.Heterogeneous public
  using (Prefix; []; _∷_)
open import Data.List.Relation.Binary.Suffix.Heterogeneous public
  using (Suffix; here; there)


-- ** Relations
open import Relation.Nullary public
  using (¬_; Dec; yes; no; does; _because_; ofʸ; ofⁿ; Irrelevant; recompute)
open import Relation.Nullary.Negation public
  using (¬?; contradiction)
open import Relation.Nullary.Decidable public
  using ( ⌊_⌋; isNo; isYes; True; False
        ; toWitness; fromWitness; toWitnessFalse; fromWitnessFalse
        ; dec-yes; dec-no; dec-true; dec-false; dec-yes-irr
        )
open import Relation.Nullary.Implication public
  using (_→-dec_)
open import Relation.Nullary.Sum public
  using (_⊎-dec_)
open import Relation.Nullary.Product public
  using (_×-dec_)
open import Relation.Unary public
  using (Pred)
  renaming (Decidable to Decidable¹)
open import Relation.Binary public
  using (Rel; Reflexive; Symmetric; Transitive; StrictTotalOrder; DecidableEquality; IsEquivalence; Setoid )
  renaming (Decidable to Decidable²)
open import Relation.Binary.PropositionalEquality public
  using ( _≡_; _≢_; refl; sym; ≢-sym; trans; cong; subst; inspect; _≗_
        ; module ≡-Reasoning
        ; setoid )
  renaming ([_] to ≡[_])
module PropEq where
  open import Relation.Binary.PropositionalEquality public

-- ** Algebra
open import Algebra public
  using (Op₁; Op₂; Opₗ; Opᵣ)
module Alg {a ℓ} {A : Set a} (_~_ : Rel A ℓ) where
  open import Algebra.Definitions {A = A} _~_ public
import Algebra.Definitions as A
module Alg≡ {a} {A : Set a} where
  open import Algebra.Definitions {A = A} _≡_ public

-- ** Induction
open import Induction.WellFounded public
  using (WellFounded; Acc; acc)
module WF where
  open import Induction.WellFounded public

-- ** Reflection
module Meta where
  open import Reflection public
    hiding (_≟_; _>>_; _>>=_; return)
  open import Reflection.Term public
    hiding (_≟-AbsTerm_; _≟-AbsType_; _≟-ArgTerm_; _≟-ArgType_; _≟-Args_; _≟-Clause_; _≟-Clauses_; _≟_; _≟-Sort_)
  open import Reflection.Argument public
    using (unArg)
  open import Reflection.Abstraction public
    using (unAbs)
  open import Reflection.Argument.Visibility public
    using (Visibility)

-- ** Shorthands
Pred₀ Rel₀ : ∀ {ℓ} → Set ℓ → Set (1ℓ ⊔ₗ ℓ)
Pred₀ A = Pred A 0ℓ
Rel₀  A = Rel  A 0ℓ
