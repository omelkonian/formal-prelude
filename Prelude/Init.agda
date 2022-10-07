module Prelude.Init where

module SetAsType where
  open import Agda.Primitive using () renaming (Set to Type) public

-- ** Universes
module Lvl where
  open import Level public
open import Level public
  using (Level; 0ℓ; Setω)
  renaming (suc to lsuc; _⊔_ to _⊔ₗ_)
1ℓ = lsuc 0ℓ
2ℓ = lsuc 1ℓ
3ℓ = lsuc 2ℓ
4ℓ = lsuc 3ℓ
variable ℓ ℓ′ ℓ″ ℓ‴ ℓ₀ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

Set[_↝_] : ∀ ℓ ℓ′ → Set (lsuc ℓ ⊔ₗ lsuc ℓ′)
Set[ ℓ ↝ ℓ′ ] = Set ℓ → Set ℓ′

Set↑ : Setω
Set↑ = ∀ {ℓ} → Set[ ℓ ↝ ℓ ]

-- ** Equality
open import Relation.Binary.PropositionalEquality public
  using ( _≡_; _≢_; refl; sym; ≢-sym; trans; cong; subst; inspect; _≗_
        ; module ≡-Reasoning
        ; setoid )
  renaming ([_] to ≡[_])

-- ** Functions
open import Function public
  using ( id; const; constᵣ
        ; _∘_; flip; _$_; _$!_; _$-; _|>_; case_return_of_
        ; _∘′_; _∘₂_; _$′_; _$!′_; _|>′_; case_of_
        ; _∋_; _on_; typeOf; it
        )
module Fun where
  open import Function public
  module Inv where
    open import Function.Inverse public
  module Eq where
    open import Function.Equality public
  module Equiv where
    open import Function.Equivalence public
open import Function.Definitions public
  using (Congruent; Injective; Surjective; Bijective; Inverseˡ; Inverseʳ; Inverseᵇ)
module _ {a b} {A : Set a} {B : Set b} where
  open import Function.Definitions {A = A} {B = B} _≡_ _≡_ public
    using ()
    renaming
      ( Congruent to Congruent≡; Injective to Injective≡
      ; Surjective to Surjective≡; Bijective to Bijective≡
      ; Inverseˡ to Inverse≡ˡ; Inverseʳ to Inverse≡ʳ; Inverseᵇ to Inverse≡ᵇ
      )
open import Function.Bundles public
  using (module Injection; _↣_)

-- forward composition (= kleene composition of `Monad Id`)
infixr 0 _>≡>_
_>≡>_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} → (A → B) → (B → C) → A → C
f >≡> g = g ∘ f

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
  using (Σ; Σ-syntax; _,_; proj₁; proj₂; ∃; ∃-syntax; _×_; _,′_; <_,_>; curry; uncurry; -,_)
module Product where
  open import Data.Product public
  open import Data.Product.Properties public

open import Data.Sum public
  using (_⊎_; inj₁; inj₂; isInj₁; isInj₂)
module Sum where
  open import Data.Sum public
  open import Data.Sum.Properties public

open import Data.These public
  using (These; this; that; these)
module ∣These∣ where
  open import Data.These public
  open import Data.These.Properties public

open import Data.Bool  public
  using (Bool; true; false; not; if_then_else_; _∧_; _∨_; T)
open import Data.Bool.Properties public
  using (T?)
module B where
  open import Data.Bool  public
  open import Data.Bool.Properties public
  open import Data.Bool.Show public

open import Data.Nat public
  using (ℕ; suc; zero; _+_; _*_; _∸_; _⊔_; _⊓_; s≤s; z≤n)
open import Data.Nat.Properties public
  using (module ≤-Reasoning)
module Nat where
  open import Data.Nat public
  open import Data.Nat.Properties public
  open import Data.Nat.Show public
  module Ord where
    open import Data.Nat public using (_≤_; _<_; _≥_; _>_; _≤?_; _<?_; _≥?_; _>?_)
  module Ind where
    open import Data.Nat.Induction public

open import Data.Integer public
  using (ℤ; +_)
module Integer where
  open import Data.Integer public
  open import Data.Integer.Properties public

open import Data.Float public
  using (Float)
module Float where
  open import Data.Float public
  open import Data.Float.Properties public

open import Data.Fin public
  using (Fin; #_)
  renaming (suc to fsuc; zero to fzero)
open import Data.Fin.Patterns public
  using (0F; 1F; 2F; 3F; 4F; 5F; 6F; 7F; 8F; 9F)
module F where
  open import Data.Fin public
  open import Data.Fin.Properties public

open import Data.Word public
  using (Word64)
module Word where
  open import Data.Word public
  open import Data.Word.Properties public

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
  using (Maybe; just; nothing; Is-just; Is-nothing; maybe; maybe′; fromMaybe)
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
  using ( List; _∷_; []; [_]; _∷ʳ_; map; filter; concat; concatMap; length; _++_; foldl; foldr
        ; upTo; applyUpTo; mapMaybe; all; any; and; or; partitionSums; zip; unzip; sum; null; allFin
        ; take; drop; takeWhile; dropWhile
        )
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
  using (List⁺; _∷_; _∷⁺_; _⁺∷ʳ_ ; _⁺++_; _++⁺_; _⁺++⁺_)
  renaming ([_] to [_]⁺)
open import Data.List.Membership.Propositional public
  using ({-mapWith∈;-} find; lose)
open import Data.List.Relation.Unary.Any public
  using (Any; here; there; any?)
open import Data.List.Relation.Unary.All public
  using (All; _∷_; []; all?)
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
open import Data.List.Relation.Ternary.Interleaving public
  using (Interleaving; [])


-- ** Relations
module Nullary where
  open import Relation.Nullary public
  open import Relation.Nullary.Negation public
open import Relation.Nullary public
  using (¬_; Dec; yes; no; does; _because_; ofʸ; ofⁿ; Irrelevant; recompute)
open import Relation.Nullary.Negation public
  using (¬?; contradiction)
open import Relation.Nullary.Decidable public
  using ( ⌊_⌋; isNo; isYes; True; False
        ; toWitness; fromWitness; toWitnessFalse; fromWitnessFalse
        ; dec-yes; dec-no; dec-true; dec-false; dec-yes-irr
        ; isYes≗does
        )
open import Relation.Nullary.Implication public
  using (_→-dec_)
open import Relation.Nullary.Sum public
  using (_⊎-dec_)
open import Relation.Nullary.Product public
  using (_×-dec_)

module Unary where
  open import Relation.Unary public
open import Relation.Unary public
  using (Pred)
  renaming (Decidable to Decidable¹; _⇒_ to _⇒¹_; _⊆_ to _⊆¹_)

open import Relation.Binary public
  using ( REL; Rel; Reflexive; Irreflexive; Symmetric; Antisymmetric; Trans; Transitive; Total
        ; _⟶_Respects_; _Respects_; _Respectsʳ_; _Respectsˡ_; _Respects₂_
        ; DecidableEquality; IsEquivalence; Setoid)
  renaming (Decidable to Decidable²; _⇒_ to _⇒²_; _⇔_ to _⇔²_)
module PropEq where
  open import Relation.Binary.PropositionalEquality public
module Binary where
  open import Relation.Binary.Core public
  open import Relation.Binary.Definitions public
  module _ {A : Set ℓ} where
    open import Relation.Binary.Structures (_≡_ {A = A}) public
  open import Relation.Binary.Bundles public

module Ternary where
  open import Relation.Ternary public
open import Relation.Ternary public
  renaming (_⇒_ to _⇒³_; _⇔_ to _⇔³_; _=[_]⇒_ to _=[_]⇒³_
           ; _Preserves_⟶_ to _Preserves³_⟶_; _Preserves_⟶_⟶_ to _Preserves³_⟶_⟶_
           ; Reflexive to Reflexive³; Decidable to Decidable³; WeaklyDecidable to WeaklyDecidable³
           ; Irrelevant to Irrelevant³; Recomputable to Recomputable³; Universal to Universal³
           ; NonEmpty to NonEmpty³
           )
-- ** Algebra
open import Algebra public
  using (Op₁; Op₂; Opₗ; Opᵣ)
module Alg {a ℓ} {A : Set a} (_~_ : Rel A ℓ) where
  open import Algebra.Definitions {A = A} _~_ public
module Alg≡ {a} {A : Set a} where
  open import Algebra.Definitions {A = A} _≡_ public

-- ** Induction
open import Induction.WellFounded public
  using (WellFounded; Acc; acc)
module WF where
  open import Induction.WellFounded public

-- ** Reflection
module Meta where
  open import Agda.Builtin.Reflection public
    using (onlyReduceDefs; dontReduceDefs)
  open import Reflection public
    hiding (_≟_; _>>_; _>>=_; return; visibility)

  open import Reflection.Term public
    hiding ( _≟-AbsTerm_; _≟-AbsType_; _≟-ArgTerm_; _≟-ArgType_; _≟-Args_; _≟-Clause_
           ; _≟-Clauses_; _≟_; _≟-Sort_; _≟-Pattern_ )

  open import Reflection.Argument public
    using (unArg)
  open import Reflection.Argument.Visibility public
    using (Visibility)
  open import Reflection.Argument.Information public
    using (visibility)
  module Argument where
    open import Reflection.Argument public
    open import Reflection.Argument.Visibility public
    open import Reflection.Argument.Information public hiding (_≟_)

  open import Reflection.Abstraction public
    using (unAbs)
  module Abstraction where
    open import Reflection.Abstraction public

  open import Reflection.Meta public
    using (Meta)
  module Meta where
    open import Reflection.Meta public

  module Show where
    open import Reflection.Show public


-- ** Shorthands
Pred₀ Rel₀ 3Rel₀ : ∀ {ℓ} → Set ℓ → Set (1ℓ ⊔ₗ ℓ)
Pred₀ A = Pred A 0ℓ
Rel₀  A = Rel  A 0ℓ
3Rel₀ A = 3Rel A 0ℓ
