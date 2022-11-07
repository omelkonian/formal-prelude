module Prelude.Accessors where

open import Prelude.Init; open SetAsType

variable A B : Type; n : ℕ

-- general indexed version
record HasField′ (A : Type) (B : A → Type) : Type where
  constructor mkHasField
  field _∙ : (a : A) → B a
open HasField′ ⦃...⦄ public

-- simple non-indexed version
HasField : Op₂ Type
HasField A B = HasField′ A (const B)

-- instance
--   List-num : HasField (List A) ℕ
--   List-num ._∙ = length
-- private _ = [ "single" ] ∙ ≡ 1 ∋ refl

-- Deriving
AccessorTy : Type → (Type → Type)
AccessorTy = flip HasField

Accessor : Type → Type₁
Accessor B = ∀ {A} → ⦃ HasField A B ⦄ → A → B

AccessorBuilder : Type → Type₁
AccessorBuilder B = ∀ {A} → (A → B) → HasField A B

open import Prelude.Tactics
open import Prelude.Generics hiding (_∙)
open import Prelude.Monad
open Meta
genAccessor : Name → Name → Name → Name → TC ⊤
genAccessor ty f mk B = do
  declareDef (vArg ty) unknown
  defineFun ty [ ⟦⇒ quote AccessorTy ∙⟦ def B [] ⟧ ⟧ ]
  declareDef (vArg f) (quote Accessor ∙⟦ def B [] ⟧)
  defineFun f [ ⟦⇒ def (quote _∙) [] ⟧ ]
  declareDef (vArg mk) (quote AccessorBuilder ∙⟦ def B [] ⟧)
  defineFun mk [ ⟦⇒ con (quote mkHasField) [] ⟧ ]

-- HasNum = AccessorTy ℕ
-- _∙num  = Accessor ℕ ∋ _∙
-- ∙num=  = AccessorBuilder ℕ ∋ mkHasField
unquoteDecl HasNum _∙num ∙num=_ = genAccessor HasNum _∙num ∙num=_ (quote ℕ)
private
  instance
    List-num : HasNum (List A)
    List-num = ∙num= length
  _ = [ "single" ] ∙    ≡ 1 ∋ refl
  _ = [ "single" ] ∙num ≡ 1 ∋ refl

open import Prelude.Show
unquoteDecl HasStr _∙str ∙str=_ = genAccessor HasStr _∙str ∙str=_ (quote String)
private
  instance
    List-str : ⦃ Show A ⦄ → HasStr (List A)
    List-str = ∙str= show
  _ = [ "single" ] ∙    ≡ "{single}" ∋ refl
  _ = [ "single" ] ∙str ≡ "{single}" ∋ refl

--
