{-# OPTIONS --safe #-}
module Prelude.Accessors where

open import Prelude.Init; open SetAsType
open import Prelude.Monad
open import Prelude.Generics.Core hiding (_∙)

-- general indexed version
record HasField′ (A : Type) (B : A → Type) : Type where
  constructor mkHasField
  field _∙ : (a : A) → B a
open HasField′ ⦃...⦄ public

-- simple non-indexed version
HasField : Op₂ Type
HasField A B = HasField′ A (const B)

-- e.g.
-- instance
--   List-num : HasField (List A) ℕ
--   List-num ._∙ = length
-- private _ = [ "single" ] ∙ ≡ 1 ∋ refl

-- ** deriving

AccessorTy : Type → (Type → Type)
AccessorTy = flip HasField

Accessor : Type → Type₁
Accessor B = ∀ {A} → ⦃ HasField A B ⦄ → A → B

AccessorBuilder : Type → Type₁
AccessorBuilder B = ∀ {A} → (A → B) → HasField A B

open Meta

genAccessor : Name → Name → Name → Name → TC ⊤
genAccessor ty f mk B = do
  declareDef (vArg ty) unknown
  defineFun ty [ ⟦⇒ quote AccessorTy ∙⟦ def B [] ⟧ ⟧ ]
  declareDef (vArg f) (quote Accessor ∙⟦ def B [] ⟧)
  defineFun f [ ⟦⇒ def (quote _∙) [] ⟧ ]
  declareDef (vArg mk) (quote AccessorBuilder ∙⟦ def B [] ⟧)
  defineFun mk [ ⟦⇒ con (quote mkHasField) [] ⟧ ]
--
