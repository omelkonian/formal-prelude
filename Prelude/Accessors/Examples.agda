module Prelude.Accessors.Examples where

open import Prelude.Init; open SetAsType
open import Prelude.Show
open import Prelude.Accessors

private variable A : Type ℓ

-- e.g.
-- ```
-- HasNum = AccessorTy ℕ
-- _∙num  = Accessor ℕ ∋ _∙
-- ∙num=  = AccessorBuilder ℕ ∋ mkHasField
-- ```
unquoteDecl HasNum _∙num ∙num=_ = genAccessor HasNum _∙num ∙num=_ (quote ℕ)
private
  instance
    List-num : HasNum (List A)
    List-num = ∙num= length
  _ = [ "single" ] ∙    ≡ 1 ∋ refl
  _ = [ "single" ] ∙num ≡ 1 ∋ refl

unquoteDecl HasStr _∙str ∙str=_ = genAccessor HasStr _∙str ∙str=_ (quote String)
private
  instance
    List-str : ⦃ Show A ⦄ → HasStr (List A)
    List-str = ∙str= show
  _ = [ "single" ] ∙    ≡ "{single}" ∋ refl
  _ = [ "single" ] ∙str ≡ "{single}" ∋ refl
