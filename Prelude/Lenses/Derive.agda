{-# OPTIONS -v Lens:100 #-}
module Prelude.Lenses.Derive where

open import Prelude.Init
open Meta
open import Prelude.Generics
open Debug ("Lens" , 100)
open import Prelude.Show
open import Prelude.Semigroup
open import Prelude.Monad

open import Prelude.Lenses.Core

deriveLenses : Name → List (Name × Name × Name × Name) → TC ⊤
deriveLenses n lns = do
  print "**************************"
  print $ "Deriving lenses for " ◇ show n
  d@(record-type _ fs) ← getDefinition n
    where _ → error "Not a record type"
  print $ "fields: " ◇ show fs
  let fs = vArgs fs
  return⊤ $ forM (zip fs lns) $ λ where (f , (ln , gn , sn , mn)) → do
    (pi _ (abs _ fTy)) ← getType f
      where _ → error "Not a field type (should be `<RECORD> → <FIELD>`)."
    genSimpleDef ln (quote Lens ∙⟦ n ∙ ∣ fTy ⟧) $
     mkRecord ( (quote Lens.get , f ∙)
              ∷ (quote Lens.set , `λ⟦ "r" ∣ "x′" ⇒ updateField fs (♯ 1) f (♯ 0) ⟧)
              ∷ [])
    genSimpleDef gn (quote Getter ∙⟦ n ∙ ∣ fTy ⟧) $
      quote Lens.get ∙⟦ ln ∙ ⟧
    genSimpleDef sn (quote Setter ∙⟦ n ∙ ∣ fTy ⟧) $
      quote Lens.set ∙⟦ ln ∙ ⟧
    genSimpleDef mn (quote Modifier ∙⟦ n ∙ ∣ fTy ⟧) $
      quote Lens.modify ∙⟦ ln ∙ ⟧

--------------------------
-- Example

private
  record R₀ : Set where
    field y : String
  open R₀
  unquoteDecl 𝕪 _∙y _∙y=_ _∙y↝_
    = deriveLenses (quote R₀)
      [ (𝕪 , _∙y , _∙y=_ , _∙y↝_) ]
  infixl 10 _∙y=_ _∙y↝_

  _ : record {y = "test"} ∙y ≡ "test"
  _ = refl

  _ : (record {y = "test"} ∙y= "TEST") ∙y ≡ "TEST"
  _ = refl

  record R : Set where
    field x  : ℕ
          r  : R₀
  open R
  unquoteDecl 𝕩 _∙x _∙x=_ _∙x↝_
              𝕣 _∙r _∙r=_ _∙r↝_
    = deriveLenses (quote R)
      ( (𝕩 , _∙x , _∙x=_ , _∙x↝_)
      ∷ (𝕣 , _∙r , _∙r=_ , _∙r↝_)
      ∷ [])
  infixl 10 _∙x=_ _∙x↝_ _∙r=_ _∙r↝_

  _ : R → String
  _ = λ r → r ∙r ∙y

  _ : R → String → R
  -- _ = λ r y′ → r ∙r= ((r ∙r) ∙y= y′)
  _ = λ r y′ → r ∙r↝ (_∙y= y′)

  _ : R → Op₁ String → R
  -- _ = λ r f → r ∙r= ((r ∙r) ∙y↝ f)
  _ = λ r f → r ∙r↝ (_∙y↝ f)
