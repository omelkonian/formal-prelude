module Prelude.Lenses where

open import Prelude.Init
open import Prelude.Lenses.Core public
open import Prelude.Lenses.Derive public

private variable A B C : Set

lens-id : Lens A A
lens-id = λ where
  .get → id
  .set → λ _ → id

_lens-∘_ : Lens A B → Lens B C → Lens A C
A⟫B@(record {get = _∙b; set = _∙b≔_})
  lens-∘
  B⟫C@(record {get = _∙c; set = _∙c≔_})
     = λ where .get → _∙c ∘ _∙b
               .set a c → a ∙b↝ (_∙c≔ c)
 where _∙b↝_ = modify A⟫B
       _∙c↝_ = modify B⟫C

lens-×ˡ : Lens (A × B) A
lens-×ˡ = λ where
  .get → proj₁
  .set (a , b) a′ → (a′ , b)

lens-×ʳ : Lens (A × B) B
lens-×ʳ = λ where
  .get → proj₂
  .set (a , b) b′ → (a , b′)

-- lens-× : Lens A B
--        → Lens (A × C) (B × C)
-- lens-× A⟫B@(record {get = _∙b; set = _∙b≔_})
--      = λ where .get → {!!}
--                .set → {!!}
--  where _∙b↝_ = modify A⟫B

private
  record R₀ : Set where
    field y : String
  open R₀
  unquoteDecl 𝕪 _∙y _∙y=_ _∙y↝_
    = deriveLenses (quote R₀)
      [ (𝕪 , _∙y , _∙y=_ , _∙y↝_) ]
  infix 10 _∙y=_ _∙y↝_

  _ = record {y = "test"} ∙y ≡ "test"
    ∋ refl

  _ = (record {y = "test"} ∙y= "TEST") ∙y ≡ "TEST"
    ∋ refl
