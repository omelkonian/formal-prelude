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
A⟫B lens-∘ B⟫C = λ where
    .get → _∙c ∘ _∙b
    .set a c → a ∙b↝ (_∙c= c)
  where open Lens A⟫B renaming (get to _∙b; set to _∙b=_; modify to _∙b↝_)
        open Lens B⟫C renaming (get to _∙c; set to _∙c=_)

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
    field
      x : ℕ
      y : String
  open R₀
  unquoteDecl 𝕩 _∙x _∙x=_ _∙x↝_
              𝕪 _∙y _∙y=_ _∙y↝_
    = deriveLenses (quote R₀)
      ( (𝕩 , _∙x , _∙x=_ , _∙x↝_)
      ∷ (𝕪 , _∙y , _∙y=_ , _∙y↝_)
      ∷ [])
  infixl 10 _∙x=_ _∙x↝_ _∙y=_ _∙y↝_

  ex-record : R₀
  ex-record = record {x = 42; y = "test"}

  _ = ex-record ∙y ≡ "test"
    ∋ refl

  _ = (ex-record ∙y= "TEST") ∙y ≡ "TEST"
    ∋ refl

  _ = (ex-record ∙x= 422) ∙x ≡ 422
    ∋ refl

  _ = ex-record ∙y= "TEST"
                ∙x= 422
    ≡ record {x = 422; y = "TEST"}
    ∋ refl

  _ = ex-record ∙y↝ ("$" Str.++_)
                ∙x= 422
                ∙x↝ (_∸ 1)
    ≡ record {x = 421; y = "$test"}
    ∋ refl
