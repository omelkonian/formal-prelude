-------------------------------------------------------------------------------------
-- List notation without having to use `nil/[]`,
-- achieved by implicitly coercing elements to singleton lists.

-- For a more general treatment, where we inject into arbitrary sums/variants
-- at the cost of worse type inference, see Prelude.Variants.
-------------------------------------------------------------------------------------
open import Prelude.Init; open SetAsType

module Prelude.Lists.NoNil where

private
  variable X A B : Type
  pattern 𝕃 = inj₁ refl; pattern ℝ = inj₂ refl

record List? (X A : Type) : Type₁ where
  field isList : (A ≡ X) ⊎ (A ≡ List X)
  syntax isList {X}{A} = A isListOf? X

  toL : A → List X
  toL with isList
  ... | 𝕃 = [_]
  ... | ℝ = id
  syntax toL {A = A} = toL[ A ]
open List? ⦃...⦄ public

infixr 4 _⊕_
_⊕_ : ⦃ List? X A ⦄ → ⦃ List? X B ⦄ → A → B → List X
_⊕_ {X}{A}{B} x y
  with A isListOf? X | B isListOf? X
... | 𝕃 | 𝕃 = x ∷ y ∷ []
... | 𝕃 | ℝ = x ∷ y
... | ℝ | 𝕃 = x ∷ʳ y
... | ℝ | ℝ = x ++ y

instance
  Pick𝕃 : List? X X
  Pick𝕃 = record {isList = 𝕃}

  Pickℝ : List? X (List X)
  Pickℝ = record {isList = ℝ}

test-variant : ⦃ List? X A ⦄ → A → List X
test-variant {X}{A}
  with A isListOf? X
... | 𝕃 = [_]
... | ℝ = id

open import Prelude.General; open MultiTest
_ = List ℕ
 ∋⋮ []
  ⋮ [ 0 ]
  ⋮ 0 ⊕ 1
  ⋮ 0 ⊕ [ 1 ]
  ⋮ [ 0 ] ⊕ 1
  ⋮ [ 0 ] ⊕ [ 1 ]
  ⋮ 0 ⊕ 1 ⊕ 2
  ⋮ 0 ⊕ 1 ⊕ [ 2 ]
  ⋮ 0 ⊕ [ 1 ] ⊕ 2
  ⋮ [ 0 ] ⊕ 1 ⊕ 2
  ⋮ 0 ⊕ [ 1 ] ⊕ [ 2 ]
  ⋮ [ 0 ] ⊕ [ 1 ] ⊕ 2
  ⋮ [ 0 ] ⊕ 1 ⊕ [ 2 ]
  ⋮ [ 0 ] ⊕ [ 1 ] ⊕ [ 2 ]
  ⋮∅
