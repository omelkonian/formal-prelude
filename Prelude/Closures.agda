module Prelude.Closures where

open import Prelude.Init
open import Prelude.General hiding (_⊢_)
open import Prelude.Setoid
open import Prelude.Decidable

-- labelled relations
LRel : Set ℓ × Set → (ℓ′ : Level) → Set (ℓ ⊔ₗ lsuc ℓ′)
LRel (A , L) ℓ = A → L → A → Set ℓ

LRel₀ : Set ℓ × Set → Set _
LRel₀ (A , L) = LRel (A , L) 0ℓ

unlabel : ∀ {A : Set ℓ} {L : Set} → LRel (A , L) ℓ′ → Rel A ℓ′
unlabel _—→[_]_ x y = ∃ λ α → x —→[ α ] y

infix 0 emitting_∶_ emit∶_
-- pattern emitting_∶_ = _,_

emitting_∶_ : ∀ {A : Set ℓ} {B : Pred A ℓ′} → (x : A) → B x → Σ A B
emitting_∶_ = _,_
emit∶_ = -,_

-- [RECOMMENDED] infix -1 _—→_

module LabelledReflexiveTransitiveClosure
  {A : Set ℓ} {L : Set} (_—[_]→_ : LRel (A , L) ℓ) where

  private
    variable
      x y z : A
      α α′ : L
      αs αs′ : List L

  -- left-biased
  infix  3 _∎
  infixr 2 _—→⟨_⟩_
  infix  1 begin_; pattern begin_ x = x
  infix -1 _—→_ _—[_]↠_ _—↠_ _—[_]↠⁺_ _—↠⁺_
  data _—[_]↠_ : LRel (A , List L) ℓ where
    _∎ : ∀ x → x —[ [] ]↠ x
    _—→⟨_⟩_ : ∀ x → x —[ α ]→ y → y —[ αs ]↠ z → x —[ α ∷ αs ]↠ z
  data _—[_]↠⁺_ : LRel (A , List L) ℓ where
    _—→⟨_⟩_ : ∀ x → x —[ α ]→ y → y —[ αs ]↠ z → x —[ α ∷ αs ]↠⁺ z

  _—→_  = unlabel _—[_]→_
  _—↠_  = unlabel _—[_]↠_
  _—↠⁺_ = unlabel _—[_]↠⁺_

  -- right-biased view
  _←[_]—_ : LRel (A , L) ℓ
  y ←[ α ]— x = x —[ α ]→ y

  -- infix  3 _∎
  infixr 2 _⟨_⟩←—_
  infix -1 _←—_ _↞[_]—_ _↞—_ _⁺↞[_]—_ _⁺↞—_
  data _↞[_]—_ : LRel (A , List L) ℓ where
    _∎ : ∀ x → x ↞[ [] ]— x
    _⟨_⟩←—_ : ∀ z → (z ←[ α ]— y) → (y ↞[ αs ]— x) → z ↞[ αs L.∷ʳ α ]— x
  data _⁺↞[_]—_ : LRel (A , List L) ℓ where
    _⟨_⟩←—_ : ∀ z → (z ←[ α ]— y) → (y ↞[ αs ]— x) → z ⁺↞[ αs L.∷ʳ α ]— x

  _←—_  = unlabel _←[_]—_
  _↞—_  = unlabel _↞[_]—_
  _⁺↞—_ = unlabel _⁺↞[_]—_

  -- view correspondence
  infixr 2 _`—→⟨_⟩_
  _`—→⟨_⟩_ : ∀ x → y ←[ α ]— x → z ↞[ αs ]— y → z ↞[ α ∷ αs ]— x
  _ `—→⟨ st ⟩ _ ∎           = _ ⟨ st ⟩←— _ ∎
  _ `—→⟨ st ⟩ _ ⟨ st′ ⟩←— p = _ ⟨ st′ ⟩←— _ `—→⟨ st ⟩ p

  viewLeft : x —[ αs ]↠ y → y ↞[ αs ]— x
  viewLeft (_ ∎)          = _ ∎
  viewLeft (_ —→⟨ st ⟩ p) = _ `—→⟨ st ⟩ viewLeft p

  infixr 2 _`⟨_⟩←—_
  _`⟨_⟩←—_ : ∀ z → y —[ α ]→ z → x —[ αs ]↠ y → x —[ αs ∷ʳ α ]↠ z
  _ `⟨ st ⟩←— (_ ∎)           = _ —→⟨ st ⟩ _ ∎
  _ `⟨ st ⟩←— (_ —→⟨ st′ ⟩ p) = _ —→⟨ st′ ⟩ (_ `⟨ st ⟩←— p)

  viewRight : y ↞[ αs ]— x → x —[ αs ]↠ y
  viewRight (_ ∎)          = _ ∎
  viewRight (_ ⟨ st ⟩←— p) = _ `⟨ st ⟩←— viewRight p

  view↔ : (x —[ αs ]↠ y) ↔ (y ↞[ αs ]— x)
  view↔ = viewLeft , viewRight

-- [BUG] this needs to be placed above the simpler `ReflexiveTransitiveClosure`:
-- Agda complains that we're re-definining `_—→⟨_⟩_`, although they should leave in different namespaces.
module UpToLabelledReflexiveTransitiveClosure
  {A : Set ℓ} {L : Set} (_—[_]→_ : LRel (A , L) ℓ) ⦃ _ : ISetoid A ⦄ where

  open LabelledReflexiveTransitiveClosure _—[_]→_ public
    using (_—→_; _←[_]—_; _←—_)

  private
    variable
      x y z x′ y′ z′ : A
      α α′ : L
      αs αs′ : List L

  -- left-biased
  infix  3 _∎
  infixr 2 _—→⟨_⟩_⊢_
  infix  1 begin_; pattern begin_ x = x
  infix -1 _—↠_ _—[_]↠_ _—↠⁺_ _—[_]↠⁺_
  data _—[_]↠_ : LRel (A , List L) ℓ where
    _∎ : ∀ x → x —[ [] ]↠ x
    _—→⟨_⟩_⊢_ : ∀ x {x′ y y′ z}
      → x′ —[ α ]→ y′
      → x ≈ x′ × y ≈ y′
      → y —[ αs ]↠ z
        --———————————————
      → x —[ α ∷ αs ]↠ z
  data _—[_]↠⁺_ : LRel (A , List L) ℓ where
    _—→⟨_⟩_⊢_ : ∀ x {x′ y y′ z}
      → x′ —[ α ]→ y′
      → x ≈ x′ × y ≈ y′
      → y —[ αs ]↠ z
        --———————————————
      → x —[ α ∷ αs ]↠⁺ z
  _—↠_  = unlabel _—[_]↠_
  _—↠⁺_ = unlabel _—[_]↠⁺_

  -- right-biased view
  -- infix  3 _∎
  infixr 2 _⟨_⟩←—_⊢_
  infix -1 _↞[_]—_ _↞—_ _⁺↞[_]—_ _⁺↞—_
  data _↞[_]—_ : LRel (A , List L) ℓ where
    _∎ : ∀ x → x ↞[ [] ]— x
    _⟨_⟩←—_⊢_ : ∀ z {z′ y y′ x}
      → (z′ ←[ α ]— y′)
      → z ≈ z′ × y ≈ y′
      → (y ↞[ αs ]— x)
        --————————————————————
      → z ↞[ αs L.∷ʳ α ]— x
  data _⁺↞[_]—_ : LRel (A , List L) ℓ where
    _⟨_⟩←—_⊢_ : ∀ z {z′ y y′ x}
      → (z′ ←[ α ]— y′)
      → z ≈ z′ × y ≈ y′
      → (y ↞[ αs ]— x)
        --————————————————————
      → z ⁺↞[ αs L.∷ʳ α ]— x
  _↞—_  = unlabel _↞[_]—_
  _⁺↞—_ = unlabel _⁺↞[_]—_

  -- automatic-proof version
  module _ ⦃ _ : IDecSetoid A ⦄ where

    infixr 2 _—→⟨_⟩_ _⟨_⟩←—_

    _—→⟨_⟩_ : ∀ (x : A)
      → x′ —[ α ]→ y′
      → y —[ αs ]↠ z
      → {True $ x ≈? x′}
      → {True $ y ≈? y′}
        --————————————————
      → x —[ α ∷ αs ]↠ z
    (x —→⟨ x′→y′ ⟩ y↠z) {p₁} {p₂} = x —→⟨ x′→y′ ⟩ toWitness p₁ , toWitness p₂ ⊢ y↠z

    _⟨_⟩←—_ : ∀ z
      → z′ ←[ α ]— y′
      → y ↞[ αs ]— x
      → {True $ z ≈? z′}
      → {True $ y ≈? y′}
        --——————————————————
      → z ↞[ αs L.∷ʳ α ]— x
    (z ⟨ z′←y′ ⟩←— y↞x) {p₁} {p₂} = z ⟨ z′←y′ ⟩←— toWitness p₁ , toWitness p₂ ⊢ y↞x

  -- view correspondence
  infixr 2 _`—→⟨_⟩_⊢_
  _`—→⟨_⟩_⊢_ : ∀ (x : A) {x′ y y′ x}
    → y′ ←[ α ]— x′
    → x ≈ x′ × y ≈ y′
    → z ↞[ αs ]— y
    → z ↞[ α ∷ αs ]— x
  _ `—→⟨ st ⟩ eq ⊢ _ ∎                  = _ ⟨ st ⟩←— swap eq ⊢ _ ∎
  x `—→⟨ st ⟩ eq ⊢ _ ⟨ st′ ⟩←— eq′ ⊢ tr = _ ⟨ st′ ⟩←— eq′ ⊢ (x `—→⟨ st ⟩ eq ⊢ tr)

  viewLeft : x —[ αs ]↠ y → y ↞[ αs ]— x
  viewLeft (_ ∎)          = _ ∎
  viewLeft (c —→⟨ st ⟩ eq ⊢ p) = c `—→⟨ st ⟩ eq ⊢ viewLeft p

  infixr 2 _`⟨_⟩←—_⊢_
  _`⟨_⟩←—_⊢_ : ∀ z {z′ y y′ x}
    → y′ —[ α ]→ z′
    → z ≈ z′ × y ≈ y′
    → x —[ αs ]↠ y
    → x —[ αs ∷ʳ α ]↠ z
  _ `⟨ st ⟩←— eq ⊢ (_ ∎)                 = _ —→⟨ st ⟩ swap eq ⊢ _ ∎
  _ `⟨ st ⟩←— eq ⊢ (_ —→⟨ st′ ⟩ eq′ ⊢ p) = _ —→⟨ st′ ⟩ eq′ ⊢ (_ `⟨ st ⟩←— eq ⊢ p)

  viewRight : y ↞[ αs ]— x → x —[ αs ]↠ y
  viewRight (_ ∎)          = _ ∎
  viewRight (_ ⟨ st ⟩←— eq ⊢ p) = _ `⟨ st ⟩←— eq ⊢ viewRight p

  view↔ : (x —[ αs ]↠ y) ↔ (y ↞[ αs ]— x)
  view↔ = viewLeft , viewRight

module ReflexiveTransitiveClosure {A : Set ℓ} (_—→_ : Rel A ℓ) where

  private variable x y z : A

  -- left-biased
  infix  3 _∎
  infixr 2 _—→⟨_⟩_
  infix  1 begin_; pattern begin_ x = x
  infix -1 _—↠_ _—↠⁺_
  data _—↠_ : Rel A ℓ where
    _∎ : ∀ x → x —↠ x
    _—→⟨_⟩_ : ∀ x → x —→ y → y —↠ z → x —↠ z
  data _—↠⁺_ : Rel A ℓ where
    _—→⟨_⟩_ : ∀ x → x —→ y → y —↠ z → x —↠⁺ z


  -- right-biased view
  _←—_ = flip _—→_

  -- infix  3 _∎
  infixr 2 _⟨_⟩←—_
  infix -1 _←—_ _↞—_ _⁺↞—_
  data _↞—_ : Rel A ℓ where
    _∎ : ∀ x → x ↞— x
    _⟨_⟩←—_ : ∀ z → z ←— y → y ↞— x → z ↞— x
  data _⁺↞—_ : Rel A ℓ where
    _⟨_⟩←—_ : ∀ z → z ←— y → y ↞— x → z ⁺↞— x

  -- view correspondence
  infixr 2 _`—→⟨_⟩_
  _`—→⟨_⟩_ : ∀ x → y ←— x → z ↞— y → z ↞— x
  _ `—→⟨ st ⟩ _ ∎           = _ ⟨ st ⟩←— _ ∎
  _ `—→⟨ st ⟩ _ ⟨ st′ ⟩←— p = _ ⟨ st′ ⟩←— _ `—→⟨ st ⟩ p

  viewLeft : x —↠ y → y ↞— x
  viewLeft (_ ∎)          = _ ∎
  viewLeft (_ —→⟨ st ⟩ p) = _ `—→⟨ st ⟩ viewLeft p

  infixr 2 _`⟨_⟩←—_
  _`⟨_⟩←—_ : ∀ z → y —→ z → x —↠ y → x —↠ z
  _ `⟨ st ⟩←— (_ ∎)           = _ —→⟨ st ⟩ _ ∎
  _ `⟨ st ⟩←— (_ —→⟨ st′ ⟩ p) = _ —→⟨ st′ ⟩ (_ `⟨ st ⟩←— p)

  viewRight : y ↞— x → x —↠ y
  viewRight (_ ∎)          = _ ∎
  viewRight (_ ⟨ st ⟩←— p) = _ `⟨ st ⟩←— viewRight p

  view↔ : (x —↠ y) ↔ (y ↞— x)
  view↔ = viewLeft , viewRight

module UpToReflexiveTransitiveClosure
  {A : Set ℓ} (_—→_ : Rel A ℓ) ⦃ _ : ISetoid A ⦄ where

  open ReflexiveTransitiveClosure _—→_ public
    using (_←—_)

  private variable x y z x′ y′ z′ : A

  -- left-biased
  infix  3 _∎
  infixr 2 _—→⟨_⟩_⊢_
  infix  1 begin_; pattern begin_ x = x
  infix -1 _—↠_ _—↠⁺_
  data _—↠_ : Rel A ℓ where
    _∎ : ∀ x → x —↠ x
    _—→⟨_⟩_⊢_ : ∀ x {x′ y y′ z}
      → x′ —→ y′
      → x ≈ x′ × y ≈ y′
      → y —↠ z
        --———————————————
      → x —↠ z
  data _—↠⁺_ : Rel A ℓ where
    _—→⟨_⟩_⊢_ : ∀ x {x′ y y′ z}
      → x′ —→ y′
      → x ≈ x′ × y ≈ y′
      → y —↠ z
        --———————————————
      → x —↠⁺ z

  -- right-biased view
  -- infix  3 _∎
  infixr 2 _⟨_⟩←—_⊢_
  infix -1 _↞—_ _⁺↞—_
  data _↞—_ : Rel A ℓ where
    _∎ : ∀ x → x ↞— x
    _⟨_⟩←—_⊢_ : ∀ z {z′ y y′ x}
      → (z′ ←— y′)
      → z ≈ z′ × y ≈ y′
      → (y ↞— x)
        --————————————————————
      → z ↞— x
  data _⁺↞—_ : Rel A ℓ where
    _⟨_⟩←—_⊢_ : ∀ z {z′ y y′ x}
      → (z′ ←— y′)
      → z ≈ z′ × y ≈ y′
      → (y ↞— x)
        --————————————————————
      → z ⁺↞— x

  -- automatic-proof version
  module _ ⦃ ds : IDecSetoid A ⦄ where

    infixr 2 _—→⟨_⟩_ _⟨_⟩←—_

    _—→⟨_⟩_ : ∀ x
      → x′ —→ y′
      → y —↠ z
      → {True $ x ≈? x′}
      → {True $ y ≈? y′}
        --————————————————
      → x —↠ z
    (x —→⟨ x′→y′ ⟩ y↠z) {p₁} {p₂} = x —→⟨ x′→y′ ⟩ toWitness p₁ , toWitness p₂ ⊢ y↠z

    _⟨_⟩←—_ : ∀ z
      → z′ ←— y′
      → y ↞— x
      → {True $ z ≈? z′}
      → {True $ y ≈? y′}
        --——————————————————
      → z ↞— x
    (z ⟨ z′←y′ ⟩←— y↞x) {p₁} {p₂} = z ⟨ z′←y′ ⟩←— toWitness p₁ , toWitness p₂ ⊢ y↞x

  -- view correspondence
  infixr 2 _`—→⟨_⟩_⊢_
  _`—→⟨_⟩_⊢_ : ∀ (x : A) {x′ y y′ x}
    → y′ ←— x′
    → x ≈ x′ × y ≈ y′
    → z ↞— y
    → z ↞— x
  _ `—→⟨ st ⟩ eq ⊢ _ ∎                  = _ ⟨ st ⟩←— swap eq ⊢ _ ∎
  x `—→⟨ st ⟩ eq ⊢ _ ⟨ st′ ⟩←— eq′ ⊢ tr = _ ⟨ st′ ⟩←— eq′ ⊢ (x `—→⟨ st ⟩ eq ⊢ tr)

  viewLeft : x —↠ y → y ↞— x
  viewLeft (_ ∎)          = _ ∎
  viewLeft (c —→⟨ st ⟩ eq ⊢ p) = c `—→⟨ st ⟩ eq ⊢ viewLeft p

  infixr 2 _`⟨_⟩←—_⊢_
  _`⟨_⟩←—_⊢_ : ∀ z {z′ y y′ x}
    → y′ —→ z′
    → z ≈ z′ × y ≈ y′
    → x —↠ y
    → x —↠ z
  _ `⟨ st ⟩←— eq ⊢ (_ ∎)                 = _ —→⟨ st ⟩ swap eq ⊢ _ ∎
  _ `⟨ st ⟩←— eq ⊢ (_ —→⟨ st′ ⟩ eq′ ⊢ p) = _ —→⟨ st′ ⟩ eq′ ⊢ (_ `⟨ st ⟩←— eq ⊢ p)

  viewRight : y ↞— x → x —↠ y
  viewRight (_ ∎)          = _ ∎
  viewRight (_ ⟨ st ⟩←— eq ⊢ p) = _ `⟨ st ⟩←— eq ⊢ viewRight p

  view↔ : (x —↠ y) ↔ (y ↞— x)
  view↔ = viewLeft , viewRight

private
  open import Prelude.Nary
  variable n : ℕ

  module _ where

    infix -1 _—→_
    data _—→_ : Rel₀ ℕ where
      [inc] : n —→ suc n
      [dec] : suc n —→ n

    open ReflexiveTransitiveClosure _—→_

    _ : 10 —↠ 10
    _ = begin 10 ∎

    _ : 10 —↠⁺ 12
    _ = begin
      10 —→⟨ [inc] ⟩
      11 —→⟨ [dec] ⟩
      10 —→⟨ [inc] ⟩
      11 —→⟨ [inc] ⟩
      12 ∎

    _ : 12 ⁺↞— 10
    _ = begin
      12 ⟨ [inc] ⟩←—
      11 ⟨ [inc] ⟩←—
      10 ⟨ [dec] ⟩←—
      11 ⟨ [inc] ⟩←—
      10 ∎

  -- module _ where

  --   infix -1 _—[_]→_
  --   data _—[_]→_ : LRel₀ (ℕ , String) where
  --     [inc] : n —[ "inc" ]→ suc n
  --     [dec] : suc n —[ "dec" ]→ n

  --   open LabelledReflexiveTransitiveClosure _—[_]→_

  --   _ : 10 —[ [] ]↠ 10
  --   _ = begin 10 ∎

  --   _ : 10 —↠ 10
  --   _ = emit∶ begin 10 ∎

  --   _ : 10 —↠ 10
  --   _ = emitting [] ∶ begin 10 ∎

  --   _ : 10 —↠⁺ 12
  --   _ = emitting ⟦ "inc" , "dec" , "inc" , "inc" ⟧ ∶
  --       begin 10 —→⟨ [inc] ⟩
  --             11 —→⟨ [dec] ⟩
  --             10 —→⟨ [inc] ⟩
  --             11 —→⟨ [inc] ⟩
  --             12 ∎

  --   _ : 12 ⁺↞— 10
  --   _ = emitting ⟦ "inc" , "dec" , "inc" , "inc" ⟧ ∶
  --       begin 12 ⟨ [inc] ⟩←—
  --             11 ⟨ [inc] ⟩←—
  --             10 ⟨ [dec] ⟩←—
  --             11 ⟨ [inc] ⟩←—
  --             10 ∎

  module _ where

    infix -1 _—[_]→_
    data _—[_]→_ : LRel₀ (ℕ , String) where
      [inc] : n —[ "inc" ]→ suc n
      [dec] : suc n —[ "dec" ]→ n

    instance
      Setoidℕ : ISetoid ℕ
      Setoidℕ ._≈_ = _≡_

    open import Prelude.DecEq
    open UpToLabelledReflexiveTransitiveClosure _—[_]→_

    _ : 10 —[ [] ]↠ 10
    _ = begin 10 ∎

    _ : 10 —↠ 10
    _ = emit∶ begin 10 ∎

    _ : 10 —↠ 10
    _ = emitting [] ∶ begin 10 ∎

    _ : 10 —↠⁺ 12
    _ = emitting ⟦ "inc" , "dec" , "inc" , "inc" ⟧ ∶
        begin 10 —→⟨ [inc]      ⟩ it , it ⊢
              11 —→⟨ [dec] {10} ⟩
              10 —→⟨ [inc] {10} ⟩
              11 —→⟨ [inc] {11} ⟩
              12 ∎
              -- [BUG] cannot replace with begin 10 —→⟨ [inc] ⟩ 11 ⋯
              -- i.e. unnecessary implicits + first two equivalence proofs

    _ : 12 ⁺↞— 10
    _ = emitting ⟦ "inc" , "dec" , "inc" , "inc" ⟧ ∶
        begin 12 ⟨ [inc]      ⟩←— it , it ⊢
              11 ⟨ [inc] {10} ⟩←—
              10 ⟨ [dec] {10} ⟩←—
              11 ⟨ [inc] {10} ⟩←—
              10 ∎
