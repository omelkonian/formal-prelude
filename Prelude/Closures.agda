module Prelude.Closures where

open import Prelude.Init
open import Prelude.General

module ReflexiveTransitiveClosure {A : Set ℓ} (_—→_ : Rel A ℓ) where

  private variable x y z : A

  -- left-biased
  infix -1 _—↠_
  data _—↠_ : Rel A ℓ where
    _∎ : ∀ x → x —↠ x
    _—→⟨_⟩_ : ∀ x → x —→ y → y —↠ z → x —↠ z

  infix  3 _∎
  infixr 2 _—→⟨_⟩_
  infix  1 begin_
  pattern begin_ x = x

  -- right-biased view
  _←—_ : Rel A ℓ
  _←—_ = flip _—→_

  infix -1 _↞—_
  data _↞—_ : Rel A ℓ where
    _∎ : ∀ x → x ↞— x
    _⟨_⟩←—_ : ∀ z → z ←— y → y ↞— x → z ↞— x

  -- infix  3 _∎
  infixr 2 _⟨_⟩←—_

  -- view correspondence
  viewLeft : x —↠ y → y ↞— x
  viewLeft (_ ∎)          = _ ∎
  viewLeft (_ —→⟨ st ⟩ p) = _ `—→⟨ st ⟩ viewLeft p
    where
      infixr 2 _`—→⟨_⟩_
      _`—→⟨_⟩_ : ∀ x → y ←— x → z ↞— y → z ↞— x
      _ `—→⟨ st ⟩ _ ∎           = _ ⟨ st ⟩←— _ ∎
      _ `—→⟨ st ⟩ _ ⟨ st′ ⟩←— p = _ ⟨ st′ ⟩←— _ `—→⟨ st ⟩ p

  viewRight : y ↞— x → x —↠ y
  viewRight (_ ∎)          = _ ∎
  viewRight (_ ⟨ st ⟩←— p) = _ `⟨ st ⟩←— viewRight p
    where
      infixr 2 _`⟨_⟩←—_
      _`⟨_⟩←—_ : ∀ z → y —→ z → x —↠ y → x —↠ z
      _ `⟨ st ⟩←— (_ ∎)           = _ —→⟨ st ⟩ _ ∎
      _ `⟨ st ⟩←— (_ —→⟨ st′ ⟩ p) = _ —→⟨ st′ ⟩ (_ `⟨ st ⟩←— p)

  view↔ : (x —↠ y) ↔ (y ↞— x)
  view↔ = viewLeft , viewRight

private
  variable n : ℕ

  infix -1 _—→_
  data _—→_ : Rel₀ ℕ where
    [inc] : n —→ suc n
    [dec] : suc n —→ n

  open ReflexiveTransitiveClosure _—→_

  _ : 10 —↠ 12
  _ = begin
    10 —→⟨ [inc] ⟩
    11 —→⟨ [dec] ⟩
    10 —→⟨ [inc] ⟩
    11 —→⟨ [inc] ⟩
    12 ∎

  _ : 12 ↞— 10
  _ = begin
    12 ⟨ [inc] ⟩←—
    11 ⟨ [dec] ⟩←—
    12 ⟨ [inc] ⟩←—
    11 ⟨ [inc] ⟩←—
    10 ∎

-- labelled relations
LRel : Set ℓ × Set ℓ′ → (ℓ″ : Level) → Set (ℓ ⊔ₗ ℓ′ ⊔ₗ lsuc ℓ″)
LRel (A , L) ℓ = A → L → A → Set ℓ

module LabelledReflexiveTransitiveClosure
  {A : Set ℓ} {L : Set} (_—[_]→_ : LRel (A , L) ℓ) where

  private
    variable
      x y z : A
      α α′ : L
      αs αs′ : List L

  -- left-biased
  infix -1 _—[_]↠_
  data _—[_]↠_ : LRel (A , List L) ℓ where
    _∎ : ∀ x → x —[ [] ]↠ x
    _—→⟨_⟩_ : ∀ x → x —[ α ]→ y → y —[ αs ]↠ z → x —[ α ∷ αs ]↠ z

  infix  3 _∎
  infixr 2 _—→⟨_⟩_
  infix  1 begin_
  pattern begin_ x = x

  -- right-biased view
  _←[_]—_ : LRel (A , L) ℓ
  y ←[ α ]— x = x —[ α ]→ y

  infix -1 _↞[_]—_
  data _↞[_]—_ : LRel (A , List L) ℓ where
    _∎ : ∀ x → x ↞[ [] ]— x
    _⟨_⟩←—_ : ∀ z → (z ←[ α ]— y) → (y ↞[ αs ]— x) → z ↞[ αs L.∷ʳ α ]— x

  -- infix  3 _∎
  infixr 2 _⟨_⟩←—_
