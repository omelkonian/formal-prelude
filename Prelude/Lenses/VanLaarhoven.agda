open import Prelude.Init; open SetAsType
open import Prelude.Functor

module Prelude.Lenses.VanLaarhoven where

record Functor′ (F : Type → Type) : Type₁ where
  field fmap′ : ∀ {A B : Type} → (A → B) → (F A → F B)
  _⟨$⟩_ = fmap′
open Functor′ ⦃...⦄ public

Const : Type → (Type → Type)
Const A _ = A

Id : Type → Type
Id = id

private variable A B I O : Type

instance
  Functor′-Id : Functor′ Id
  Functor′-Id .fmap′ = id

  Functor′-Const : Functor′ (Const A)
  Functor′-Const .fmap′ = const id

Lens : Type → Type → Type₁
-- Lens I O = ∀ (F : Type↑) → ⦃ Functor F ⦄ → (I → F I) → (O → F O)
Lens I O = ∀ F → ⦃ Functor′ F ⦄ → (I → F I) → (O → F O)

over : Lens I O → (I → I) → (O → O)
over l f o = l Id f o
-- runIdentity $ l (Identity . f) o

view : Lens I O → O → I
-- view {I = I} l o = l (Const I) id o
view {I = I} l o = {!!}

-- l₁ : Lens A (A × B)
-- l₁ F f (x , y) = (_, y) ⟨$⟩ f x

-- l₂ : Lens B (A × B)
-- l₂ F f (x , y) = (x ,_) ⟨$⟩ f y

-- view : A × B → A
-- view {A}{B} (x , y) = l₁ {A} {B} (Const (B → A)) const (x , y) y

-- _ = view (1 , "one") ≡ 1 ∋ refl

-- _ = over l₁ suc (1 , "one") ≡ (2 , "one") ∋ refl

-- set : A × B → A → A × B
-- set xy x′ = over l₁ (const x′) xy

-- -- _∙_ : O → Lens I O → I
-- -- o ∙ l = l _ (const _) o
