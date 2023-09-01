module Prelude.Anyable where

open import Prelude.Init hiding (Any); open SetAsType

record Anyable (F : Type ℓ → Type ℓ) : Type (lsuc ℓ) where
  field Any : ∀ {A} → Pred₀ A → F A → Type ℓ

  ∃∈-syntax  = Any
  ∃∈-syntax′ = Any
  ∄∈-syntax  = λ {A} P → ¬_ ∘ Any {A} P
  ∄∈-syntax′ = ∄∈-syntax
  infix 2 ∃∈-syntax ∃∈-syntax′ ∄∈-syntax ∄∈-syntax′
  syntax ∃∈-syntax  P         xs = ∃[∈    xs ] P
  syntax ∃∈-syntax′ (λ x → P) xs = ∃[ x ∈ xs ] P
  syntax ∄∈-syntax  P         xs = ∄[∈    xs ] P
  syntax ∄∈-syntax′ (λ x → P) xs = ∄[ x ∈ xs ] P

open Anyable ⦃...⦄ public

instance
  Anyable-List : Anyable {ℓ} List
  Anyable-List .Any = L.Any.Any

  Anyable-Vec : ∀ {n} → Anyable {ℓ} (flip Vec n)
  Anyable-Vec .Any P = V.Any.Any P

  Anyable-Maybe : Anyable {ℓ} Maybe
  Anyable-Maybe .Any = M.Any.Any

private
  open import Prelude.Decidable
  open import Prelude.Ord.Core
  open import Prelude.Ord.Instances

  _ : ∃[ x ∈ List ℕ ∋ [ 1 ⨾  2 ⨾ 3 ] ] (x > 0)
  _ = auto

  _ : ∃[ x ∈ Vec ℕ 3 ∋ [ 1 ⨾  2 ⨾ 3 ] ] (x > 0)
  _ = auto

  _ : ∃[ x ∈ just 42 ] (x > 0)
  _ = auto

  _ : ∄[ x ∈ nothing ] (x > 0)
  _ = auto
