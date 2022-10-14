open import Prelude.Init; open SetAsType
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Apartness
open import Prelude.Ord
open import Prelude.Setoid

module Prelude.Bags.Abstract.Interface (A : Type) (σ : Level) where

record Bagᴵ : Type (lsuc σ) where
  constructor mkBagᴵ
  field
    Bag : Type σ
    ∅ : Bag
    singleton : A → Bag
    occurs : Bag → A → ℕ
    _─_ _∪_ : Op₂ Bag
    scale : Bag → ℕ → Bag

  syntax Bag {A = A} = Bag⟨ A ⟩
  infixr 6 _─_
  infixr 5 _∪_
  infix  4 _∈ˢ_ _∉ˢ_ _⊆ˢ_ _⊇ˢ_ _⊈ˢ_ _⊉ˢ_

  _∈ˢ_ : A → Bag → Type
  x ∈ˢ b = occurs b x > 0

  _∉ˢ_ : A → Bag → Type
  x ∉ˢ s = ¬ (x ∈ˢ s)

  -- ** relational properties
  field
    singleton∈ˢ : ∀ {x x′} → x′ ∈ˢ singleton x ↔ x′ ≡ x

    occurs-∪ : ∀ x xs ys → occurs (xs ∪ ys) x ≡ occurs xs x + occurs ys x
    occurs-─ : ∀ x xs ys → occurs (xs ─ ys) x ≡ occurs xs x ∸ occurs ys x
    occurs-scale : ∀ x xs n → occurs (scale xs n) x ≡ occurs xs x * n

  postulate
    ∈-∪⁻ : ∀ x xs ys → x ∈ˢ (xs ∪ ys) → x ∈ˢ xs ⊎ x ∈ˢ ys
    ∈-∪⁺ˡ : ∀ x xs ys → x ∈ˢ xs → x ∈ˢ (xs ∪ ys)
    ∈-∪⁺ʳ : ∀ x xs ys → x ∈ˢ ys → x ∈ˢ (xs ∪ ys)
    ∉∅ : ∀ x → x ∉ˢ ∅

  -- ∈-─⁻ : ∀ x xs ys → x ∈ˢ (xs ─ ys) → x ∈ˢ xs
  -- ∈-─⁺ : ∀ x xs ys → x ∈ˢ xs → x ∉ˢ ys → x ∈ˢ (xs ─ ys)

  _♯ˢ_ : Rel₀ Bag
  s ♯ˢ s′ = ∀ {k} → ¬ (k ∈ˢ s × k ∈ˢ s′)

  instance
    Apart-Bag : Bag // Bag
    Apart-Bag ._♯_ = _♯ˢ_

  -- ♯-comm : Symmetric _♯_
  ♯-comm : ∀ (x y : Bag) → x ♯ y → y ♯ x
  ♯-comm x y x♯y = x♯y ∘ Product.swap

  ♯-skipˡ : ∀ xs ys (zs : Bag) → (xs ∪ ys) ♯ zs → ys ♯ zs
  ♯-skipˡ xs ys _ p (x∈ys , x∈zs) = p (∈-∪⁺ʳ _ xs ys x∈ys , x∈zs)

  _⊆ˢ_ _⊇ˢ_ _⊈ˢ_ _⊉ˢ_ : Rel Bag _
  b ⊆ˢ b′ = ∀ {x} → occurs b x ≤ occurs b′ x
  b ⊈ˢ b′ = ¬ b ⊆ˢ b′; b ⊇ˢ b′ = b′ ⊆ˢ b; b ⊉ˢ b′ = ¬ b ⊇ˢ b′

  ⊆ˢ-trans : Transitive _⊆ˢ_
  ⊆ˢ-trans p q = Nat.≤-trans p q

  instance
    Setoid-Bag : ISetoid Bag
    Setoid-Bag = λ where
      .relℓ → _
      ._≈_ s s′ → (s ⊆ˢ s′) × (s′ ⊆ˢ s)

    SetoidLaws-Bag : Setoid-Laws Bag
    SetoidLaws-Bag .isEquivalence = record
      { refl  = Nat.≤-refl , Nat.≤-refl
      ; sym   = Product.swap
      ; trans = λ where (ij , ji) (jk , kj) → ⊆ˢ-trans ij jk , ⊆ˢ-trans kj ji
      }

  open Alg (Rel₀ Bag ∋ _≈_)
