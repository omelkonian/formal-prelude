module Prelude.Decidable.Examples where

open import Prelude.Init; open SetAsType
open import Prelude.DecEq
open import Prelude.Nary

open import Prelude.Decidable.Core
open import Prelude.Decidable.Instances

private
  _ = (¬ ¬ ((true , true) ≡ (true , true)))
    × (8 ≡ 18 ∸ 10)
    ∋ auto

  _ = ¬ ( (¬ ¬ ((true , true) ≡ (true , true)))
        × (8 ≡ 17 ∸ 10) )
    ∋ auto

  _ : ∀ {A : Type ℓ}
    → ⦃ DecEq A ⦄
    → {m : Maybe (List A)} {x₁ x₂ : A}
    → Dec $ M.Any.Any (λ xs → (xs ≡ ⟦ x₁ , x₂ ⟧) ⊎ Any (const ⊤) xs) m
  _ = dec

  -- ** Non-dependent records
  record Valid : Type where
    field
      p₁ : ¬ ( (¬ ¬ (true ≡ true))
             × (8 ≡ 17 ∸ 10) )
      p₂ : (¬ ¬ (true ≡ true))
         × (8 ≡ 18 ∸ 10)
  open Valid

  t : Valid ⁇
  t .dec
    with dec
  ... | no ¬p₁ = no  (¬p₁ ∘ p₁)
  ... | yes p₁
    with dec
  ... | no ¬p₂ = no  (¬p₂ ∘ p₂)
  ... | yes p₂ = yes record {p₁ = p₁; p₂ = p₂}

{-
  -- ** Dependent records (simple)
  record Valid : Type where
    field
      p₁ : ⊤
      p₂ : ¬ ( (¬ ¬ (tt ≡ p₁))
             × (8 ≡ 17 ∸ 10) )
  open Valid

  t : Valid ⁇
  t .dec
    with dec
  ... | no ¬p₁ = no  (¬p₁ ∘ p₁)
  ... | yes p₁
    with dec
  ... | no ¬p₂ = no  {!!} -- (¬p₂ ∘ p₂) -- doesn't work because of dependency between p₁ and p₂
  ... | yes p₂ = yes record {p₁ = p₁; p₂ = p₂}
-}

{-
  -- ** Dependent records (advanced)
  record Valid ⦃ da : DecEq A ⦄ (m : Maybe (List A)) (x₁ x₂ : A) : Type where
    field
      p₁ : M.Any.Any (λ xs → ( (xs ≡ ⟦ x₁ , x₂ ⟧)
                            × (Any (const ⊤) xs)
                            ⊎ (_⊆_ (_≟_ ⦃ da ⦄) ⟦ x₁ , x₂ ⟧ xs)
                            )) m

      p₂ : proj₁ (M.Any.satisfied p₁) ≡ ⟦ x₁ , x₂ ⟧
  open Valid

  t : ∀ ⦃ DecEq A ⦄ {m : Maybe (List A)} {x₁ x₂} → (Valid m x₁ x₂) ⁇
  t .dec
    with dec
  ... | no ¬p₁ = no  (¬p₁ ∘ p₁)
  ... | yes p₁
    with dec
  ... | no ¬p₂ = no  {!!} -- (¬p₂ ∘ p₂) -- doesn't work because of dependency between p₁ and p₂
  ... | yes p₂ = yes record {p₁ = p₁; p₂ = p₂}
-}
