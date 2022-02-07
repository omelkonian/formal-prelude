module Prelude.Decidable where

open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Lists
open import Prelude.Nary

record _⁇ (P : Set ℓ) : Set ℓ where
  constructor ⁇_
  field dec : Dec P

  auto : ⦃ True dec ⦄ → P
  auto ⦃ pr ⦄ = toWitness pr

  -- NB: already covered by `auto`
  -- ¬auto : ∀ {pr : False dec} → ¬ P
  -- ¬auto {pr} = toWitnessFalse pr

  contradict : ∀ {X : Set} {pr : False dec} → P → X
  contradict {pr = pr} = ⊥-elim ∘ toWitnessFalse pr

open _⁇ ⦃ ... ⦄ public

¿_¿ : ∀ (X : Set ℓ) → ⦃ X ⁇ ⦄ → Dec X
¿ _ ¿ = dec

_⁇¹ : ∀ {A : Set ℓ} → (P : Pred A ℓ′) → Set (ℓ ⊔ₗ ℓ′)
P ⁇¹ = ∀ {x} → P x ⁇

dec¹ : ∀ {A : Set ℓ} {P : Pred A ℓ′} → ⦃ P ⁇¹ ⦄ → Decidable¹ P
dec¹ _ = dec

¿_¿¹ : ∀ {A : Set ℓ} (P : Pred A ℓ′) → ⦃ P ⁇¹ ⦄ → Decidable¹ P
¿ _ ¿¹ = dec¹

_⁇² : ∀ {A B : Set ℓ} → (P : REL A B ℓ′) → Set (ℓ ⊔ₗ ℓ′)
_~_ ⁇² = ∀ {x y} → (x ~ y) ⁇

dec² : ∀ {A B : Set ℓ} {_~_ : REL A B ℓ′} → ⦃ _~_ ⁇² ⦄ → Decidable² _~_
dec² _ _ = dec

¿_¿² : ∀ {A B : Set ℓ} (_~_ : REL A B ℓ′) → ⦃ _~_ ⁇² ⦄ → Decidable² _~_
¿ _ ¿² = dec²

_⁇³ : ∀ {A B C : Set ℓ} → (P : 3REL A B C ℓ′) → Set (ℓ ⊔ₗ ℓ′)
_~_~_ ⁇³ = ∀ {x y z} → (x ~ y ~ z) ⁇

dec³ : ∀ {A B C : Set ℓ} {_~_~_ : 3REL A B C ℓ′} → ⦃ _~_~_ ⁇³ ⦄ → Decidable³ _~_~_
dec³ _ _ _ = dec

¿_¿³ : ∀ {A B C : Set ℓ} (_~_~_ : 3REL A B C ℓ′) → ⦃ _~_~_ ⁇³ ⦄ → Decidable³ _~_~_
¿ _ ¿³ = dec³

private variable
  A : Set ℓ
  B : Set ℓ′

instance
  -- Basics
  Dec-⊥ : ⊥ ⁇
  Dec-⊥ .dec = no λ()

  Dec-⊤ : ⊤ ⁇
  Dec-⊤ .dec = yes tt

  Dec-→ : ⦃ A ⁇ ⦄ → ⦃ B ⁇ ⦄ → (A → B) ⁇
  Dec-→ .dec = dec →-dec dec

  -- NB: Already covered by implication
  -- Dec-¬ : ⦃ A ⁇ ⦄ → (¬ A) ⁇
  -- Dec-¬ .dec = ¬? dec

  Dec-× : ⦃ A ⁇ ⦄ → ⦃ B ⁇ ⦄ → (A × B) ⁇
  Dec-× .dec = dec ×-dec dec

  Dec-⊎ : ⦃ A ⁇ ⦄ → ⦃ B ⁇ ⦄ → (A ⊎ B) ⁇
  Dec-⊎ .dec = dec ⊎-dec dec

  DecEq⇒Dec : ⦃ DecEq A ⦄ → _≡_ {A = A} ⁇²
  DecEq⇒Dec .dec = _ ≟ _

private variable
  p : Level
  P¹ : Pred A p
  P² : Rel A p

instance
  -- Bool
  Dec-T : ∀ {t : Bool} → T t ⁇
  Dec-T .dec = T? _

  -- Maybe
  Dec-All : ⦃ P¹ ⁇¹ ⦄ → All P¹ ⁇¹
  Dec-All .dec = all? dec¹ _

  Dec-Any : ⦃ P¹ ⁇¹ ⦄ → Any P¹ ⁇¹
  Dec-Any .dec = any? dec¹ _

  Dec-AllPairs : ⦃ P² ⁇² ⦄ → AllPairs P² ⁇¹
  Dec-AllPairs .dec = allPairs? dec² _

  Dec-MAll : ⦃ _ : P¹ ⁇¹ ⦄ → M.All.All P¹ ⁇¹
  Dec-MAll .dec = M.All.dec dec¹ _

  Dec-MAny : ⦃ _ : P¹ ⁇¹ ⦄ → M.Any.Any P¹ ⁇¹
  Dec-MAny .dec = M.Any.dec dec¹ _

private
  _ = (¬ ¬ ((true , true) ≡ (true , true)))
    × (8 ≡ 18 ∸ 10)
    ∋ auto

  _ = ¬ ( (¬ ¬ ((true , true) ≡ (true , true)))
        × (8 ≡ 17 ∸ 10) )
    ∋ auto

  _ : ∀ {A : Set ℓ}
    → ⦃ DecEq A ⦄
    → {m : Maybe (List A)} {x₁ x₂ : A}
    → Dec $ M.Any.Any (λ xs → (xs ≡ ⟦ x₁ , x₂ ⟧) ⊎ Any (const ⊤) xs) m
  _ = dec

  -- ** Non-dependent records
  record Valid : Set where
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
  record Valid : Set where
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
  record Valid ⦃ da : DecEq A ⦄ (m : Maybe (List A)) (x₁ x₂ : A) : Set where
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
