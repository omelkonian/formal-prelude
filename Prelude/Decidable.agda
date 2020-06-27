module Prelude.Decidable where

open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Lists

record Decidable {p} (P : Set p) : Set p where
  field
    dec : Dec P

  auto : ∀ {pr : True dec} → P
  auto {pr} = toWitness pr

  -- NB: already covered by `auto`
  -- ¬auto : ∀ {pr : False dec} → ¬ P
  -- ¬auto {pr} = toWitnessFalse pr

open Decidable {{...}} public

syntax Decidable A = A ⁇

private
  variable
    a b : Level
    A : Set a
    B : Set b

instance
  Dec-→ : {{_ : A ⁇}} {{_ : B ⁇}} → (A → B) ⁇
  Dec-→ .dec = dec →-dec dec

  -- NB: Already covered by implication
  -- Dec-¬ : {{_ : A ⁇}} → (¬ A) ⁇
  -- Dec-¬ .dec = ¬? dec

  Dec-× : {{_ : A ⁇}} {{_ : B ⁇}} → (A × B) ⁇
  Dec-× .dec = dec ×-dec dec

  Dec-⊎ : {{_ : A ⁇}} {{_ : B ⁇}} → (A ⊎ B) ⁇
  Dec-⊎ .dec = dec ⊎-dec dec

  DecEq⇒Dec : {{_ : DecEq A}} {x y : A} → (x ≡ y) ⁇
  DecEq⇒Dec .dec = _ ≟ _

--

private
  variable
    bx : Bool

    xs ys : List A

    mx : Maybe A

    P¹ : Pred A 0ℓ
    P² : Rel A 0ℓ

instance
  Dec-⊥ : ⊥ ⁇
  Dec-⊥ .dec = no λ()

  Dec-⊤ : ⊤ ⁇
  Dec-⊤ .dec = yes tt

  Dec-T : T bx ⁇
  Dec-T .dec = T? _

  Dec-⊆ : {A : Set} {{da : DecEq A}} {xs ys : List A} → (xs ⊆ ys) ⁇
  Dec-⊆ .dec = _ ⊆? _

  Dec-All : {{_ : ∀ {xs} → P¹ xs ⁇}} → All P¹ xs ⁇
  Dec-All .dec = all? (λ _ → dec) _

  Dec-Any : {{_ : ∀ {xs} → P¹ xs ⁇}} → Any P¹ xs ⁇
  Dec-Any .dec = any? (λ _ → dec) _

  Dec-AllPairs : {{_ : ∀ {x y} → P² x y ⁇}} → AllPairs P² xs ⁇
  Dec-AllPairs .dec = allPairs? (λ _ _ → dec) _

  Dec-MAll : {{_ : ∀ {mx} → P¹ mx ⁇}} → M.All.All P¹ mx ⁇
  Dec-MAll .dec = M.All.dec (λ _ → dec) _

  Dec-MAny : {{_ : ∀ {mx} → P¹ mx ⁇}} → M.Any.Any P¹ mx ⁇
  Dec-MAny .dec = M.Any.dec (λ _ → dec) _


private
  _ : (¬ ¬ ((true , true) ≡ (true , true)))
    × (8 ≡ 18 ∸ 10)
  _ = auto

  _ : ¬ ( (¬ ¬ ((true , true) ≡ (true , true)))
        × (8 ≡ 17 ∸ 10) )
  _ = auto

  _ : ∀ {{da : DecEq A}} {m : Maybe (List A)} {x₁ x₂ : A}
    → Dec
    $ M.Any.Any (λ xs → ( (xs ≡ ⟦ x₁ , x₂ ⟧)
                        × (Any (const ⊤) xs)
                        ⊎ (⟦ x₁ , x₂ ⟧ ⊆ xs) )) m
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
  record Valid {{da : DecEq A}} (m : Maybe (List A)) (x₁ x₂ : A) : Set where
    field
      p₁ : M.Any.Any (λ xs → ( (xs ≡ ⟦ x₁ , x₂ ⟧)
                            × (Any (const ⊤) xs)
                            ⊎ (_⊆_ (_≟_ {{da}}) ⟦ x₁ , x₂ ⟧ xs)
                            )) m

      p₂ : proj₁ (M.Any.satisfied p₁) ≡ ⟦ x₁ , x₂ ⟧
  open Valid

  t : ∀ {{_ : DecEq A}} {m : Maybe (List A)} {x₁ x₂} → (Valid m x₁ x₂) ⁇
  t .dec
    with dec
  ... | no ¬p₁ = no  (¬p₁ ∘ p₁)
  ... | yes p₁
    with dec
  ... | no ¬p₂ = no  {!!} -- (¬p₂ ∘ p₂) -- doesn't work because of dependency between p₁ and p₂
  ... | yes p₂ = yes record {p₁ = p₁; p₂ = p₂}
-}
