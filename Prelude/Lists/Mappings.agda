------------------------------------------------------------------------
-- Mappings as total functions from membership proofs of a finite list.

module Prelude.Lists.Mappings where

open import Prelude.Init
open L.Mem using (_∈_; mapWith∈; ∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open L.Perm using (∈-resp-↭; Any-resp-↭)
open import Prelude.General using (⟫_)
open import Prelude.Lists.Membership
open import Prelude.Lists.Permutations

private variable
  a b p : Level
  A : Set a
  B : Set b
  P : Pred A p

  x : A
  xs xs′ ys zs : List A

-- ** Mappings from membership proofs.
infixr 0 _↦′_ _↦_

_↦′_ : List A → (A → Set ℓ) → Set _
xs ↦′ P = ∀ {x} → x ∈ xs → P x

map↦ = _↦′_
syntax map↦ xs (λ x → f) = ∀[ x ∈ xs ] f

_↦_ : List A → Set b → Set _
xs ↦ B = xs ↦′ const B

dom : ∀ {xs : List A} → xs ↦′ P → List A
dom {xs = xs} _ = xs

codom : xs ↦ B → List B
codom = mapWith∈ _

codom-↦ : ∀ {xs : List A} → (f : xs ↦ B) → codom f ↦ A
codom-↦ {xs = x ∷ _} f = λ where
  (here  _)  → x
  (there x∈) → codom-↦ (f ∘ there) x∈

weaken-↦ : xs ↦′ P → ys ⊆ xs → ys ↦′ P
weaken-↦ f ys⊆xs = f ∘ ys⊆xs

cons-↦ : (x : A) → P x → xs ↦′ P → (x ∷ xs) ↦′ P
cons-↦ _ y _ (here refl) = y
cons-↦ _ _ f (there x∈)  = f x∈

uncons-↦ : (x ∷ xs) ↦′ P → xs ↦′ P
uncons-↦ = _∘ there

permute-↦ : xs ↭ ys → xs ↦′ P → ys ↦′ P
permute-↦ xs↭ys xs↦ = xs↦ ∘ L.Perm.∈-resp-↭ (↭-sym xs↭ys)

_++/↦_ : xs ↦′ P → ys ↦′ P → xs ++ ys ↦′ P
xs↦ ++/↦ ys↦ = ∈-++⁻ _ >≡> λ where
  (inj₁ x∈) → xs↦ x∈
  (inj₂ y∈) → ys↦ y∈

destruct-++/↦ : xs ++ ys ↦′ P → (xs ↦′ P) × (ys ↦′ P)
destruct-++/↦ xys↦ = xys↦ ∘ ∈-++⁺ˡ , xys↦ ∘ ∈-++⁺ʳ _

destruct≡-++/↦ : zs ≡ xs ++ ys → zs ↦′ P → (xs ↦′ P) × (ys ↦′ P)
destruct≡-++/↦ refl = destruct-++/↦

extend-↦ : zs ↭ xs ++ ys → xs ↦′ P → ys ↦′ P → zs ↦′ P
extend-↦ zs↭ xs↦ ys↦ = permute-↦ (↭-sym zs↭) (xs↦ ++/↦ ys↦)

cong-↦ : xs ↦′ P → xs′ ≡ xs → xs′ ↦′ P
cong-↦ f refl = f

open ≡-Reasoning

-- ** Pointwise equality of same-domain mappings.
module _ {A : Set ℓ} {xs : List A} {P : Pred A ℓ′} where
  _≗↦_ : Rel (xs ↦′ P) _
  f ≗↦ f′ = ∀ {x : A} (x∈ : x ∈ xs) → f x∈ ≡ f′ x∈

  _≗⟨_⟩↦_ : ∀ {ys : List A} →
    (ys ↦′ P) → (p↭ : xs ↭ ys) → (xs ↦′ P) → Set _
  f′ ≗⟨ p↭ ⟩↦ f = ∀ {x : A} (x∈ : x ∈ xs) → f′ (∈-resp-↭ p↭ x∈) ≡ f x∈

  permute-≗↦ : ∀ {ys : List A}
    → (p↭ : xs ↭ ys)
    → (f : xs ↦′ P)
      --——————————————————————————————————————
    → permute-↦ p↭ f ≗⟨ p↭ ⟩↦ f
  permute-≗↦ p↭ f {x} x∈ =
    begin
      permute-↦ p↭ f (∈-resp-↭ p↭ x∈)
    ≡⟨⟩
      (f ∘ ∈-resp-↭ (↭-sym p↭)) (∈-resp-↭ p↭ x∈)
    ≡⟨⟩
      f (∈-resp-↭ (↭-sym p↭) $ ∈-resp-↭ p↭ x∈)
    ≡⟨ cong f (∈-resp-↭∘∈-resp-↭˘ p↭ x∈) ⟩
      f x∈
    ∎


  permute-↦∘permute-↦˘ : ∀ {ys : List A}
    → (p↭ : xs ↭ ys)
    → (f : xs ↦′ P)
      --——————————————————————————————————————
    → permute-↦ (↭-sym p↭) (permute-↦ p↭ f) ≗↦ f
  permute-↦∘permute-↦˘ p↭ f {x} x∈
    rewrite permute-≗↦ p↭ f x∈
          | L.Perm.↭-sym-involutive p↭
    = cong f $ Any-resp-↭∘Any-resp-↭˘ p↭ x∈

module _ (f : xs ↦′ P) (g : ys ↦′ P) where
  destruct-++/↦∘++/↦ :
    let f′ , g′ = destruct-++/↦ (f ++/↦ g)
    in (f ≗↦ f′) × (g ≗↦ g′)
  destruct-++/↦∘++/↦ = f≗ , g≗
    where
      fg : (xs ↦′ P) × (ys ↦′ P)
      fg = destruct-++/↦ (f ++/↦ g)
      f′ = fg .proj₁; g′ = fg .proj₂

      f≗ : f ≗↦ f′
      f≗ x∈ rewrite Any-++⁻∘Any-++⁺ˡ {ys = ys} x∈ = refl

      g≗ : g ≗↦ g′
      g≗ x∈ rewrite Any-++⁻∘Any-++⁺ʳ {xs = xs} x∈ = refl

  destruct≡-++/↦∘cong-↦ :
    (eq : zs ≡ xs ++ ys) →
    let f′ , g′ = destruct≡-++/↦ eq (cong-↦ (f ++/↦ g) eq)
    in (f ≗↦ f′) × (g ≗↦ g′)
  destruct≡-++/↦∘cong-↦ refl = destruct-++/↦∘++/↦

-- T0D0 use for permute-↦∘permute-↦˘ to simplify
module _ {A : Set ℓ} {P : A → Set ℓ′} {x : A} {xs ys zs : List A} where
  permute-↦∘permute-↦ :
    (p : xs ↭ ys) (q : ys ↭ zs) (f : xs ↦′ P) →
    --——————————————————————————————————————————————————————
    permute-↦ q (permute-↦ p f) ≗↦ permute-↦ (↭-trans p q) f
  permute-↦∘permute-↦ p q f x∈ =
    begin
      permute-↦ q (permute-↦ p f) x∈
    ≡⟨⟩
      f (∈-resp-↭ (↭-sym p) $ ∈-resp-↭ (↭-sym q) x∈)
    ≡⟨⟩
      f (∈-resp-↭ (↭-sym $ ↭-trans p q) x∈)
    ≡⟨⟩
      permute-↦ (↭-trans p q) f x∈
    ∎

-- ** Pointwise equality of ⊆-related mappings.
module _ {A : Set ℓ} {xs ys : List A} {P : Pred A ℓ′} where
  _≗⟨_⊆⟩↦_ : ys ↦′ P → (p : ys ⊆ xs) → xs ↦′ P → Set _
  f′ ≗⟨ p ⊆⟩↦ f = f′ ≗↦ (f ∘ p)

  weaken-≗↦ : (p : ys ⊆ xs) (f : xs ↦′ P)
    → weaken-↦ f p ≗⟨ p ⊆⟩↦ f
  weaken-≗↦ _ _ _ = refl

  _≗↦ˡ_ : xs ++ ys ↦′ P → xs ↦′ P → Set _
  fg ≗↦ˡ f = (fg ∘ L.Mem.∈-++⁺ˡ) ≗↦ f

  ++-≗↦ˡ : (f : xs ↦′ P) (g : ys ↦′ P)
    → (f ++/↦ g) ≗↦ˡ f
  ++-≗↦ˡ _ _ (here _) = refl
  ++-≗↦ˡ _ _ (there x∈) rewrite ∈-++⁻∘∈-++⁺ˡ {ys = ys} x∈ = refl

  _≗↦ʳ_ : xs ++ ys ↦′ P → ys ↦′ P → Set _
  fg ≗↦ʳ g = (fg ∘ L.Mem.∈-++⁺ʳ _) ≗↦ g

  ++-≗↦ʳ : (f : xs ↦′ P) (g : ys ↦′ P)
    → (f ++/↦ g) ≗↦ʳ g
  ++-≗↦ʳ f g y∈ with ⟫ xs
  ... | ⟫ [] = refl
  ... | ⟫ _ ∷ xs′ rewrite ∈-++⁻∘∈-++⁺ʳ {xs = xs} y∈ = refl

  _≗↦ˡʳ_,_ : xs ++ ys ↦′ P → xs ↦′ P → ys ↦′ P → Set _
  fg ≗↦ˡʳ f , g = (fg ≗↦ˡ f) × (fg ≗↦ʳ g)

  ++-≗↦ˡʳ : (f : xs ↦′ P) (g : ys ↦′ P)
    → (f ++/↦ g) ≗↦ˡʳ f , g
  ++-≗↦ˡʳ f g = ++-≗↦ˡ f g , ++-≗↦ʳ f g

-- ** Properties.
++/↦-inj₂ : ∀ (f : xs ↦′ P) (g : ys ↦′ P) (x∈ : x ∈ xs ++ ys) (y∈ : x ∈ ys)
  → ∈-++⁻ xs x∈ ≡ inj₂ y∈
    --———————————————————
  → (f ++/↦ g) x∈ ≡ g y∈
++/↦-inj₂ {xs = xs} _ _ x∈ _ eq
  with inj₂ _ ← ∈-++⁻ xs x∈
  with refl ← eq
  = refl

++/↦≡-inj₂ : (eq : zs ≡ xs ++ ys)
  → ∀ (f : xs ↦′ P) (g : ys ↦′ P) (x∈ : x ∈ zs) (y∈ : x ∈ ys)
    → ∈-++⁻ xs (subst (x ∈_) eq x∈) ≡ inj₂ y∈
      --—————————————————————————————————————
    → subst (_↦′ P) (sym eq) (f ++/↦ g) x∈ ≡ g y∈
++/↦≡-inj₂ refl = ++/↦-inj₂

++/↦-there : (f : x ∷ xs ↦′ P) (g : ys ↦′ P)
  → ((f ∘ there) ++/↦ g) ≗↦ ((f ++/↦ g) ∘ there)
++/↦-there {xs = []}         _ _ {_} _        = refl
++/↦-there {xs = _ ∷ _}      _ _ {_} (here _) = refl
++/↦-there {xs = xs@(_ ∷ _)} _ _ {_} (there x∈)
  with ∈-++⁻ xs (there x∈)
... | inj₁ _ = refl
... | inj₂ _ = refl

uncons-≗↦ : (f : x ∷ xs ↦′ P) (g : ys ↦′ P)
  → uncons-↦ (f ++/↦ g) ≗↦ (uncons-↦ f ++/↦ g)
uncons-≗↦ f g {y} y∈ =
  begin uncons-↦ (f ++/↦ g) y∈  ≡⟨⟩
        (f ++/↦ g) (there y∈)   ≡⟨ sym $ ++/↦-there f g y∈ ⟩
        ((f ∘ there) ++/↦ g) y∈ ≡⟨⟩
        (uncons-↦ f ++/↦ g) y∈  ∎
