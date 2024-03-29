{-# OPTIONS --safe #-}
module Prelude.Lists.Membership where

open import Prelude.Init; open SetAsType
open L.Mem
open import Prelude.General
open import Prelude.InferenceRules
open import Prelude.Null
open import Prelude.Lists.Core
open import Prelude.Lists.Indexed
open import Prelude.Lists.Empty

private variable
  A : Type ℓ; B : Type ℓ′; C : Type ℓ″
  x x′ y : A; xs ys : List A
  P Q : Pred A ℓ

-- ** Any

module _ {A : Type ℓ} {P : Pred A ℓ′} {xs : List A} where
  Is-here Is-there : Pred₀ (Any P xs)
  Is-here = λ where
    (here _)  → ⊤
    (there _) → ⊥
  Is-there = λ where
    (here _)  → ⊥
    (there _) → ⊤

Any-++⁻∘Any-++⁺ˡ : (x∈ : Any P xs)
  → L.Any.++⁻ xs {ys} (L.Any.++⁺ˡ {xs = xs}{ys} x∈)
  ≡ inj₁ x∈
Any-++⁻∘Any-++⁺ˡ (here _) = refl
Any-++⁻∘Any-++⁺ˡ {ys = ys} (there x∈) rewrite Any-++⁻∘Any-++⁺ˡ {ys = ys} x∈ = refl

Any-++⁻∘Any-++⁺ʳ : (y∈ : Any P ys)
  → L.Any.++⁻ xs {ys} (L.Any.++⁺ʳ xs {ys} y∈)
  ≡ inj₂ y∈
Any-++⁻∘Any-++⁺ʳ {xs = []} _ = refl
Any-++⁻∘Any-++⁺ʳ {xs = _ ∷ xs} y∈ rewrite Any-++⁻∘Any-++⁺ʳ {xs = xs} y∈ = refl

Any-++⁻⇒Any-++⁺ : ∀ {xs ys : List A}
  → (x∈ : Any P (xs ++ ys))
    --———————————————————
  → case L.Any.++⁻ xs {ys} x∈ of λ where
      (inj₁ x∈ˡ) → x∈ ≡ L.Any.++⁺ˡ x∈ˡ
      (inj₂ x∈ʳ) → x∈ ≡ L.Any.++⁺ʳ xs x∈ʳ
Any-++⁻⇒Any-++⁺ {xs = []}          x∈       = refl
Any-++⁻⇒Any-++⁺ {xs = x ∷ xs} {ys} (here _) = refl
Any-++⁻⇒Any-++⁺ {xs = x ∷ xs} {ys} (there x∈)
  with IH ← Any-++⁻⇒Any-++⁺ {xs = xs}{ys} x∈
  with L.Any.++⁻ xs x∈
... | inj₁ x∈ˡ = cong there IH
... | inj₂ x∈ʳ = cong there IH

destruct-Any-++ : ∀ {xs ys : List A}
  → (x∈ : Any P (xs ++ ys))
    --——————————————————
  → (∃ λ (x∈ˡ : Any P xs) → x∈ ≡ L.Any.++⁺ˡ x∈ˡ)
  ⊎ (∃ λ (x∈ʳ : Any P ys) → x∈ ≡ L.Any.++⁺ʳ xs x∈ʳ)
destruct-Any-++ {xs = xs}{ys} x∈
  with L.Any.++⁻ xs {ys} x∈ | Any-++⁻⇒Any-++⁺ {xs = xs}{ys} x∈
... | inj₁ x∈ˡ | refl = inj₁ $ -, refl
... | inj₂ x∈ʳ | refl = inj₂ $ -, refl

destruct-Any-++² : ∀ {xs ys zs : List A}
  → (x∈ : Any P (xs ++ ys ++ zs))
    --————————————————————————————————————
  → (∃ λ (x∈xs : Any P xs) → x∈ ≡ (L.Any.++⁺ˡ x∈xs))
  ⊎ (∃ λ (x∈ys : Any P ys) → x∈ ≡ (L.Any.++⁺ʳ xs $ L.Any.++⁺ˡ x∈ys))
  ⊎ (∃ λ (x∈zs : Any P zs) → x∈ ≡ (L.Any.++⁺ʳ xs $ L.Any.++⁺ʳ ys x∈zs))
destruct-Any-++² {xs = xs}{ys} x∈
  with destruct-Any-++ {xs = xs} x∈
... | inj₁ (_   , refl) = inj₁ $ -, refl
... | inj₂ (x∈ʳ , refl)
  with destruct-Any-++ {xs = ys} x∈ʳ
... | inj₁ (_ , refl) = inj₂ $ inj₁ $ -, refl
... | inj₂ (_ , refl) = inj₂ $ inj₂ $ -, refl

-- ** _∈_

∈-++⁻∘∈-++⁺ˡ : (x∈ : x ∈ xs)
  → ∈-++⁻ xs {ys} (∈-++⁺ˡ {xs = xs}{ys} x∈)
  ≡ inj₁ x∈
∈-++⁻∘∈-++⁺ˡ = Any-++⁻∘Any-++⁺ˡ

∈-++⁻∘∈-++⁺ʳ : (y∈ : y ∈ ys)
  → ∈-++⁻ xs {ys} (∈-++⁺ʳ xs {ys} y∈)
  ≡ inj₂ y∈
∈-++⁻∘∈-++⁺ʳ = Any-++⁻∘Any-++⁺ʳ

∈-++⁻⇒∈-++⁺ˡ : ∀ {xs ys : List A}
  → (x∈ : x ∈ xs ++ ys)
    --———————————————————
  → case ∈-++⁻ xs {ys} x∈ of λ where
      (inj₁ x∈ˡ) → x∈ ≡ ∈-++⁺ˡ x∈ˡ
      (inj₂ x∈ʳ) → x∈ ≡ ∈-++⁺ʳ xs x∈ʳ
∈-++⁻⇒∈-++⁺ˡ {xs = xs} x∈ with ∈-++⁻ xs x∈ | Any-++⁻⇒Any-++⁺ {xs = xs} x∈
... | inj₁ _ | p = p
... | inj₂ _ | p = p

destruct-∈-++ : ∀ {xs ys : List A}
  → (x∈ : x ∈ xs ++ ys)
    --——————————————————
  → (∃ λ (x∈ˡ : x ∈ xs) → x∈ ≡ ∈-++⁺ˡ x∈ˡ)
  ⊎ (∃ λ (x∈ʳ : x ∈ ys) → x∈ ≡ ∈-++⁺ʳ xs x∈ʳ)
destruct-∈-++ = destruct-Any-++

destruct-∈-++² : ∀ {xs ys zs : List A}
  → (x∈ : x ∈ xs ++ ys ++ zs)
    --————————————————————————————————————
  → (∃ λ (x∈xs : x ∈ xs) → x∈ ≡ (∈-++⁺ˡ x∈xs))
  ⊎ (∃ λ (x∈ys : x ∈ ys) → x∈ ≡ (∈-++⁺ʳ xs $ ∈-++⁺ˡ x∈ys))
  ⊎ (∃ λ (x∈zs : x ∈ zs) → x∈ ≡ (∈-++⁺ʳ xs $ ∈-++⁺ʳ ys x∈zs))
destruct-∈-++² = destruct-Any-++²

-- ** _⊆_

⊆-tail : x ∷ xs ⊆ ys → xs ⊆ ys
⊆-tail = _∘ there

module _ {P : Pred A ℓ} (P? : Decidable¹ P) where
  ⊆-filter : xs ⊆ ys → filter P? xs ⊆ filter P? ys
  ⊆-filter {xs = xs}{ys} xs⊆ y∈ =
    let x∈ , Px = ∈-filter⁻ P? y∈
    in ∈-filter⁺ P? (xs⊆ x∈) Px

  destruct-∈-filter : ∀ {x xs} (x∈ : x ∈ xs) (Px : P x) →
    ∈-filter⁻ P? (∈-filter⁺ P? x∈ Px) .proj₁ ≡ x∈
  destruct-∈-filter {x} (here refl) Px rewrite dec-yes (P? x) Px .proj₂ = refl
  destruct-∈-filter (there {x = y} x∈) Px
    with IH ← destruct-∈-filter x∈ Px
    with P? y
  ... | yes p = cong there IH
  ... | no ¬p = cong there IH

-- ** map
∈-map⁻inverseˡ : ∀ (f : A → B) (f⁻¹ : B → A) →
  ∙ Inverse≡ˡ {A = B} f⁻¹ f
  ∙ y ∈ map f xs
    ───────────────────────
    f⁻¹ y ∈ xs
∈-map⁻inverseˡ {xs = xs} f f⁻¹ inv y∈ =
  let x , x∈ , eq = ∈-map⁻ f y∈
  in subst (_∈ xs) (sym $ trans (cong f⁻¹ eq) (inv _)) x∈

-- ** mapWith∈

∈-mapWith∈⁻ : ∀ {xs : List A} {f : ∀ {x} → x ∈ xs → B} {y : B}
  → y ∈ mapWith∈ xs f
  → ∃ λ x → Σ (x ∈ xs) λ x∈ → y ≡ f {x} x∈
∈-mapWith∈⁻ {xs = x ∷ _}  (here refl) = x , here refl , refl
∈-mapWith∈⁻ {xs = x ∷ xs} (there p)   = let x , x∈ , y≡ = ∈-mapWith∈⁻ p in x , there x∈ , y≡

mapWith∈-∀ : ∀ {xs : List A}  {f : ∀ {x : A} → x ∈ xs → B} {P : B → Type}
  → (∀ {x} x∈ → P (f {x} x∈))
  → (∀ {y} → y ∈ mapWith∈ xs f → P y)
mapWith∈-∀ {xs = x ∷ xs} ∀P {y} (here px)  rewrite px = ∀P (L.Any.here refl)
mapWith∈-∀ {xs = x ∷ xs} ∀P {y} (there y∈) = mapWith∈-∀ (∀P ∘ L.Any.there) y∈

map∘mapWith∈ : ∀ {A B C : Type}
    (g : B → C)  (xs : List A) (f : ∀ {x} → x ∈ xs → B)
  → map g (mapWith∈ xs f) ≡ mapWith∈ xs (g ∘ f)
map∘mapWith∈ _ [] _ = refl
map∘mapWith∈ _ (_ ∷ _) f = cong (_ ∷_) $ map∘mapWith∈ _ _ (f ∘ there)

mapWith∈∘map : ∀ {A B C : Type}
  (f : A → B) (xs : List A) (g : ∀ {x} → x ∈ map f xs → C)
  → mapWith∈ (map f xs) g ≡ mapWith∈ xs (g ∘ ∈-map⁺ f)
mapWith∈∘map _ [] _ = refl
mapWith∈∘map _ (_ ∷ _) g = cong (_ ∷_) $ mapWith∈∘map _ _ (g ∘ there)

-- ** Unique

unique-∈ : Unique (x ∷ xs) → x ∉ xs
unique-∈ {xs = []} u ()
unique-∈ {xs = x ∷ xs} ((x≢x ∷ _) ∷ _) (here refl) = x≢x refl
unique-∈ {xs = x ∷ xs} ((_ ∷ p) ∷ _)   (there x∈)  = L.All.All¬⇒¬Any p x∈

Unique-mapWith∈ : ∀ {A B : Type} {xs : List A} {f : ∀ {x} → x ∈ xs → B}
  → (∀ {x x′} {x∈ : x ∈ xs} {x∈′ : x′ ∈ xs} → f x∈ ≡ f x∈′ → L.Any.index x∈ ≡ L.Any.index x∈′)
  → Unique (mapWith∈ xs f)
Unique-mapWith∈ {xs = []}     {f = f} f≡ = []
Unique-mapWith∈ {xs = x ∷ xs} {f = f} f≡
  = L.All.tabulate (mapWith∈-∀ {P = f (L.Any.here refl) ≢_} λ _ eq → case f≡ eq of λ () )
  ∷ Unique-mapWith∈ {xs = xs} (F.suc-injective ∘ f≡)

-- ** Any/All

All∉[] : All (_∉ []) ys
All∉[] {ys = []}     = []
All∉[] {ys = y ∷ ys} = (λ ()) ∷ All∉[] {ys = ys}

Any-front : ∀ {P : Pred₀ A} {xs : List A} → Any P xs → List A
Any-front {xs = xs} x∈ = take (indexℕ x∈) xs

Any-tail : ∀ {P : Pred₀ A} {xs : List A} → Any P xs → List A
Any-tail {xs = xs} x∈ = drop (suc $ indexℕ x∈) xs
-- Any-tail {xs = _ ∷ xs}     (here _)   = xs
-- Any-tail {xs = _ ∷ _ ∷ xs} (there x∈) = ∈-tail x∈

lookup∈ : (p : Any P xs) → L.Any.lookup p ∈ xs
lookup∈ = λ where
  (here _)  → here refl
  (there p) → there $′ lookup∈ p

⊆-resp-Any : _⊆_ Respects˘ (Any P)
⊆-resp-Any xs⊆ = λ where
  (here px) → L.Any.map (λ{ refl → px }) (xs⊆ $ here refl)
  (there p) → ⊆-resp-Any (xs⊆ ∘ there) p

-- ** drop

∈-drop⁻ : ∀ {n} {A : Type} {x : A} {xs : List A}
  → x ∈ drop n xs
  → x ∈ xs
∈-drop⁻ {n = 0} x∈ = x∈
∈-drop⁻ {n = suc n} {xs = _ ∷ xs} x∈ = there $ ∈-drop⁻ {n = n} x∈

-- ** splitAt

splitAt-∈-++⁺ˡ :
  (x∈ : x ∈ xs)
  → splitAtˡ (ys ++ xs) (index⁺ $ ∈-++⁺ʳ ys x∈)
  ≡ ys ++ splitAtˡ xs (index⁺ x∈)
splitAt-∈-++⁺ˡ {ys = []}     _  = refl
splitAt-∈-++⁺ˡ {ys = y ∷ ys} x∈ = cong (y ∷_) (splitAt-∈-++⁺ˡ {ys = ys} x∈)

splitAt-∈-++⁺ʳ :
  (x∈ : x ∈ xs)
  → splitAtʳ xs (index⁺ x∈)
  ≡ splitAtʳ (ys ++ xs) (index⁺ $ ∈-++⁺ʳ ys x∈)
splitAt-∈-++⁺ʳ {ys = []}     _  = refl
splitAt-∈-++⁺ʳ {ys = _ ∷ ys} x∈ = splitAt-∈-++⁺ʳ {ys = ys} x∈

-- ** indexℕ

indexℕ-++⁺ˡ : (x∈ : x ∈ xs) → indexℕ (∈-++⁺ˡ {ys = ys} x∈) ≡ indexℕ x∈
indexℕ-++⁺ˡ = λ where
  (here _) → refl
  (there x∈) → cong suc (indexℕ-++⁺ˡ x∈)

-- ** Last∈

LastAny : ∀ {A : Type ℓ} {P : Pred A ℓ′} {xs : List A} → Pred (Any P xs) ℓ
LastAny (there p) = LastAny p
LastAny {xs = _ ∷ xs} (here _) = Null xs

Last∈ : Pred (x ∈ xs) _
-- Last = Null ∘ Any-tail
Last∈ = LastAny

Last∈-there⁺ : ∀ (x∈ : x ∈ xs) → Last∈ x∈ → Last∈ (there {x = x′} x∈)
Last∈-there⁺ _ = id

module _ (f : P ⊆¹ Q) where
  LastAny-map⁺ :
    (p : Any P xs)
    → LastAny p
    → LastAny (L.Any.map f p)
  LastAny-map⁺ (here _)  = id
  LastAny-map⁺ (there p) = LastAny-map⁺ p

  LastAny-map⁻ :
    (p : Any P xs)
    → LastAny (L.Any.map f p)
    → LastAny p
  LastAny-map⁻ (here _)  = id
  LastAny-map⁻ (there p) = LastAny-map⁻ p

module _ (f : A → B) (P : Pred B ℓ) where
  LastAny-map⁺⁺ :
    (p : Any (P ∘ f) xs)
    → LastAny p
    → LastAny (L.Any.map⁺ {P = P} p)
  LastAny-map⁺⁺ (here _)  refl = refl
  LastAny-map⁺⁺ (there p) lp   = LastAny-map⁺⁺ p lp

Last∈-map⁺ : ∀ (f : A → B) (x∈ : x ∈ xs) →
  Last∈ x∈
  ───────────────────
  Last∈ (∈-map⁺ f x∈)
Last∈-map⁺ f (here _)  refl = refl
Last∈-map⁺ f (there p) lp   = Last∈-map⁺ f p lp

∉-++⁻ :
  x ∉ xs ++ ys
  ───────────────────
  (x ∉ xs) × (x ∉ ys)
∉-++⁻ x∉ = (x∉ ∘ ∈-++⁺ˡ) , (x∉ ∘ ∈-++⁺ʳ _)

∉-++⁻ˡ : x ∉ xs ++ ys → x ∉ xs
∉-++⁻ˡ = proj₁ ∘ ∉-++⁻
∉-++⁻ʳ : x ∉ xs ++ ys → x ∉ ys
∉-++⁻ʳ = proj₂ ∘ ∉-++⁻

∉-++⁺ :
  ∙ x ∉ xs
  ∙ x ∉ ys
    ────────────
    x ∉ xs ++ ys
∉-++⁺ x∉ˡ x∉ʳ = ∈-++⁻ _ >≡> Sum.[ x∉ˡ , x∉ʳ ]

∉-∷⁺ : y ≢ x → y ∉ xs → y ∉ x ∷ xs
∉-∷⁺ y≢ y∉ = λ where
  (here refl) → y≢ refl
  (there y∈)  → y∉ y∈

∉-∷⁻ : y ∉ x ∷ xs → y ≢ x × y ∉ xs
∉-∷⁻ y∉ = (λ where refl → y∉ $ here refl) , y∉ ∘ there

module _ (P? : Decidable¹ P) where
  ∉-filter⁻ : x ∉ filter P? xs → P x → x ∉ xs
  ∉-filter⁻ x∉ px = x∉ ∘ flip (∈-filter⁺ P?) px

  ∉-filter⁺ : x ∉ xs → x ∉ filter P? xs
  ∉-filter⁺ = _∘ (proj₁ ∘ ∈-filter⁻ P?)

-- ** aligning & zipping

{-
∈-alignWith⁺ˡ :
∈-alignWith⁺ʳ :
∈-alignWith⁻ :

∈-zipWith⁺ˡ :
∈-zipWith⁺ʳ :
∈-zipWith⁻ :

∈-unalignWith⁺ˡ :
∈-unalignWith⁺ʳ :
∈-unalignWith⁻ :

∈-unzipWith⁺ˡ :
∈-unzipWith⁺ʳ :
∈-unzipWith⁻ :

∈-partitionSumsWith⁺ˡ
∈-partitionSumsWith⁺ʳ
∈-partitionSumsWith⁻

∈-align⁺ˡ : a ∈ as → this a ∈ align as bs
∈-align⁺ʳ : b ∈ bs → that b ∈ align as bs
∈-align⁻

∈-zip⁺ˡ
∈-zip⁺ʳ
∈-zip⁻

∈-unalign⁺ˡ
∈-unalign⁺ʳ
∈-unalign⁻

∈-unzip⁺ˡ
∈-unzip⁺ʳ
∈-unzip⁻
-}

private variable
  a : A; b : B
  abs abs′ : List (A ⊎ B)

∈-partitionSums⁺ˡ ∈-lefts⁺ : inj₁ a ∈ abs → a ∈ lefts abs
∈-partitionSums⁺ˡ {abs = inj₁ _ ∷ _} (here refl) = here refl
∈-partitionSums⁺ˡ {abs = inj₁ _ ∷ _} (there a∈)  = there $ ∈-partitionSums⁺ˡ a∈
∈-partitionSums⁺ˡ {abs = inj₂ _ ∷ _} (there a∈)  = ∈-partitionSums⁺ˡ a∈
∈-lefts⁺ = ∈-partitionSums⁺ˡ

∈-partitionSums⁺ʳ ∈-rights⁺ : inj₂ b ∈ abs → b ∈ rights abs
∈-partitionSums⁺ʳ {abs = inj₂ _ ∷ _} (here refl) = here refl
∈-partitionSums⁺ʳ {abs = inj₁ _ ∷ _} (there b∈)  = ∈-partitionSums⁺ʳ b∈
∈-partitionSums⁺ʳ {abs = inj₂ _ ∷ _} (there b∈)  = there $ ∈-partitionSums⁺ʳ b∈
∈-rights⁺ = ∈-partitionSums⁺ʳ

∈-partitionSums⁻ˡ ∈-lefts⁻ : a ∈ lefts abs → inj₁ a ∈ abs
∈-partitionSums⁻ˡ {abs = inj₁ _ ∷ _} (here refl) = here refl
∈-partitionSums⁻ˡ {abs = inj₁ _ ∷ _} (there a∈)  = there $′ ∈-partitionSums⁻ˡ a∈
∈-partitionSums⁻ˡ {abs = inj₂ _ ∷ _} a∈          = there $′ ∈-partitionSums⁻ˡ a∈
∈-lefts⁻ = ∈-partitionSums⁻ˡ

∈-partitionSums⁻ʳ ∈-rights⁻ : b ∈ rights abs → inj₂ b ∈ abs
∈-partitionSums⁻ʳ {abs = inj₁ _ ∷ _} b∈          = there $′ ∈-partitionSums⁻ʳ b∈
∈-partitionSums⁻ʳ {abs = inj₂ _ ∷ _} (here refl) = here refl
∈-partitionSums⁻ʳ {abs = inj₂ _ ∷ _} (there b∈)  = there $′ ∈-partitionSums⁻ʳ b∈
∈-rights⁻ = ∈-partitionSums⁻ʳ

-- ∈-merge⁺ˡ :
-- ∈-merge⁺ʳ :
-- ∈-merge⁻ :
