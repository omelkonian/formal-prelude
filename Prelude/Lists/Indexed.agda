------------------------------------------------------------------------
-- Indexed operations on lists.

{-# OPTIONS --safe #-}
module Prelude.Lists.Indexed where

open import Prelude.Init; open SetAsType
open L.Mem using (_∈_; ∈-map⁺; mapWith∈)
open Nat   using (_<_; _≤_; ≤-pred)
open F     using (toℕ; fromℕ<)
open import Prelude.General
open import Prelude.Bifunctor
open import Prelude.InferenceRules
open import Prelude.Split

private variable
  A : Type ℓ; B : Type ℓ′
  P Q : Pred A ℓ″
  xs : List A; ys : List B
  x : A
  m n : ℕ

Index : List A → Type
Index = Fin ∘ length

Index⁺ : List A → Type
Index⁺ = Fin ∘ suc ∘ length

infix 3 _‼_
_‼_ : (vs : List A) → Index vs → A
_‼_ = L.lookup

infix 3 _⁉_
_⁉_ : List A → ℕ → Maybe A
[]       ⁉ _     = nothing
(x ∷ xs) ⁉ zero  = just x
(x ∷ xs) ⁉ suc n = xs ⁉ n

remove : (vs : List A) → Index vs → List A
remove []       ()
remove (_ ∷ xs) fzero    = xs
remove (x ∷ vs) (fsuc f) = x ∷ remove vs f

_at_⟨_⟩ : (vs : List A) → Index vs → A → List A
[]       at ()       ⟨ _ ⟩
(_ ∷ xs) at fzero    ⟨ x ⟩ = x ∷ xs
(y ∷ vs) at (fsuc f) ⟨ x ⟩ = y ∷ (vs at f ⟨ x ⟩)

_at_⟨_⟩remove_ : (vs : List A) → Index vs → A → Index vs → List A
[] at () ⟨ _ ⟩remove ()
(_ ∷ vs) at fzero  ⟨ _  ⟩remove fzero  = vs
(_ ∷ vs) at fzero  ⟨ xv ⟩remove fsuc y = xv ∷ remove vs y
(_ ∷ vs) at fsuc x ⟨ xv ⟩remove fzero  = vs at x ⟨ xv ⟩
(v ∷ vs) at fsuc x ⟨ xv ⟩remove fsuc y = v ∷ vs at x ⟨ xv ⟩remove y

indices : List A → List ℕ
indices xs = upTo (length xs)

fin-indices : (xs : List A) → List (Index xs)
fin-indices = allFin ∘ length

enumerate : (xs : List A) → List (Index xs × A)
enumerate xs = zip (fin-indices xs) xs

findElem : ∀ {P : Pred₀ A} → Decidable¹ P → List A → Maybe (A × List A)
findElem P? xs with L.Any.any? P? xs
... | yes px = let i = L.Any.index px in just ((xs ‼ i) , remove xs i)
... | no  _  = nothing

length≡⇒Ix : ∀ (xs : List A) (ys : List B) →
  length xs ≡ length ys
  ─────────────────────
  Index xs ↔ Index ys
length≡⇒Ix []       []       eq = (λ ()) , (λ ())
length≡⇒Ix (x ∷ xs) (y ∷ ys) eq =
  let IH : Index xs ↔ Index ys
      IH = length≡⇒Ix xs ys $ Nat.suc-injective eq
  in (λ where 0F → 0F; (fsuc i) → fsuc (IH .proj₁ i))
   , (λ where 0F → 0F; (fsuc i) → fsuc (IH .proj₂ i))

module ∣length≡⇒Ix∣ (xs : List A) (ys : List B) (len≡ : length xs ≡ length ys) where
  ↝ = (Index xs → Index ys) ∋ length≡⇒Ix xs ys len≡ .proj₁
  ↜ = (Index ys → Index xs) ∋ length≡⇒Ix xs ys len≡ .proj₂

length-allFin : ∀ n → length (allFin n) ≡ n
length-allFin n = L.length-tabulate id

module _ (xs : List A) (ys : List B) where
  length-zip : length (zip xs ys) ≡ length xs ⊓ length ys
  length-zip = L.length-zipWith _,_ xs ys

  length-zip≡ˡ : length xs ≡ length ys → length (zip xs ys) ≡ length xs
  length-zip≡ˡ len≡ =
    begin
      length (zip xs ys)
    ≡⟨ length-zip ⟩
      length xs ⊓ length ys
    ≡⟨ Nat.m≤n⇒m⊓n≡m $ Nat.≤-reflexive $ len≡ ⟩
      length xs
    ∎ where open ≡-Reasoning

  length-zip≡ʳ : length xs ≡ length ys → length (zip xs ys) ≡ length ys
  length-zip≡ʳ len≡ = trans (length-zip≡ˡ len≡) len≡

length-enumerate : length (enumerate xs) ≡ length xs
length-enumerate {xs = xs} =
  begin
    length (enumerate xs)
  ≡⟨ length-zip (fin-indices xs) xs ⟩
    length (fin-indices xs) ⊓ length xs
  ≡⟨ Nat.m≥n⇒m⊓n≡n $ Nat.≤-reflexive $ sym $ length-allFin (length xs) ⟩
    length xs
  ∎ where open ≡-Reasoning

‼-zip⁺ˡ : Index xs → {_ : length xs ≤ length ys} → Index (zip xs ys)
‼-zip⁺ˡ {xs = []} ()
‼-zip⁺ˡ {xs = _ ∷ xs} {ys = _ ∷ _} = λ where
  0F → 0F
  (fsuc i) {s≤s p} → fsuc (‼-zip⁺ˡ {xs = xs} i {p})
‼-zip⁺ˡ {xs = _ ∷ _} {ys = []} _ {()}

‼-zip⁺ʳ : Index ys → {_ : length ys ≤ length xs} → Index (zip xs ys)
‼-zip⁺ʳ {ys = []}     {xs = _} ()
‼-zip⁺ʳ {ys = _ ∷ ys} {xs = _ ∷ xs} = λ where
  0F → 0F
  (fsuc i) {s≤s p} → fsuc (‼-zip⁺ʳ {ys = ys} {xs = xs} i {p})
‼-zip⁺ʳ {ys = _ ∷ _} {xs = []} _ {()}

‼-zip⁻ˡ : Index (zip xs ys) → Index xs
‼-zip⁻ˡ {xs = []} ()
‼-zip⁻ˡ {xs = _ ∷ _}  {ys = []} ()
‼-zip⁻ˡ {xs = _ ∷ xs} {ys = _ ∷ _} = λ where
  0F → 0F
  (fsuc i) → fsuc (‼-zip⁻ˡ {xs = xs} i)

‼-zip⁻ʳ : Index (zip xs ys) → Index ys
‼-zip⁻ʳ {xs = []} ()
‼-zip⁻ʳ {xs = _ ∷ _}  {ys = []} ()
‼-zip⁻ʳ {xs = _ ∷ xs} {ys = _ ∷ _} = λ where
  0F → 0F
  (fsuc i) → fsuc (‼-zip⁻ʳ {xs = xs} i)

mapWithIx : (xs : List A) → (A → Index xs → B) → List B
mapWithIx xs f = map (uncurry (flip f)) $ enumerate xs

length-mapWithIx : (f : A → Index xs → B) →
  length (mapWithIx xs f) ≡ length xs
length-mapWithIx {xs = xs} f
  = trans (L.length-map (uncurry (flip f)) (enumerate xs))
          (length-enumerate {xs = xs})

length-mapWith∈ : (f : ∀ {x} → x L.Mem.∈ xs → B) →
  length (L.Mem.mapWith∈ xs f) ≡ length xs
length-mapWith∈ {xs = []} _ = refl
length-mapWith∈ {xs = _ ∷ xs} f = cong suc $ length-mapWith∈ {xs = xs} (f ∘ there)

module _ (f : A → B) {xs : List A} where
  open ∣length≡⇒Ix∣ (map f xs) xs (L.length-map f xs)
    renaming (↝ to ‼-map⁻; ↜ to ‼-map⁺) public

module _  {xs : List A} (f : ∀ {x : A} → x ∈ xs → B) where
  open ∣length≡⇒Ix∣ (mapWith∈ xs f) xs (length-mapWith∈ {xs = xs} f)
    renaming (↝ to ‼-mapWith∈⁻; ↜ to ‼-mapWith∈⁺) public

module _  {xs : List A} (f : A → Index xs → B) where
  open ∣length≡⇒Ix∣ (mapWithIx xs f) xs (length-mapWithIx {xs = xs} f)
    renaming (↝ to ‼-mapWithIx⁻; ↜ to ‼-mapWithIx⁺) public

module _ {A : Type} {xs : List A} where
  open ∣length≡⇒Ix∣ (enumerate xs) xs (length-enumerate {xs = xs})
    renaming (↝ to ‼-enumerate⁻; ↜ to ‼-enumerate⁺) public

-- ** indexℕ

indexℕ : Any P xs → ℕ
indexℕ = toℕ ∘ L.Any.index

indexℕ-Any-map : ∀ {f : P ⊆¹ Q}
  → (x∈ : Any P xs)
  → indexℕ (L.Any.map f x∈)
  ≡ indexℕ x∈
indexℕ-Any-map = λ where
  (here _)  → refl
  (there p) → cong suc $ indexℕ-Any-map p

indexℕ-Any-map⁺ : ∀ {f : A → B} {P : Pred B ℓ}
  → (x∈ : Any (P ∘ f) xs)
  → indexℕ (L.Any.map⁺ {f = f} {P = P} x∈)
  ≡ indexℕ x∈
indexℕ-Any-map⁺ = λ where
  (here _)  → refl
  (there p) → cong suc $ indexℕ-Any-map⁺ p

zip-∈ : ∀ {xs : List A} {ys : List B} {x : A} {y : B}
  → (x , y) ∈ zip xs ys → (x ∈ xs) × (y ∈ ys)
zip-∈ {xs = _ ∷ xs} {_ ∷ ys} (here refl) = here refl , here refl
zip-∈ {xs = _ ∷ xs} {_ ∷ ys} (there xy∈) with zip-∈ xy∈
... | (x∈ , y∈) = there x∈ , there y∈

ix∈→x∈ : ∀ {xs : List A} {i : Index xs} {x : A}
  → (i , x) ∈ enumerate xs → x ∈ xs
ix∈→x∈ = proj₂ ∘ zip-∈

index⁺ : Any P xs → Index⁺ xs
index⁺ = fsuc ∘ L.Any.index

splitAt : ∀ (xs : List A) → Index⁺ xs → List A × List A
splitAt xs       fzero    = [] , xs
splitAt (x ∷ xs) (fsuc i) = map₁ (x ∷_) (splitAt xs i)

splitAtˡ splitAtʳ : ∀ (xs : List A) → Index⁺ xs → List A
splitAtˡ = proj₁ ∘₂ splitAt
splitAtʳ = proj₂ ∘₂ splitAt

splitAt′ : ∀ (xs : List A) → ℕ → Maybe (List A × List A)
splitAt′ xs n with n Nat.<? suc (length xs)
... | yes n≤ = just $ splitAt xs (F.fromℕ< {m = n} {n = suc (length xs)} n≤)
... | no  _  = nothing

splitAt≡ : (i : Index⁺ xs)
 → splitAt′ xs (toℕ i) ≡ just (splitAt xs i)
splitAt≡ {xs = xs} i
  with toℕ i Nat.<? suc (length xs)
... | yes i≤ = cong just (cong (splitAt xs) (F.fromℕ<-toℕ i i≤))
... | no  i≰ = ⊥-elim $ i≰ (F.toℕ<n i)

splitAt⁺ʳ : ∀ (xs : List A) → Index xs
  → Σ[ xsˡ ∈ List⁺ A ] Σ[ xsʳ ∈ List A ]
      L.NE.length xsˡ + length xsʳ ≡ length xs
splitAt⁺ʳ (x ∷ xs) fzero    = x ∷ [] , xs , refl
splitAt⁺ʳ (x ∷ xs) (fsuc i) = let xsˡ , xsʳ , p = splitAt⁺ʳ xs i
                              in  x ∷⁺ xsˡ , xsʳ , cong suc p

instance
  Split-∈ : ∀ {A : Type ℓ} {xs : List A} {P : Pred A ℓ′} →
    Any P xs -splitsInto- List A
  Split-∈ {xs = xs} .split = splitAt xs ∘ index⁺

private
  _ : splitAt⁺ʳ (0 ∷ 1 ∷ []) (# 0) ≡ (L.NE.[ 0 ] , [ 1 ] , refl)
  _ = refl

  _ : splitAt⁺ʳ (0 ∷ 1 ∷ []) (# 1) ≡ (0 ∷ 1 ∷ [] , [] , refl)
  _ = refl

length-∈∙left : {xs : List A} (x∈ : Any P xs) → length (x∈ ∙left) ≡ suc (indexℕ x∈)
length-∈∙left {xs = x ∷ xs} (here _) = refl
length-∈∙left {xs = x ∷ xs} (there x∈) rewrite length-∈∙left {xs = xs} x∈ = refl

map-map₁-zip : ∀ {A B C : Type} {xs : List A} {ys : List B} (f : A → C)
  → map (map₁ f) (zip xs ys)
  ≡ zip (map f xs) ys
map-map₁-zip {xs = []}     {ys = _}      f = refl
map-map₁-zip {xs = _ ∷ xs} {ys = []}     f = refl
map-map₁-zip {xs = _ ∷ xs} {ys = _ ∷ ys} f rewrite map-map₁-zip {xs = xs} {ys = ys} f = refl

enum∈-∷ : ∀ {A : Type} {x y : A} {xs : List A} {i : Index xs}
  → (i , y) ∈ enumerate xs
  → (fsuc i , y) ∈ enumerate (x ∷ xs)
enum∈-∷ {x = x} {y = y} {xs = xs} {i = i} ix∈
  with ∈-map⁺ (map₁ fsuc) ix∈
... | ix∈′
  rewrite map-map₁-zip {xs = L.tabulate {n = length xs} id} {ys = xs} fsuc
        | L.map-tabulate {n = length xs} (λ x → x) fsuc
        = there ix∈′

x∈→ix∈ : ∀ {A : Type} {xs : List A} {x : A}
  → (x∈ : x ∈ xs) → ((L.Any.index x∈ , x) ∈ enumerate xs)
x∈→ix∈ (here refl) = here refl
x∈→ix∈ {xs = _ ∷ xs} (there x∈) = enum∈-∷ (x∈→ix∈ x∈)

mapEnumWith∈ : (xs : List A) → (∀ (i : Index xs) (x : A) → x ∈ xs → B) → List B
mapEnumWith∈ xs f = mapWith∈ (enumerate xs) λ{ {(i , x)} ix∈ → f i x (ix∈→x∈ ix∈) }

map∘zip∘tabulate⟨fsuc⟩≈map⟨fsuc⟩∘zip∘tabulate : ∀ {A B : Type} {m : ℕ} (xs : List A) {P : Fin (suc m) × A → B} {f : Index xs → Fin m}
 → map P (zip (L.tabulate {n = length xs} (fsuc ∘ f)) xs)
 ≡ map (P ∘ map₁ fsuc) (zip (L.tabulate {n = length xs} f) xs)
map∘zip∘tabulate⟨fsuc⟩≈map⟨fsuc⟩∘zip∘tabulate [] = refl
map∘zip∘tabulate⟨fsuc⟩≈map⟨fsuc⟩∘zip∘tabulate {A}{B}{m} (x ∷ xs) {P = P} {f = f} = cong (_ ∷_) $ map∘zip∘tabulate⟨fsuc⟩≈map⟨fsuc⟩∘zip∘tabulate {A}{B}{m} xs {P = P} {f = f ∘ fsuc}

‼-suc : ∀ {x : A} {xs : List A} {i : Index xs}
  → (x ∷ xs ‼ fsuc i)
  ≡ (xs ‼ i)
‼-suc = refl

‼-map : ∀ {xs : List A} {f : A → B}
  → Index xs
  → Index (map f xs)
‼-map {xs = x ∷ xs} fzero    = fzero
‼-map {xs = x ∷ xs} (fsuc i) = fsuc (‼-map {xs = xs} i)

‼-mapWith∈ : ∀ {xs : List A} {f : ∀ {x} → x ∈ xs → B}
  → Index xs
  → Index (mapWith∈ xs f)
‼-mapWith∈ {xs = x ∷ xs} fzero    = fzero
‼-mapWith∈ {xs = x ∷ xs} (fsuc i) = fsuc (‼-mapWith∈ {xs = xs} i)

map-‼ : ∀ {xs : List A} {x : A} {f : A → B} (x∈ : x ∈ xs)
  → (map f xs ‼ ‼-map {xs = xs} {f = f} (L.Any.index x∈)) ≡ f x
map-‼ (here refl) = refl
map-‼ {xs = _ ∷ xs} {f = f} (there x∈) rewrite map-‼ {xs = xs} {f = f} x∈ = refl

‼→⁉ : ∀ {xs : List A} {ix : Index xs}
    → just (xs ‼ ix) ≡ (xs ⁉ toℕ ix)
‼→⁉ {xs = []}     {()}
‼→⁉ {xs = x ∷ xs} {fzero}   = refl
‼→⁉ {xs = x ∷ xs} {fsuc ix} = ‼→⁉ {xs = xs} {ix}

‼-index : (x∈xs : x ∈ xs)
        → (xs ‼ L.Any.index x∈xs) ≡ x
‼-index (here refl) = refl
‼-index (there x∈)  rewrite ‼-index x∈ = refl

toℕ< : ∀ (fin : Fin n) → toℕ fin < n
toℕ< fzero    = s≤s z≤n
toℕ< (fsuc f) = s≤s (toℕ< f)

fromℕ<∘toℕ< : ∀ (i : Fin n) → fromℕ< (toℕ< i) ≡ i
fromℕ<∘toℕ< fzero    = refl
fromℕ<∘toℕ< (fsuc i) rewrite fromℕ<∘toℕ< i = refl

‼-fromℕ<∘toℕ< : (i : Index xs)
              → (xs ‼ fromℕ< (toℕ< i)) ≡ (xs ‼ i)
‼-fromℕ<∘toℕ< i rewrite fromℕ<∘toℕ< i = refl

fromℕ<-≡ : (p₁ : m < length xs)
         → (p₂ : m < length xs)
         → fromℕ< p₁ ≡ fromℕ< p₂
fromℕ<-≡ {m = zero}  {xs = x ∷ xs} p₁ p₂ = refl
fromℕ<-≡ {m = suc m} {xs = x ∷ xs} p₁ p₂ rewrite fromℕ<-≡ {m = m} {xs = xs} (≤-pred p₁) (≤-pred p₂) = refl

‼-fromℕ<-≡ : (p₁ : m < length xs)
           → (p₂ : m < length ys)
           → xs ≡ ys
           → (xs ‼ fromℕ< p₁)
           ≡ (ys ‼ fromℕ< p₂)
‼-fromℕ<-≡ {m = m} {xs = xs} p₁ p₂ refl rewrite fromℕ<-≡ {m = m} {xs = xs} p₁ p₂ = refl

proj₁∘find : (x∈xs : x ∈ xs)
           → proj₁ (find x∈xs) ≡ x
proj₁∘find (here refl) = refl
proj₁∘find (there x∈)  = proj₁∘find x∈

just-⁉⇒∈ : ∀ {i : ℕ}
  → (xs ⁉ i) ≡ just x
  → x ∈ xs
just-⁉⇒∈ {xs = _ ∷ _}  {i = zero}  ⁉≡just = here (M.just-injective (sym ⁉≡just))
just-⁉⇒∈ {xs = _ ∷ xs} {i = suc i} ⁉≡just = there (just-⁉⇒∈ {xs = xs} {i = i} ⁉≡just)
