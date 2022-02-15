------------------------------------------------------------------------
-- Indexed operations on lists.

module Prelude.Lists.Indexed where

open import Prelude.Init
open L.Mem using (_∈_; ∈-map⁺; mapWith∈)
open Nat   using (_<_; ≤-pred)
open F     using (toℕ; fromℕ<)
open import Prelude.Bifunctor

private variable
  A : Set ℓ
  B : Set ℓ′

  m n : ℕ
  x : A
  xs ys : List A

Index : List A → Set
Index = Fin ∘ length

Index⁺ : List A → Set
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

zip-∈ : ∀ {xs : List A} {ys : List B} {x : A} {y : B}
  → (x , y) ∈ zip xs ys → (x ∈ xs) × (y ∈ ys)
zip-∈ {xs = _ ∷ xs} {_ ∷ ys} (here refl) = here refl , here refl
zip-∈ {xs = _ ∷ xs} {_ ∷ ys} (there xy∈) with zip-∈ xy∈
... | (x∈ , y∈) = there x∈ , there y∈

ix∈→x∈ : ∀ {xs : List A} {i : Index xs} {x : A}
  → (i , x) ∈ enumerate xs → x ∈ xs
ix∈→x∈ = proj₂ ∘ zip-∈

splitAt : ∀ (xs : List A) → Index⁺ xs → List A × List A
splitAt xs       fzero    = [] , xs
splitAt (x ∷ xs) (fsuc i) = map₁ (x ∷_) (splitAt xs i)

splitAt⁺ʳ : ∀ (xs : List A) → Index xs
  → Σ[ xsˡ ∈ List⁺ A ] Σ[ xsʳ ∈ List A ]
      L.NE.length xsˡ + length xsʳ ≡ length xs
splitAt⁺ʳ (x ∷ xs) fzero    = x ∷ [] , xs , refl
splitAt⁺ʳ (x ∷ xs) (fsuc i) = let xsˡ , xsʳ , p = splitAt⁺ʳ xs i
                              in  x ∷⁺ xsˡ , xsʳ , cong suc p

private
  _ : splitAt⁺ʳ (0 ∷ 1 ∷ []) (# 0) ≡ (L.NE.[ 0 ] , [ 1 ] , refl)
  _ = refl

  _ : splitAt⁺ʳ (0 ∷ 1 ∷ []) (# 1) ≡ (0 ∷ 1 ∷ [] , [] , refl)
  _ = refl

map-map₁-zip : ∀ {A B C : Set} {xs : List A} {ys : List B} (f : A → C)
  → map (map₁ f) (zip xs ys)
  ≡ zip (map f xs) ys
map-map₁-zip {xs = []}     {ys = _}      f = refl
map-map₁-zip {xs = _ ∷ xs} {ys = []}     f = refl
map-map₁-zip {xs = _ ∷ xs} {ys = _ ∷ ys} f rewrite map-map₁-zip {xs = xs} {ys = ys} f = refl

enum∈-∷ : ∀ {A : Set} {x y : A} {xs : List A} {i : Index xs}
  → (i , y) ∈ enumerate xs
  → (fsuc i , y) ∈ enumerate (x ∷ xs)
enum∈-∷ {x = x} {y = y} {xs = xs} {i = i} ix∈
  with ∈-map⁺ (map₁ fsuc) ix∈
... | ix∈′
  rewrite map-map₁-zip {xs = L.tabulate {n = length xs} id} {ys = xs} fsuc
        | L.map-tabulate {n = length xs} (λ x → x) fsuc
        = there ix∈′

x∈→ix∈ : ∀ {A : Set} {xs : List A} {x : A}
  → (x∈ : x ∈ xs) → ((L.Any.index x∈ , x) ∈ enumerate xs)
x∈→ix∈ (here refl) = here refl
x∈→ix∈ {xs = _ ∷ xs} (there x∈) = enum∈-∷ (x∈→ix∈ x∈)

mapEnumWith∈ : (xs : List A) → (∀ (i : Index xs) (x : A) → x ∈ xs → B) → List B
mapEnumWith∈ xs f = mapWith∈ (enumerate xs) λ{ {(i , x)} ix∈ → f i x (ix∈→x∈ ix∈) }

map∘zip∘tabulate⟨fsuc⟩≈map⟨fsuc⟩∘zip∘tabulate : ∀ {A B : Set} {m : ℕ} (xs : List A) {P : Fin (suc m) × A → B} {f : Index xs → Fin m}
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

map-‼ : ∀ {xs : List A} {x : A} {f : A → B} (x∈ : x ∈ xs)
  → (map f xs ‼ ‼-map {xs = xs} {f = f} (L.Any.index x∈)) ≡ f x
map-‼ (here refl) = refl
map-‼ {xs = _ ∷ xs} {f = f} (there x∈) rewrite map-‼ {xs = xs} {f = f} x∈ = refl

indexℕ : (x∈ : x ∈ xs) → ℕ
indexℕ = toℕ ∘ L.Any.index

‼→⁉ : ∀ {xs : List A} {ix : Index xs}
    → just (xs ‼ ix) ≡ (xs ⁉ toℕ ix)
‼→⁉ {xs = []}     {()}
‼→⁉ {xs = x ∷ xs} {fzero}   = refl
‼→⁉ {xs = x ∷ xs} {fsuc ix} = ‼→⁉ {xs = xs} {ix}

⁉→‼ : ∀ {xs ys : List A} {ix : Index xs}
    → (len≡ : length xs ≡ length ys)
    → (xs ⁉ toℕ ix) ≡ (ys ⁉ toℕ ix)
    → (xs ‼ ix) ≡ (ys ‼ F.cast len≡ ix)
⁉→‼ {xs = []}     {[]}      {ix}      len≡ eq   = refl
⁉→‼ {xs = []}     {x ∷ ys}  {ix}      () eq
⁉→‼ {xs = x ∷ xs} {[]}      {ix}      () eq
⁉→‼ {xs = x ∷ xs} {.x ∷ ys} {fzero}   len≡ refl = refl
⁉→‼ {xs = x ∷ xs} {y ∷ ys}  {fsuc ix} len≡ eq
  rewrite ‼-suc {x = x} {xs} {ix}
        = ⁉→‼ {xs = xs} {ys} {ix} (Nat.suc-injective len≡) eq

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
