{-# OPTIONS --allow-unsolved-metas #-}
------------------------------------------------------------------------
-- List utilities
------------------------------------------------------------------------

module Prelude.Lists where

open import Level            using (Level)
open import Function         using (_∘_; _∋_; case_of_; id; _$_)
open import Function.Bundles using (_↔_)

open import Data.Empty    using (⊥; ⊥-elim)
open import Data.Unit     using (⊤; tt)
open import Data.Product  using (_×_; _,_; map₁; map₂; proj₁; proj₂; <_,_>; ∃-syntax)
open import Data.Sum      using (_⊎_; inj₁; inj₂; isInj₁; isInj₂)
open import Data.Maybe    using (Maybe; just; nothing)
open import Data.Fin      using (Fin; toℕ; fromℕ<; inject≤; cast; inject₁)
  renaming (zero to fzero; suc to fsuc; _≟_ to _≟ᶠ_)
open import Data.Nat      using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s; pred; _<?_; ≤-pred)
open import Data.List     using ( List; []; [_]; _∷_; _∷ʳ_; _++_; map; mapMaybe; concatMap; length
                                ; zip; sum; upTo; lookup; allFin; unzip; tabulate; filter; foldr )

open import Data.Nat.Properties using (suc-injective)

open import Data.List.Properties                                using (length-map; map-tabulate; filter-none)
open import Data.List.Membership.Propositional                  using (_∈_; mapWith∈; find)
open import Data.List.Membership.Propositional.Properties       using (∈-map⁺; ∈-map⁻; ∈-filter⁺)
open import Data.List.Relation.Unary.Any as Any                 using (Any; here; there)
open import Data.List.Relation.Unary.All as All                 using (All; []; _∷_)
open import Data.List.Relation.Unary.Unique.Propositional       using (Unique)
open import Data.List.Relation.Binary.Subset.Propositional      using (_⊆_)
open import Data.List.Relation.Binary.Prefix.Heterogeneous      using (Prefix; []; _∷_)
open import Data.List.Relation.Binary.Pointwise as PW           using (Pointwise; []; _∷_)
open import Data.List.Relation.Binary.Suffix.Heterogeneous      using (Suffix; here; there)
open import Data.List.Relation.Binary.Permutation.Propositional using ( _↭_; prep; ↭-sym; ↭-reflexive
                                                                      ; module PermutationReasoning )

open import Relation.Nullary                      using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable            using (True)
open import Relation.Binary                       using (Decidable)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; sym; trans; module ≡-Reasoning)
open import Algebra using (Op₂; Identity; Commutative)

------------------------------------------------------------------------
-- Indexed operations.

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

    x y : A
    xs ys : List A

    m n : ℕ

Index : List A → Set
Index = Fin ∘ length

infix 3 _‼_
_‼_ : (vs : List A) → Index vs → A
_‼_ = lookup

infix 3 _⁉_
_⁉_ : List A → ℕ → Maybe A
[]       ⁉ _     = nothing
(x ∷ xs) ⁉ zero  = just x
(x ∷ xs) ⁉ suc n = xs ⁉ n

remove : ∀ {A : Set} → (vs : List A) → Index vs → List A
remove []       ()
remove (_ ∷ xs) fzero    = xs
remove (x ∷ vs) (fsuc f) = x ∷ remove vs f

_at_⟨_⟩ : ∀ {A : Set} → (vs : List A) → Index vs → A → List A
[]       at ()       ⟨ _ ⟩
(_ ∷ xs) at fzero    ⟨ x ⟩ = x ∷ xs
(y ∷ vs) at (fsuc f) ⟨ x ⟩ = y ∷ (vs at f ⟨ x ⟩)

_at_⟨_⟩remove_ : ∀ {A : Set} → (vs : List A) → Index vs → A → Index vs → List A
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
  rewrite map-map₁-zip {xs = tabulate {n = length xs} id} {ys = xs} fsuc
        | map-tabulate {n = length xs} (λ x → x) fsuc
        = there ix∈′

x∈→ix∈ : ∀ {A : Set} {xs : List A} {x : A}
  → (x∈ : x ∈ xs) → ((Any.index x∈ , x) ∈ enumerate xs)
x∈→ix∈ (here refl) = here refl
x∈→ix∈ {xs = _ ∷ xs} (there x∈) = enum∈-∷ (x∈→ix∈ x∈)

mapEnumWith∈ : (xs : List A) → (∀ (i : Index xs) (x : A) → x ∈ xs → B) → List B
mapEnumWith∈ xs f = mapWith∈ (enumerate xs) λ{ {(i , x)} ix∈ → f i x (ix∈→x∈ ix∈) }

‼-suc : ∀ {ℓ} {A : Set ℓ} {x : A} {xs : List A} {i : Index xs}
  → (x ∷ xs ‼ fsuc i)
  ≡ (xs ‼ i)
‼-suc = refl

‼-map : ∀ {A B : Set} {xs : List A} {f : A → B}
  → Index xs
  → Index (map f xs)
‼-map {xs = x ∷ xs} fzero    = fzero
‼-map {xs = x ∷ xs} (fsuc i) = fsuc (‼-map {xs = xs} i)

map-‼ : ∀ {xs : List A} {x : A} {f : A → B} (x∈ : x ∈ xs)
  → (map f xs ‼ ‼-map {xs = xs} {f = f} (Any.index x∈)) ≡ f x
map-‼ (here refl) = refl
map-‼ {xs = _ ∷ xs} {f = f} (there x∈) rewrite map-‼ {xs = xs} {f = f} x∈ = refl

‼→⁉ : ∀ {ℓ} {A : Set ℓ} {xs : List A} {ix : Index xs}
    → just (xs ‼ ix) ≡ (xs ⁉ toℕ ix)
‼→⁉ {_} {_} {[]}     {()}
‼→⁉ {_} {_} {x ∷ xs} {fzero}   = refl
‼→⁉ {_} {A} {x ∷ xs} {fsuc ix} = ‼→⁉ {_} {A} {xs} {ix}

⁉→‼ : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} {ix : Index xs}
    → (len≡ : length xs ≡ length ys)
    → (xs ⁉ toℕ ix) ≡ (ys ⁉ toℕ ix)
    → (xs ‼ ix) ≡ (ys ‼ cast len≡ ix)
⁉→‼ {_} {A} {[]}     {[]}      {ix}      len≡ eq   = refl
⁉→‼ {_} {A} {[]}     {x ∷ ys}  {ix}      () eq
⁉→‼ {_} {A} {x ∷ xs} {[]}      {ix}      () eq
⁉→‼ {_} {A} {x ∷ xs} {.x ∷ ys} {fzero}   len≡ refl = refl
⁉→‼ {_} {A} {x ∷ xs} {y ∷ ys}  {fsuc ix} len≡ eq
  rewrite ‼-suc {_} {A} {x} {xs} {ix}
        = ⁉→‼ {_} {A} {xs} {ys} {ix} (suc-injective len≡) eq

‼-index : (x∈xs : x ∈ xs)
        → (xs ‼ Any.index x∈xs) ≡ x
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

------------------------------------------------------------------------
-- General utilities.

unzip₃ : List (A × B × C) → List A × List B × List C
unzip₃ = map₂ unzip ∘ unzip

filter₁ : List (A ⊎ B) → List A
filter₁ = mapMaybe isInj₁

filter₂ : List (A ⊎ B) → List B
filter₂ = mapMaybe isInj₂

map-proj₁-map₁ : ∀ {xs : List (A × B)} {f : A → C}
  → map proj₁ (map (map₁ f) xs)
  ≡ map (f ∘ proj₁) xs
map-proj₁-map₁ {xs = []} = refl
map-proj₁-map₁ {xs = x ∷ xs} {f = f}
  rewrite map-proj₁-map₁ {xs = xs} {f = f}
        = refl

-- mapWith∈/filter
filter-exists : ∀ {_∈?_ : ∀ (x : A) (xs : List A) → Dec (x ∈ xs)} {f : B → A}
                  {x : A} {xs : List A} {ys : List B}
  → (x∈ : x ∈ map f ys)
  → Unique ys
  → filter ((_∈? (x ∷ xs)) ∘ f) ys
  ↭ (proj₁ ∘ ∈-map⁻ f) x∈ ∷ filter ((_∈? xs) ∘ f) ys
filter-exists {A = A} {B = B} {_∈?_ = _∈?_} {f = f} {x = x} {xs = xs} {ys = ys} x∈ uniq
  with ∈-map⁻ f x∈
... | y , y∈ , refl -- y∈  : y ∈ ys
  with ∈-filter⁺ (_∈? (x ∷ xs) ∘ f) y∈ (here refl)
... | y∈′           -- y∈′ : y ∈ filter _ ys
    = begin
        filter ((_∈? (x ∷ xs)) ∘ f) ys
      ↭⟨ {!!} ⟩
        y ∷ filter ((_∈? xs) ∘ f) ys
      ∎ where open PermutationReasoning

mapWith∈↭filter : ∀ {_∈?_ : ∀ (x : A) (xs : List A) → Dec (x ∈ xs)} {f : B → A}
                    {xs : List A} {ys : List B}
  → (p⊆ : xs ⊆ map f ys)
  → Unique ys
  → mapWith∈ xs (proj₁ ∘ ∈-map⁻ f ∘ p⊆)
  ↭ filter ((_∈? xs) ∘ f) ys
mapWith∈↭filter {A = A} {B = B} {_∈?_ = _∈?_} {f = f} {xs = []}     {ys = ys} p⊆ uniq =
  ↭-sym (↭-reflexive $ filter-none ((_∈? []) ∘ f) (All.universal (λ _ ()) ys))
mapWith∈↭filter {A = A} {B = B} {_∈?_ = _∈?_} {f = f} {xs = x ∷ xs} {ys = ys} p⊆ uniq =
  begin
    mapWith∈ (x ∷ xs) get
  ≡⟨⟩
    get {x} _ ∷ mapWith∈ xs (proj₁ ∘ ∈-map⁻ f ∘ p⊆ ∘ there)
  ↭⟨ prep (get {x} _) (mapWith∈↭filter {_∈?_ = _∈?_} (p⊆ ∘ there) uniq) ⟩
    get {x} _ ∷ filter ((_∈? xs) ∘ f) ys
  ↭⟨ ↭-sym (filter-exists {_∈?_ = _∈?_} (p⊆ (here refl)) uniq) ⟩
    filter ((_∈? (x ∷ xs)) ∘ f) ys
  ∎ where open PermutationReasoning
          get : ∀ {x′} → x′ ∈ x ∷ xs → B
          get = proj₁ ∘ ∈-map⁻ f ∘ p⊆

↭⇒≡ : ∀ {x₀ : A} {xs ys : List A} {_⊕_ : Op₂ A}
  → Identity _≡_ x₀ _⊕_
  → Commutative _≡_ _⊕_
  → xs ↭ ys
  → foldr _⊕_ x₀ xs ≡ foldr _⊕_ x₀ ys
↭⇒≡ = {!!}

-- Any/All
All-Any-refl : ∀ {xs : List A} {f : A → B}
  → All (λ x → Any (λ x′ → f x ≡ f x′) xs) xs
All-Any-refl {xs = []}     = []
All-Any-refl {xs = _ ∷ xs} = here refl ∷ All.map there (All-Any-refl {xs = xs})

-- Prefix relation, instantiated for propositional equality.
Prefix≡ : List A → List A → Set _
Prefix≡ = Prefix _≡_

-- Suffix relation, instantiated for propositional equality.
Suffix≡ : List A → List A → Set _
Suffix≡ = Suffix _≡_

∈⇒Suffix : ∀ {A : Set} {x : A} {ys : List A}
  → x ∈ ys
  → ∃[ xs ] Suffix≡ (x ∷ xs) ys
∈⇒Suffix {ys = x ∷ xs}  (here refl) = xs , here (refl ∷ PW.refl refl)
∈⇒Suffix {ys = _ ∷ ys′} (there x∈) = map₂ there (∈⇒Suffix x∈)

-- Finite sets.
Finite : Set → Set
Finite A = ∃[ n ] (A ↔ Fin n)

finList : Finite A → List A
finList (n , record {f⁻¹ = Fin→A }) = map Fin→A (allFin n)

_≟_∶-_ : (x : A) → (y : A) → Finite A → Dec (x ≡ y)
x ≟ y ∶- (_ , record { f       = toFin
                     ; f⁻¹     = fromFin
                     ; cong₂   = cong′
                     ; inverse = _ , invˡ })
  with toFin x ≟ᶠ toFin y
... | yes x≡y = yes (begin x                 ≡⟨ sym (invˡ x) ⟩
                           fromFin (toFin x) ≡⟨ cong′ x≡y ⟩
                           fromFin (toFin y) ≡⟨ invˡ y ⟩
                           y ∎)
                where open ≡-Reasoning
... | no  x≢y = no λ{ refl → x≢y refl }

≡-findec : Finite A → Decidable {A = A} _≡_
≡-findec A↔fin = _≟_∶- A↔fin
