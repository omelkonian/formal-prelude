{-# OPTIONS --allow-unsolved-metas #-}
------------------------------------------------------------------------
-- List utilities
------------------------------------------------------------------------

module Prelude.Lists where

open import Level            using (Level; 0ℓ)
open import Function         using (_∘_; _∋_; case_of_; id; _$_)
open import Function.Bundles using (_↔_)

open import Data.Empty    using (⊥; ⊥-elim)
open import Data.Unit     using (⊤; tt)
open import Data.Product  using (_×_; _,_; map₁; map₂; proj₁; proj₂; <_,_>; ∃; ∃-syntax; Σ; Σ-syntax)
open import Data.Sum      using (_⊎_; inj₁; inj₂; isInj₁; isInj₂)


open import Data.Maybe using (Maybe; just; nothing; Is-just; Is-nothing)
import Data.Maybe.Properties as Maybe

open import Data.Nat
open import Data.Nat.Properties

open import Data.Fin            using (Fin; toℕ; fromℕ<; inject≤; cast; inject₁)
  renaming (zero to fzero; suc to fsuc; _≟_ to _≟ᶠ_)
open import Data.Fin.Properties using ()
  renaming (suc-injective to fsuc-injective)

open import Data.List
  renaming (sum to ∑ℕ)
open import Data.List.Properties using (length-map; map-tabulate; filter-none; ++-identityˡ; ++-identityʳ)
open import Data.List.NonEmpty   using (List⁺; _∷_; toList; _⁺++_; last; _∷⁺_)
  renaming ([_] to [_]⁺; map to map⁺)

open import Data.List.Membership.Propositional                  using (_∈_; _∉_; mapWith∈; find)
open import Data.List.Membership.Propositional.Properties       using (∈-map⁺; ∈-map⁻; ∈-filter⁺; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any as Any                 using (Any; here; there)
import Data.List.Relation.Unary.Any.Properties as Any
open import Data.List.Relation.Unary.All as All                 using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as All
open import Data.List.Relation.Unary.Unique.Propositional       using (Unique)
open import Data.List.Relation.Unary.AllPairs as AllPairs       using ([]; _∷_)
open import Data.List.Relation.Binary.Subset.Propositional      using (_⊆_)
open import Data.List.Relation.Binary.Prefix.Heterogeneous      using (Prefix; []; _∷_)
open import Data.List.Relation.Binary.Pointwise as PW           using (Pointwise; []; _∷_)
open import Data.List.Relation.Binary.Suffix.Heterogeneous      using (Suffix; here; there)
open import Data.List.Relation.Binary.Permutation.Propositional using ( _↭_; prep; ↭-sym; ↭-reflexive
                                                                      ; module PermutationReasoning )

open import Relation.Nullary           using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (True)
open import Relation.Unary as Unary    using (Pred)
open import Relation.Binary            using (Decidable)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; cong; sym; trans; module ≡-Reasoning)
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

just-⁉⇒∈ : ∀ {i : ℕ}
  → (xs ⁉ i) ≡ just x
  → x ∈ xs
just-⁉⇒∈ {xs = _ ∷ _}  {i = zero}  ⁉≡just = here (Maybe.just-injective (sym ⁉≡just))
just-⁉⇒∈ {xs = _ ∷ xs} {i = suc i} ⁉≡just = there (just-⁉⇒∈ {xs = xs} {i = i} ⁉≡just)

------------------------------------------------------------------------
-- Combinatorics.

-- e.g. subsequences "abc" ≡ ["","c","b","bc","a","ab","ac","abc"]
subsequences : List A → List (List A)
subsequences []       = [ [] ]
subsequences (x ∷ xs) = xss ++ map (x ∷_) xss
  where xss = subsequences xs

subsequences-refl : ∀ {xs : List A} → xs ∈ subsequences xs
subsequences-refl {xs = []}     = here refl
subsequences-refl {xs = x ∷ xs} = ∈-++⁺ʳ (subsequences xs) (∈-map⁺ (x ∷_) (subsequences-refl {xs = xs}))

-- e.g. combinations [[1,2,3],[4,5]] ≡ [[1,4],[1,5],[2,4],[2,5],[3,4],[3,5]]
combinations : List (List A) → List (List A)
combinations []         = []
combinations (xs ∷ xss) = concatMap (λ x → map (x ∷_) xss′) xs
  where xss′ = combinations xss

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

-- mapWith∈
mapWith∈-∀ : ∀ {A B : Set} {xs : List A}  {f : ∀ {x : A} → x ∈ xs → B} {P : B → Set}
  → (∀ {x} x∈ → P (f {x} x∈))
  → (∀ {y} → y ∈ mapWith∈ xs f → P y)
mapWith∈-∀ {xs = x ∷ xs} ∀P {y} (here px)  rewrite px = ∀P (Any.here refl)
mapWith∈-∀ {xs = x ∷ xs} ∀P {y} (there y∈) = mapWith∈-∀ (∀P ∘ Any.there) y∈

postulate
  mapWith∈-id : ∀ {xs : List A} → mapWith∈ xs (λ {x} _ → x) ≡ xs
  map∘mapWith∈ : ∀ {xs : List A} {f : B → C} {g : ∀ {x} → x ∈ xs → B} → map f (mapWith∈ xs g) ≡ mapWith∈ xs (f ∘ g)

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

-- Unique
Unique-mapWith∈ : ∀ {A B : Set} {xs : List A} {f : ∀ {x} → x ∈ xs → B}
  → (∀ {x x′} {x∈ : x ∈ xs} {x∈′ : x′ ∈ xs} → f x∈ ≡ f x∈′ → Any.index x∈ ≡ Any.index x∈′)
  → Unique (mapWith∈ xs f)
Unique-mapWith∈ {xs = []}     {f = f} f≡ = []
Unique-mapWith∈ {xs = x ∷ xs} {f = f} f≡
  = All.tabulate (mapWith∈-∀ {P = f (Any.here refl) ≢_} λ _ eq → case f≡ eq of λ () )
  ∷ Unique-mapWith∈ {xs = xs} (fsuc-injective ∘ f≡)

-- Empty lists
Null : ∀ {A : Set} → List A → Set
Null xs = xs ≡ []

¬Null : ∀ {A : Set} → List A → Set
¬Null xs = xs ≢ []

null? : ∀ {A : Set} → Unary.Decidable (Null {A})
null? []      = yes refl
null? (_ ∷ _) = no  λ ()

¬null? : ∀ {A : Set} → Unary.Decidable (¬Null {A})
¬null? []      = no  λ ¬p → ¬p refl
¬null? (_ ∷ _) = yes λ ()

toList≢[] : ∀ {xs : List⁺ A} → ¬Null (toList xs)
toList≢[] {xs = x ∷ xs} ()

map≢[] : ∀ {xs : List A} {f : A → B}
  → ¬Null xs
  → ¬Null (map f xs)
map≢[] {xs = []}     xs≢[] _      = ⊥-elim $ xs≢[] refl
map≢[] {xs = x ∷ xs} _    ()

mapWith∈≢[] : ∀ {xs : List A} {f : ∀ {x} → x ∈ xs → B}
  → ¬Null xs
  → ¬Null (mapWith∈ xs f)
mapWith∈≢[] {xs = []}     xs≢[] _ = ⊥-elim $ xs≢[] refl
mapWith∈≢[] {xs = x ∷ xs} _    ()

concat≡[]ˡ : ∀ {xs : List A} {xss : List (List A)}
  → Null $ concat (xs ∷ xss)
  → Null xs
concat≡[]ˡ {xs = []} _ = refl

concat≡[]ʳ : ∀ {xs : List A} {xss : List (List A)}
  → Null $ concat (xs ∷ xss)
  → Null $ concat xss
concat≡[]ʳ {xs = []} {xss = xss} concat≡[] rewrite ++-identityˡ xss = concat≡[]

concat≢[] : ∀ {xss : List (List A)}
  → ∃[ xs ] ( (xs ∈ xss)
            × ¬Null xs )
  → ¬Null (concat xss)
concat≢[] {_} {_ ∷ xss} (_  , here refl , xs≢[]) concat≡[] = xs≢[] $ concat≡[]ˡ {xss = xss} concat≡[]
concat≢[] {_} {_ ∷ xss} (xs , there xs∈ , xs≢[]) concat≡[] = concat≢[] (xs , xs∈ , xs≢[])
                                                                       (concat≡[]ʳ {xss = xss} concat≡[])

concat≡[] : ∀ {xss : List (List A)}
  → Null $ concat xss
  → All Null xss
concat≡[] {xss = []}       _  = []
concat≡[] {xss = [] ∷ xss} eq rewrite ++-identityˡ xss = refl ∷ concat≡[] eq

mapWith∈≡[] : ∀ {xs : List A} {f : ∀ {x} → x ∈ xs → B}
  → Null $ mapWith∈ xs f
  → Null xs
mapWith∈≡[] {xs = []} _ = refl

∀mapWith∈≡[] : ∀ {xs : List A} {f : ∀ {x} → x ∈ xs → List B}
  → (∀ {x} x∈ → ¬Null $ f {x} x∈)
  → ¬ (Null xs)
  → ¬ (All Null $ mapWith∈ xs f)
∀mapWith∈≡[] {xs = []}     {f} _  xs≢[]  _    = xs≢[] refl
∀mapWith∈≡[] {xs = x ∷ xs} {f} ∀f _      ∀≡[] = ∀f {x} (here refl) (All.lookup ∀≡[] (here refl))

filter≡[] : ∀ {A : Set} {P : A → Set} {P? : Unary.Decidable P} {xs : List A}
  → filter P? xs ≡ []
  → All (¬_ ∘ P) xs
filter≡[] {P = P} {P?} {[]}     _  = []
filter≡[] {P = P} {P?} {x ∷ xs} eq
  with P? x | eq
... | yes px  | ()
... | no  ¬px | eq′ = ¬px ∷ filter≡[] eq′

¬Null⇒∃x : ∀ {A : Set} {xs : List A}
  → ¬Null xs
  → ∃[ x ] (x ∈ xs)
¬Null⇒∃x {xs = []}     ¬p = ⊥-elim $ ¬p refl
¬Null⇒∃x {xs = x ∷ xs} _  = x , here refl

postulate
  Null-++⁻ : ∀ {xs ys : List A} → Null (xs ++ ys) → Null xs × Null ys

-- mapMaybe
postulate
  ∈-mapMaybe⁻ : ∀ {xs : List A} {f : A → Maybe B} {y : B}
    → y ∈ mapMaybe f xs
    → ∃ λ x → (x ∈ xs) × (f x ≡ just y)

  mapMaybe≡[]⇒All-nothing : ∀ {xs : List A} {f : A → Maybe B}
    → Null (mapMaybe f xs)
    → All (Is-nothing ∘ f) xs

  All-nothing⇒mapMaybe≡[] : ∀ {xs : List A} {f : A → Maybe B}
    → All Is-nothing (map f xs)
    → Null (mapMaybe f xs)

-- count
count : ∀ {P : A → Set} → Unary.Decidable P → List A → ℕ
count P? = length ∘ filter P?

count-single : ∀ {P : A → Set} {P? : Unary.Decidable P} {x xs}
  → count P? (x ∷ xs) ≡ 1
  → P x
  → All (x ≢_) xs
count-single {P = P} {P?} {x} {xs} count≡1 px
  with P? x
... | no ¬px = ⊥-elim $ ¬px px
... | yes _  = All.¬Any⇒All¬ xs h
  where
    h : x ∉ xs
    h x∈ = {!!}

postulate
  ⊆⇒count≤ : ∀ {xs ys : List A} {P : Pred A 0ℓ}
    → (P? : Unary.Decidable P)
    → xs ⊆ ys
    → count P? xs ≤ count P? ys

  count≡0⇒null-filter : ∀ {xs : List A} {P : Pred A 0ℓ}
    → (P? : Unary.Decidable P)
    → count P? xs ≡ 0
    → Null $ filter P? xs

  count≡0⇒All¬ : ∀ {xs : List A} {P : Pred A 0ℓ}
    → (P? : Unary.Decidable P)
    → count P? xs ≡ 0
    → All (¬_ ∘ P) xs

  count-map⁺ : ∀ {xs : List A} {f : A → B} {P : Pred B 0ℓ} {P? : Unary.Decidable P}
    → count (P? ∘ f) xs
    ≡ count P? (map f xs)

-- List⁺
All⁺ : ∀ {A : Set} → Pred A 0ℓ → List⁺ A → Set
All⁺ P = All P ∘ toList

toList⁺ : ∀ (xs : List A) → xs ≢ [] → List⁺ A
toList⁺ []       ¬[] = ⊥-elim $ ¬[] refl
toList⁺ (x ∷ xs) _   = x ∷ xs

toList∘toList⁺ : ∀ (xs : List A) (xs≢[] : ¬Null xs)
  → toList (toList⁺ xs xs≢[]) ≡ xs
toList∘toList⁺ [] ¬n     = ⊥-elim $ ¬n refl
toList∘toList⁺ (_ ∷ _) _ = refl

All⇒All⁺ : ∀ {xs : List A} {p : ¬Null xs} {P : Pred A 0ℓ}
  → All P xs
  → All⁺ P (toList⁺ xs p)
All⇒All⁺ {xs = xs} {p} ∀P rewrite toList∘toList⁺ xs p = ∀P

postulate
  last-∷ : ∀ {x : A} {xs : List⁺ A} → last (x ∷⁺ xs) ≡ last xs

All⁺-last : ∀ {A : Set} {xs : List⁺ A} {P : Pred A 0ℓ}
  → All⁺ P xs
  → P (last xs)
All⁺-last {xs = x ∷ []}     (px ∷ []) = px
All⁺-last {xs = x ∷ y ∷ xs} (_  ∷ ∀p) rewrite last-∷ {x = x}{y ∷ xs} = All⁺-last ∀p

-- Any/All
lookup≡find∘map⁻ : ∀ {xs : List A} {f : A → B} {P : Pred B 0ℓ}
  → (p : Any P (map f xs))
  → Any.lookup p ≡ f (proj₁ $ find $ Any.map⁻ p)
lookup≡find∘map⁻ {xs = xs}{f} p = {!!}

All-Any-refl : ∀ {xs : List A} {f : A → B}
  → All (λ x → Any (λ x′ → f x ≡ f x′) xs) xs
All-Any-refl {xs = []}     = []
All-Any-refl {xs = _ ∷ xs} = here refl ∷ All.map there (All-Any-refl {xs = xs})

all-filter⁺ : ∀ {P Q : A → Set} {P? : Unary.Decidable P} {xs : List A}
  → All (λ x → P x → Q x) xs
  → All Q (filter P? xs)
all-filter⁺ {xs = _} [] = []
all-filter⁺ {P? = P?} {xs = x ∷ _} (Qx ∷ Qxs)
  with P? x
... | no  _  = all-filter⁺ Qxs
... | yes Px = Qx Px ∷ all-filter⁺ Qxs

All-map : ∀ {P : Pred A 0ℓ} {Q : Pred A 0ℓ} {xs : List A}
  → (∀ x → P x → Q x)
  → All P xs
  → All Q xs
All-map P⇒Q = All.map (λ {x} → P⇒Q x)

-- Prefix relation, instantiated for propositional equality.
Prefix≡ : List A → List A → Set _
Prefix≡ = Prefix _≡_

-- Suffix relation, instantiated for propositional equality.
Suffix≡ : List A → List A → Set _
Suffix≡ = Suffix _≡_

suffix-refl : (xs : List A) → Suffix≡ xs xs
suffix-refl xs = here (PW.≡⇒Pointwise-≡ refl)

∈⇒Suffix : ∀ {A : Set} {x : A} {ys : List A}
  → x ∈ ys
  → ∃[ xs ] Suffix≡ (x ∷ xs) ys
∈⇒Suffix {ys = x ∷ xs}  (here refl) = xs , here (refl ∷ PW.refl refl)
∈⇒Suffix {ys = _ ∷ ys′} (there x∈) = map₂ there (∈⇒Suffix x∈)

postulate
  Suffix⇒⊆ : ∀ {A : Set} {xs ys : List A} → Suffix≡ xs ys → xs ⊆ ys

  proj₁∘∈⇒Suffix≡ : ∀ {A : Set} {xs : List⁺ A} {ys zs : List A} (∀x∈ : All⁺ (_∈ ys) xs) (ys≼ : Suffix≡ ys zs)
    → (proj₁ ∘ ∈⇒Suffix ∘ All⁺-last ∘ All.map (Suffix⇒⊆ ys≼)) ∀x∈
    ≡ (proj₁ ∘ ∈⇒Suffix ∘ All⁺-last) ∀x∈

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

-- Sums of nat lists.
private
  variable
    X Y : ℕ → Set

∑⁺ : List⁺ ℕ → ℕ
∑⁺ = ∑ℕ ∘ toList

∑₁ : List (∃ X) → ℕ
∑₁ = ∑ℕ ∘ map proj₁


limit : (lim : ℕ)
      → (∀ {n} → lim ≤ n → X n → Y lim)
      → (∀ {n} → n ≤ lim → X n → Y n)
      → List (∃ X)
      → List (∃ Y)
limit {X = X} {Y = Y} l k₁ k₂ = map f
  where
    f : ∃ X → ∃ Y
    f (n , x) with l ≤? n
    ... | yes l≤ = l , k₁ l≤ x
    ... | no ¬l≤ = n , k₂ n≤ x
      where
        n≤ : n ≤ l
        n≤ = ≰⇒≥ ¬l≤

postulate
  ∑₁-limit : ∀ {lim} {xs : List (∃ X)} {k₁ : ∀ {n} → lim ≤ n → X n → Y lim} {k₂ : ∀ {n} → n ≤ lim → X n → Y n}
    → ∑₁ xs ≥ lim
    → ∑₁ (limit lim k₁ k₂ xs) ≥ lim

  ∑₁-++ : ∀ {xs ys : List (∃ X)}
    → ∑₁ (xs ++ ys)
    ≡ ∑₁ xs + ∑₁ ys

  ∑ℕ-∀≡0 : ∀ {xs}
    → All (_≡ 0) xs
    → ∑ℕ xs ≡ 0

  ∑ℕ-⊆ : ∀ {xs ys} → xs ⊆ ys → ∑ℕ xs ≤ ∑ℕ ys

  ∑₁-map₂ : ∀ {xs : List (∃ X)} {f : ∀ {n} → X n → Y n}
    → ∑₁ (map (map₂ f) xs)
    ≡ ∑₁ xs

  ∑₁-single : ∀ {x : ∃ X} → ∑₁ [ n , x ] ≡ n

  x∈∑ℕ : ∀ {x xs}
    → x ∈ xs
    → x ≤ ∑ℕ xs

------------------------------------------------------------------------
-- Singleton predicate for various kinds of lists.

Singleton : List A → Set
Singleton []       = ⊥
Singleton (_ ∷ []) = ⊤
Singleton (_ ∷ _)  = ⊥

construct-Singleton : ∀ {xs : List A}
  → ∃[ x ] (xs ≡ [ x ])
  → Singleton xs
construct-Singleton (_ , refl) = tt

destruct-Singleton : ∀ {xs : List A}
  → Singleton xs
  → ∃ λ x → xs ≡ [ x ]
destruct-Singleton {xs = []}          ()
destruct-Singleton {xs = _ ∷ []}      tt = _ , refl
destruct-Singleton {xs = _ ∷ (_ ∷ _)} ()

singleton-map : ∀ {xs : List A} {f : A → B}
  → Singleton xs
  → Singleton (map f xs)
singleton-map {xs = []}        ()
singleton-map {xs = _ ∷ []}    tt = tt
singleton-map {xs = _ ∷ _ ∷ _} ()

singleton-subseqs : ∀ {xs : List A}
  → Singleton xs
  → subsequences xs ≡ [] ∷ xs ∷ []
singleton-subseqs {xs = []}        ()
singleton-subseqs {xs = _ ∷ []}    tt = refl
singleton-subseqs {xs = _ ∷ _ ∷ _} ()

singleton-mapWith∈  : ∀ {x : A} {xs : List A} {x′ : B} {f : ∀ {x} → x ∈ xs → B}
  → (∀ x∈ → f {x} x∈ ≡ x′)
  → xs ≡ [ x ]
  → mapWith∈ xs f ≡ [ x′ ]
singleton-mapWith∈ f≡ refl rewrite f≡ (here refl) = refl

singleton∈ : ∀ {xs : List A}
  → (s-xs : Singleton xs)
  → proj₁ (destruct-Singleton s-xs) ∈ xs
singleton∈ s-xs with _ , refl ← destruct-Singleton s-xs = here refl

singleton-concat : ∀ {x : A} {xss : List (List A)}
  → xss ≡ [ [ x ] ]
  → Singleton (concat xss)
singleton-concat refl = tt

All-singleton : ∀ {A : Set} {x xs} {P : A → Set}
 → xs ≡ [ x ]
 → All P xs
 → P x
All-singleton refl (Px ∷ []) = Px

---

AtMostSingleton : Pred (List A) 0ℓ
AtMostSingleton []          = ⊤
AtMostSingleton (_ ∷ [])    = ⊤
AtMostSingleton (_ ∷ _ ∷ _) = ⊥

ams-single : ∀ {x : A} {xs : List A}
  → AtMostSingleton (x ∷ xs)
  → xs ≡ []
ams-single {xs = []}    _ = refl
ams-single {xs = _ ∷ _} ()

ams-∈ : ∀ {x : A} {xs : List A}
  → AtMostSingleton xs
  → x ∈ xs
  → xs ≡ [ x ]
ams-∈ {xs = []}        _  ()
ams-∈ {xs = x ∷ []}    _  (here refl) = refl
ams-∈ {xs = _ ∷ _ ∷ _} () _

ams-filter⁺ : ∀ {xs : List A} {P : A → Set} {P? : Unary.Decidable P}
  → AtMostSingleton xs
  → AtMostSingleton (filter P? xs)
ams-filter⁺ {xs = []}                  tt = tt
ams-filter⁺ {xs = x ∷ []}    {P? = P?} tt with P? x
... | yes _ = tt
... | no  _ = tt
ams-filter⁺ {xs = _ ∷ _ ∷ _}           ()

postulate
  ams-filter-map : ∀ {xs : List A} {f : A → B} {P : Pred B 0ℓ} {P? : Unary.Decidable P}
    → AtMostSingleton $ filter P? (map f xs)
    → AtMostSingleton $ filter (P? ∘ f) xs

  ams-filter-reject : ∀ {x : A} {xs : List A} {P : Pred A 0ℓ}
    → (P? : Unary.Decidable P)
    → ¬ P x
    → AtMostSingleton $ filter P? xs
    → AtMostSingleton $ filter P? (x ∷ xs)

  ams-filter-accept : ∀ {x : A} {xs : List A} {P : Pred A 0ℓ}
    → (P? : Unary.Decidable P)
    → P x
    → Null $ filter P? xs
    → AtMostSingleton $ filter P? (x ∷ xs)

  length≤1⇒ams : ∀ {xs : List A}
    → length xs ≤ 1
    → AtMostSingleton xs

  ams-count : ∀ {P : Pred A 0ℓ} {P? : Unary.Decidable P} {xs : List A} {f : A → Maybe B}
    → (∀ x → P x → Is-just (f x))
    → count P? xs ≤ 1
    → AtMostSingleton (mapMaybe f xs)

am-¬null⇒singleton : ∀ {xs : List A}
  → AtMostSingleton xs
  → ¬Null xs
  → Singleton xs
am-¬null⇒singleton {xs = []         } tt ¬p = ⊥-elim (¬p refl)
am-¬null⇒singleton {xs = (_ ∷ [])   } _  _  = tt
am-¬null⇒singleton {xs = (_ ∷ _ ∷ _)} ()

---

Singleton⁺ : List⁺ A → Set
Singleton⁺ (_ ∷ []) = ⊤
Singleton⁺ (_ ∷ _)  = ⊥

destruct-Singleton⁺ : ∀ {xs : List⁺ A}
  → Singleton⁺ xs
  → ∃ λ x → xs ≡ [ x ]⁺
destruct-Singleton⁺ {xs = _ ∷ []}      tt = _ , refl
destruct-Singleton⁺ {xs = _ ∷ (_ ∷ _)} ()

singleton⁺ : ∀ {xs : List A}
  → AtMostSingleton xs
  → (xs≢[] : ¬Null xs)
  → Singleton⁺ (toList⁺ xs xs≢[])
singleton⁺ {xs = []}        tt xs≢[] = ⊥-elim $ xs≢[] refl
singleton⁺ {xs = _ ∷ []}    tt xs≢[] = tt
singleton⁺ {xs = _ ∷ _ ∷ _} ()

singleton-concatMap  : ∀ {h : List⁺ A} {f : A → List B}
  → Singleton⁺ h
  → (∀ x → Singleton (f x))
  → Singleton $ concatMap f (toList h)
singleton-concatMap {f = f} h⁺ s-f
  with h , refl ← destruct-Singleton⁺ h⁺
  rewrite ++-identityʳ (f h)
    = s-f h

singleton⇒singleton⁺ : ∀ {xs : List A} {xs≢[] : ¬ Null xs}
  → Singleton xs
  → Singleton⁺ (toList⁺ xs xs≢[])
singleton⇒singleton⁺ p rewrite proj₂ $ destruct-Singleton p = tt

postulate
  singleton⁺-map⁺ : ∀ {xs : List⁺ A} {f : A → B} → Singleton⁺ xs → Singleton⁺ (map⁺ f xs)

---

Singleton² : ∀ {A : Set} → Pred (List (List A)) 0ℓ
Singleton² xss = Singleton xss × All Singleton xss

construct-Singleton² : ∀ {xss : List (List A)} {x : A}
  → xss ≡ [ [ x ] ]
  → Singleton² xss
construct-Singleton² refl = tt , tt ∷ []

destruct-Singleton² : ∀ {xss : List (List A)}
  → Singleton² xss
  → ∃ λ x → xss ≡ [ [ x ] ]
destruct-Singleton² (tt , s-xs ∷ [])
  with x , refl ← destruct-Singleton s-xs
     = x , refl

singleton-concat⁺ : ∀ {xss : List (List A)}
  → Singleton² xss
  → Singleton (concat xss)
singleton-concat⁺ {xss = []}                  (()   , _)
singleton-concat⁺ {xss = []          ∷ []}    (_    , () ∷ _)
singleton-concat⁺ {xss = (_ ∷ [])    ∷ []}    (_    , _)      = tt
singleton-concat⁺ {xss = (_ ∷ _ ∷ _) ∷ []}    (_    , () ∷ _)
singleton-concat⁺ {xss = _           ∷ _ ∷ _} (()   , _)
