------------------------------------------------------------------------
-- List utilities.
------------------------------------------------------------------------

module Prelude.Lists where

import Data.List.Relation.Binary.Pointwise as PW

open import Prelude.Init hiding (_∷ʳ_)
open Nat
open L.Mem
open Alg≡
open import Prelude.General
open import Prelude.InferenceRules
open import Prelude.Bifunctor

private variable
  a b c : Level
  A : Set a
  B : Set b
  C : Set c

  x y : A
  xs ys : List A
  xss : List (List A)

  P : Pred₀ A

open import Prelude.Lists.Membership public
open import Prelude.Lists.Indexed public
open import Prelude.Lists.Combinatorics public
open import Prelude.Lists.Empty public
open import Prelude.Lists.NonEmpty public
open import Prelude.Lists.Count public
open import Prelude.Lists.Sums public
open import Prelude.Lists.Singletons public
open import Prelude.Lists.Permutations public
open import Prelude.Lists.Mappings public

-- ** unzip
proj₁∘unzip≡map∘proj₁ : (xys : List (A × B)) → proj₁ (unzip xys) ≡ map proj₁ xys
proj₁∘unzip≡map∘proj₁ [] = refl
proj₁∘unzip≡map∘proj₁ (_ ∷ xys) rewrite proj₁∘unzip≡map∘proj₁ xys = refl

proj₂∘unzip≡map∘proj₂ : (xys : List (A × B)) → proj₂ (unzip xys) ≡ map proj₂ xys
proj₂∘unzip≡map∘proj₂ [] = refl
proj₂∘unzip≡map∘proj₂ (_ ∷ xys) rewrite proj₂∘unzip≡map∘proj₂ xys = refl

∈-unzip⁻ˡ : (xys : List (A × B)) → x ∈ proj₁ (unzip xys) → ∃ λ xy → xy ∈ xys × x ≡ proj₁ xy
∈-unzip⁻ˡ xys rewrite proj₁∘unzip≡map∘proj₁ xys = ∈-map⁻ proj₁

∈-unzip⁻ʳ : (xys : List (A × B)) → y ∈ proj₂ (unzip xys) → ∃ λ xy → xy ∈ xys × y ≡ proj₂ xy
∈-unzip⁻ʳ xys rewrite proj₂∘unzip≡map∘proj₂ xys = ∈-map⁻ proj₂

unzip₃ : List (A × B × C) → List A × List B × List C
unzip₃ = map₂ unzip ∘ unzip

length-unzip₃ : ∀ (xyzs : List (A × B × C)) → let xs , ys , zs = unzip₃ xyzs in
    (length xs ≡ length xyzs)
  × (length ys ≡ length xyzs)
  × (length zs ≡ length xyzs)
length-unzip₃ [] = refl , refl , refl
length-unzip₃ (_ ∷ xyzs) =
  let xs≡ , ys≡ , zs≡ = length-unzip₃ xyzs
  in cong suc xs≡ , cong suc ys≡ , cong suc zs≡

length-unzip₃₁ : ∀ (xyzs : List (A × B × C)) → length (proj₁ $ unzip₃ xyzs) ≡ length xyzs
length-unzip₃₁ = proj₁ ∘ length-unzip₃

length-unzip₃₂ : ∀ (xyzs : List (A × B × C)) → length (proj₁ $ proj₂ $ unzip₃ xyzs) ≡ length xyzs
length-unzip₃₂ = proj₁ ∘ proj₂ ∘ length-unzip₃

length-unzip₃₃ : ∀ (xyzs : List (A × B × C)) → length (proj₂ $ proj₂ $ unzip₃ xyzs) ≡ length xyzs
length-unzip₃₃ = proj₂ ∘ proj₂ ∘ length-unzip₃

-- ** filter
filter₁ : List (A ⊎ B) → List A
filter₁ = mapMaybe isInj₁

filter₂ : List (A ⊎ B) → List B
filter₂ = mapMaybe isInj₂

map-proj₁-map₁ : ∀ {A B C : Set} {xs : List (A × B)} {f : A → C}
  → map proj₁ (map (map₁ f) xs)
  ≡ map (f ∘ proj₁) xs
map-proj₁-map₁ {xs = []} = refl
map-proj₁-map₁ {xs = x ∷ xs} {f = f} rewrite map-proj₁-map₁ {xs = xs} {f = f} = refl

findElem : ∀ {P : Pred₀ A} → Decidable¹ P → List A → Maybe (A × List A)
findElem P? xs with L.Any.any? P? xs
... | yes px = let i = L.Any.index px in just ((xs ‼ i) , remove xs i)
... | no  _  = nothing

-- ** concat/concatMap
concat-∷ : concat (x ∷ xs) ≡ x ++ concat xs
concat-∷ {xs = []}    = refl
concat-∷ {xs = _ ∷ _} = refl

⊆-concat⁺ :
    xs ∈ xss
    ────────
    xs ⊆ concat xss
⊆-concat⁺ (here refl) = ∈-++⁺ˡ
⊆-concat⁺ (there xs∈) = ∈-++⁺ʳ _ ∘ ⊆-concat⁺ xs∈

length-concat :
    xs ∈ xss
    ──────────
    length xs ≤ length (concat xss)
length-concat {xs = .xs} {xss = xs ∷ xss} (here refl)
  rewrite L.length-++ xs {concat xss}
  = Nat.m≤m+n (length xs) (length $ concat xss)
length-concat {xs = xs} {xss = ys ∷ xss} (there xs∈)
  rewrite L.length-++ ys {concat xss}
  = Nat.≤-stepsˡ (length ys) $ length-concat {xs = xs}{xss = xss} xs∈

∈-concatMap⁻ : ∀ {y : B} (f : A → List B)
  → y ∈ concatMap f xs
  → Any (λ x → y ∈ f x) xs
∈-concatMap⁻ f = L.Any.map⁻ ∘ ∈-concat⁻ (map f _)

∈-concatMap⁺ : ∀ {y : B} {f : A → List B}
  → Any (λ x → y ∈ f x) xs
  → y ∈ concatMap f xs
∈-concatMap⁺ = ∈-concat⁺ ∘ L.Any.map⁺

concatMap-∷ : ∀ {A B : Set} {x : A} {xs : List A} {f : A → List B}
  → concatMap f (x ∷ xs) ≡ f x ++ concatMap f xs
concatMap-∷ {x = x}{xs}{f} rewrite concat-∷ {x = f x}{map f xs} = refl

concatMap-++ : ∀ {A B : Set} (f : A → List B) (xs ys : List A)
  → concatMap f (xs ++ ys) ≡ concatMap f xs ++ concatMap f ys
concatMap-++ f xs ys =
  begin concatMap f (xs ++ ys)                 ≡⟨⟩
        concat (map f (xs ++ ys))              ≡⟨ cong concat (L.map-++-commute f xs ys) ⟩
        concat (map f xs ++ map f ys)          ≡⟨ sym (L.concat-++ (map f xs) (map f ys)) ⟩
        concat (map f xs) ++ concat (map f ys) ≡⟨⟩
        concatMap f xs ++ concatMap f ys       ∎
  where open ≡-Reasoning

-- ** mapWith∈

-- Any-mapWith∈⁻ : ∀ {A B : Set} {xs : List A} {f : ∀ {x} → x ∈ xs → B} {P : B → Set} → Any P (mapWith∈ xs f) → Any (P ∘ f) xs
-- Any-mapWith∈⁻ {xs = x ∷ xs} (here p)  = here p
-- Any-mapWith∈⁻ {xs = x ∷ xs} (there p) = there $ Any-mapWith∈⁻ p

∈-mapWith∈⁻ : ∀ {xs : List A} {f : ∀ {x} → x ∈ xs → B} {y : B}
  → y ∈ mapWith∈ xs f
  → ∃ λ x → Σ (x ∈ xs) λ x∈ → y ≡ f {x} x∈
∈-mapWith∈⁻ {xs = x ∷ _}  (here refl) = x , here refl , refl
∈-mapWith∈⁻ {xs = x ∷ xs} (there p)   = let x , x∈ , y≡ = ∈-mapWith∈⁻ p in x , there x∈ , y≡

mapWith∈-∀ : ∀ {xs : List A}  {f : ∀ {x : A} → x ∈ xs → B} {P : B → Set}
  → (∀ {x} x∈ → P (f {x} x∈))
  → (∀ {y} → y ∈ mapWith∈ xs f → P y)
mapWith∈-∀ {xs = x ∷ xs} ∀P {y} (here px)  rewrite px = ∀P (L.Any.here refl)
mapWith∈-∀ {xs = x ∷ xs} ∀P {y} (there y∈) = mapWith∈-∀ (∀P ∘ L.Any.there) y∈

postulate
  mapWith∈-id : ∀ {xs : List A} → mapWith∈ xs (λ {x} _ → x) ≡ xs
  map∘mapWith∈ : ∀ {xs : List A} {f : B → C} {g : ∀ {x} → x ∈ xs → B} → map f (mapWith∈ xs g) ≡ mapWith∈ xs (f ∘ g)

postulate
  filter-exists : ∀ {_∈?_ : ∀ (x : A) (xs : List A) → Dec (x ∈ xs)} {f : B → A} {x : A} {xs : List A} {ys : List B}
    → (x∈ : x ∈ map f ys)
    → Unique ys
    → filter ((_∈? (x ∷ xs)) ∘ f) ys
    ↭ (proj₁ ∘ ∈-map⁻ f) x∈ ∷ filter ((_∈? xs) ∘ f) ys
-- filter-exists {A = A} {B = B} {_∈?_ = _∈?_} {f = f} {x = x} {xs = xs} {ys = ys} x∈ uniq
--   with ∈-map⁻ f x∈
-- ... | y , y∈ , refl -- y∈  : y ∈ ys
--   with ∈-filter⁺ (_∈? (x ∷ xs) ∘ f) y∈ (here refl)
-- ... | y∈′           -- y∈′ : y ∈ filter _ ys
--     = begin
--         filter ((_∈? (x ∷ xs)) ∘ f) ys
--       ↭⟨ {!!} ⟩
--         y ∷ filter ((_∈? xs) ∘ f) ys
--       ∎ where open PermutationReasoning

mapWith∈↭filter : ∀ {_∈?_ : ∀ (x : A) (xs : List A) → Dec (x ∈ xs)} {f : B → A}
                    {xs : List A} {ys : List B}
  → (p⊆ : xs ⊆ map f ys)
  → Unique ys
  → mapWith∈ xs (proj₁ ∘ ∈-map⁻ f ∘ p⊆)
  ↭ filter ((_∈? xs) ∘ f) ys
mapWith∈↭filter {A = A} {B = B} {_∈?_ = _∈?_} {f = f} {xs = []}     {ys = ys} p⊆ uniq =
  ↭-sym (↭-reflexive $ L.filter-none ((_∈? []) ∘ f) (L.All.universal (λ _ ()) ys))
mapWith∈↭filter {A = A} {B = B} {_∈?_ = _∈?_} {f = f} {xs = x ∷ xs} {ys = ys} p⊆ uniq =
  begin
    mapWith∈ (x ∷ xs) get
  ≡⟨⟩
    get {x} _ ∷ mapWith∈ xs (proj₁ ∘ ∈-map⁻ f ∘ p⊆ ∘ there)
  ↭⟨ ↭-prep (get {x} _) (mapWith∈↭filter {_∈?_ = _∈?_} (p⊆ ∘ there) uniq) ⟩
    get {x} _ ∷ filter ((_∈? xs) ∘ f) ys
  ↭⟨ ↭-sym (filter-exists {_∈?_ = _∈?_} (p⊆ (here refl)) uniq) ⟩
    filter ((_∈? (x ∷ xs)) ∘ f) ys
  ∎ where open PermutationReasoning
          get : ∀ {x′} → x′ ∈ x ∷ xs → B
          get = proj₁ ∘ ∈-map⁻ f ∘ p⊆

postulate
  ↭⇒≡ : ∀ {x₀ : A} {xs ys : List A} {_⊕_ : Op₂ A}
    → Identity x₀ _⊕_
    → Commutative _⊕_
    → xs ↭ ys
    → foldr _⊕_ x₀ xs ≡ foldr _⊕_ x₀ ys
-- ↭⇒≡ = {!!}

-- All
All∉[] : All (_∉ []) ys
All∉[] {ys = []}     = []
All∉[] {ys = y ∷ ys} = (λ ()) ∷ All∉[] {ys = ys}

-- ** Unique
unique-∈ : Unique (x ∷ xs) → x ∉ xs
unique-∈ {xs = []} u ()
unique-∈ {xs = x ∷ xs} ((x≢x ∷ _) ∷ _) (here refl) = x≢x refl
unique-∈ {xs = x ∷ xs} ((_ ∷ p) ∷ _)   (there x∈)  = L.All.All¬⇒¬Any p x∈

Unique-mapWith∈ : ∀ {A B : Set} {xs : List A} {f : ∀ {x} → x ∈ xs → B}
  → (∀ {x x′} {x∈ : x ∈ xs} {x∈′ : x′ ∈ xs} → f x∈ ≡ f x∈′ → L.Any.index x∈ ≡ L.Any.index x∈′)
  → Unique (mapWith∈ xs f)
Unique-mapWith∈ {xs = []}     {f = f} f≡ = []
Unique-mapWith∈ {xs = x ∷ xs} {f = f} f≡
  = L.All.tabulate (mapWith∈-∀ {P = f (L.Any.here refl) ≢_} λ _ eq → case f≡ eq of λ () )
  ∷ Unique-mapWith∈ {xs = xs} (F.suc-injective ∘ f≡)

∈-irr : Unique xs → Irrelevant (x ∈ xs)
∈-irr (x∉ ∷ _)  (here refl) (here refl) = refl
∈-irr (x∉ ∷ _)  (here refl) (there x∈)  = ⊥-elim $ L.All.lookup x∉ x∈ refl
∈-irr (x∉ ∷ _)  (there x∈)  (here refl) = ⊥-elim $ L.All.lookup x∉ x∈ refl
∈-irr (_  ∷ un) (there p)   (there q)   = cong there $ ∈-irr un p q

-- ** drop
∈-drop⁻ : ∀ {n} {A : Set} {x : A} {xs : List A}
  → x ∈ drop n xs
  → x ∈ xs
∈-drop⁻ {n = 0} x∈ = x∈
∈-drop⁻ {n = suc n} {xs = _ ∷ xs} x∈ = there $ ∈-drop⁻ {n = n} x∈

-- ** mapMaybe
mapMaybe-++ : ∀ (f : A → Maybe B) xs ys → mapMaybe f (xs ++ ys) ≡ mapMaybe f xs ++ mapMaybe f ys
mapMaybe-++ f []       ys = refl
mapMaybe-++ f (x ∷ xs) ys with f x
... | just _  = cong (_ ∷_) (mapMaybe-++ f xs ys)
... | nothing = mapMaybe-++ f xs ys

module _ (f : A → Maybe B) where
  ∈-mapMaybe⁻ : y ∈ mapMaybe f xs
              → ∃ λ x → (x ∈ xs) × (f x ≡ just y)
  ∈-mapMaybe⁻ {y = y} {xs = x ∷ xs} y∈
    with f x in fx≡
  ... | nothing = map₂′ (map₁′ there) (∈-mapMaybe⁻ y∈)
  ... | just y′
    with y∈
  ... | here refl = x , here refl , fx≡
  ... | there y∈′ = map₂′ (map₁′ there) (∈-mapMaybe⁻ y∈′)

  ∈-mapMaybe⁺ : x ∈ xs → f x ≡ just y → y ∈ mapMaybe f xs
  ∈-mapMaybe⁺ {xs = x ∷ xs} x∈ eq with x∈
  ... | here refl with just y ← f x -- in fx≡ [BUG]
    = here $ M.just-injective (sym eq)
  ... | there x∈ with IH ← ∈-mapMaybe⁺ x∈ eq
    with f x
  ... | nothing = IH
  ... | just _  = there IH

  mapMaybe-here : (eq : f x ≡ just y)
    → mapMaybe f (x ∷ xs) ≡ y ∷ mapMaybe f xs
  mapMaybe-here {x = x} eq with just _ ← f x = cong (_∷ _) (M.just-injective eq)

  ∈-mapMaybe⁺-here : (eq : f x ≡ just y)
    → Is-here $ ∈-mapMaybe⁺ (here {xs = xs} refl) eq
  ∈-mapMaybe⁺-here {x = x} {y = y} {xs = xs} eq with just _ ← f x = _

  mapMaybe-⊆ : xs ⊆ ys → mapMaybe f xs ⊆ mapMaybe f ys
  mapMaybe-⊆ {xs = x ∷ xs} {ys = ys} xs⊆ fx∈ =
    let x , x∈ , fx≡ = ∈-mapMaybe⁻ fx∈
    in  ∈-mapMaybe⁺ (xs⊆ x∈) fx≡

  mapMaybe-↭ : xs ↭ ys → mapMaybe f xs ↭ mapMaybe f ys
  mapMaybe-↭ {xs = xs} {ys = .xs} ↭-refl = ↭-refl
  mapMaybe-↭ {xs = .(x ∷ _)} {ys = .(x ∷ _)} (↭-prep x xs↭ys)
    with IH ← mapMaybe-↭ xs↭ys
    with f x
  ... | nothing = IH
  ... | just y  = ↭-prep y IH
  mapMaybe-↭ {xs = .(x ∷ y ∷ _)} {ys = .(y ∷ x ∷ _)} (↭-swap x y xs↭ys)
    with IH ← mapMaybe-↭ xs↭ys
    with f x | inspect f x | f y | inspect f y
  ... | nothing | ≡[ fx ] | nothing | ≡[ fy ] rewrite fx | fy = IH
  ... | nothing | ≡[ fx ] | just y′ | ≡[ fy ] rewrite fx | fy = ↭-prep y′ IH
  ... | just x′ | ≡[ fx ] | nothing | ≡[ fy ] rewrite fx | fy = ↭-prep x′ IH
  ... | just x′ | ≡[ fx ] | just y′ | ≡[ fy ] rewrite fx | fy = ↭-swap x′ y′ IH
  mapMaybe-↭ {xs = xs} {ys = ys} (↭-trans xs↭ ↭ys) = ↭-trans (mapMaybe-↭ xs↭) (mapMaybe-↭ ↭ys)

  ∈-mapMaybe-++⁻ : ∀ xs {ys} {x : B}
    → x ∈ mapMaybe f (xs ++ ys)
    → x ∈ mapMaybe f xs
    ⊎ x ∈ mapMaybe f ys
  ∈-mapMaybe-++⁻ xs {ys} rewrite mapMaybe-++ f xs ys = ∈-++⁻ _

  ∈-mapMaybe-++⁺ˡ : ∀ {xs ys} {x : B}
    → x ∈ mapMaybe f xs
    → x ∈ mapMaybe f (xs ++ ys)
  ∈-mapMaybe-++⁺ˡ {xs}{ys} rewrite mapMaybe-++ f xs ys = ∈-++⁺ˡ

  ∈-mapMaybe-++⁺ʳ : ∀ xs {ys} {y : B}
    → y ∈ mapMaybe f ys
    → y ∈ mapMaybe f (xs ++ ys)
  ∈-mapMaybe-++⁺ʳ xs {ys} rewrite mapMaybe-++ f xs ys = ∈-++⁺ʳ _

postulate
  mapMaybe≡[]⇒All-nothing : ∀ {xs : List A} {f : A → Maybe B}
    → Null (mapMaybe f xs)
    → All (Is-nothing ∘ f) xs

  All-nothing⇒mapMaybe≡[] : ∀ {xs : List A} {f : A → Maybe B}
    → All Is-nothing (map f xs)
    → Null (mapMaybe f xs)

-- ** Any/All
Any-tail : ∀ {-A : Set-} {P : Pred₀ A} {xs : List A} → Any P xs → List A
Any-tail {xs = xs} x∈ = drop (suc $ F.toℕ $ L.Any.index x∈) xs
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

postulate
  lookup≡find∘map⁻ : ∀ {xs : List A} {f : A → B} {P : Pred₀ B}
    → (p : Any P (map f xs))
    → L.Any.lookup p ≡ f (proj₁ $ find $ L.Any.map⁻ p)

  Any-lookup∘map : ∀ {P Q : Pred₀ A}
    → (P⊆Q : ∀ {x} → P x → Q x)
    → (p : Any P xs)
    → L.Any.lookup (L.Any.map P⊆Q p) ≡ L.Any.lookup p

  lookup∘∈-map⁺ : ∀ {f : A → B}
    → (x∈ : x ∈ xs)
    → L.Any.lookup (∈-map⁺ f x∈) ≡ f x

All-Any-refl : ∀ {xs : List A} {f : A → B}
  → All (λ x → Any (λ x′ → f x ≡ f x′) xs) xs
All-Any-refl {xs = []}     = []
All-Any-refl {xs = _ ∷ xs} = here refl ∷ L.All.map there (All-Any-refl {xs = xs})

all-filter⁺ : ∀ {P Q : A → Set a} {P? : Decidable¹ P} {xs : List A}
  → All (λ x → P x → Q x) xs
  → All Q (filter P? xs)
all-filter⁺ {xs = _} [] = []
all-filter⁺ {P? = P?} {xs = x ∷ _} (Qx ∷ Qxs)
  with P? x
... | no  _  = all-filter⁺ Qxs
... | yes Px = Qx Px ∷ all-filter⁺ Qxs

All-map : ∀ {P : Pred₀ A} {Q : Pred₀ A} {xs : List A}
  → (∀ x → P x → Q x)
  → All P xs
  → All Q xs
All-map P⇒Q = L.All.map (λ {x} → P⇒Q x)

-- ** Prefix relation, instantiated for propositional equality.
Prefix≡ : List A → List A → Set _
Prefix≡ = Prefix _≡_

-- ** Suffix relation, instantiated for propositional equality.
Suffix≡ : List A → List A → Set _
Suffix≡ = Suffix _≡_

suffix-refl : (xs : List A) → Suffix≡ xs xs
suffix-refl xs = here (PW.≡⇒Pointwise-≡ refl)

∈⇒Suffix : {x : A} {ys : List A}
  → x ∈ ys
  → ∃[ xs ] Suffix≡ (x ∷ xs) ys
∈⇒Suffix {ys = x ∷ xs}  (here refl) = xs , here (refl ∷ PW.refl refl)
∈⇒Suffix {ys = _ ∷ ys′} (there x∈) = map₂′ there (∈⇒Suffix x∈)

postulate
  Suffix⇒⊆ : {xs ys : List A} → Suffix≡ xs ys → xs ⊆ ys

  proj₁∘∈⇒Suffix≡ : {xs : List⁺ A} {ys zs : List A} (∀x∈ : All⁺ (_∈ ys) xs) (ys≼ : Suffix≡ ys zs)
    → (proj₁ ∘ ∈⇒Suffix ∘ All⁺-last ∘ L.All.map (Suffix⇒⊆ ys≼)) ∀x∈
    ≡ (proj₁ ∘ ∈⇒Suffix ∘ All⁺-last) ∀x∈

-- ** Finite sets.
Finite : Set a → Set a
Finite A = ∃[ n ] (A Fun.↔ Fin n)

finList : Finite A → List A
finList (n , record {f⁻¹ = Fin→A }) = map Fin→A (allFin n)

≡-findec : Finite A → Decidable² {A = A} _≡_
≡-findec (_ , record { f = toFin; f⁻¹ = fromFin; cong₂ = cong′; inverse = _ , invˡ }) x y
  with toFin x F.≟ toFin y
... | yes x≡y = yes (begin x                 ≡⟨ sym (invˡ x) ⟩
                           fromFin (toFin x) ≡⟨ cong′ x≡y ⟩
                           fromFin (toFin y) ≡⟨ invˡ y ⟩
                           y ∎)
                where open ≡-Reasoning
... | no  x≢y = no λ{ refl → x≢y refl }

-- ** Adjacent pairs.
pairs : List A → List (A × A)
pairs = λ where
  (x ∷ y ∷ xs) → (x , y) ∷ pairs (y ∷ xs)
  _            → []

∈-pairs⁻ : ∀ {x y : A} → (x , y) ∈ pairs xs → (x ∈ xs) × (y ∈ xs)
∈-pairs⁻ {xs = _ ∷ _ ∷ _} = λ where
  (here refl) → here refl , there (here refl)
  (there x∈)  → map₁ there $ map₂ there $ ∈-pairs⁻ x∈

-- ** Interleaving.
open import Data.List.Relation.Ternary.Interleaving using (_∷ˡ_; _∷ʳ_)

_∥_≡_ : 3Rel (List A) _
_∥_≡_ = Interleaving _≡_ _≡_

pattern keepˡ p = refl ∷ˡ p
pattern keepʳ p = refl ∷ʳ p
