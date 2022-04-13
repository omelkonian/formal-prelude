module Prelude.Lists.Membership where

open import Prelude.Init
open import Prelude.General
open import Prelude.InferenceRules
open L.Mem
open import Prelude.Lists.Indexed
open import Prelude.Lists.Empty

private variable
  a b c : Level; A : Set a; B : Set b; C : Set c
  x x′ y : A; xs ys : List A
  P : Pred A ℓ

-- ** _∈_

∈-++⁻∘∈-++⁺ˡ : (x∈ : x ∈ xs)
  → ∈-++⁻ xs {ys} (∈-++⁺ˡ {xs = xs}{ys} x∈)
  ≡ inj₁ x∈
∈-++⁻∘∈-++⁺ˡ (here _) = refl
∈-++⁻∘∈-++⁺ˡ {ys = ys} (there x∈) rewrite ∈-++⁻∘∈-++⁺ˡ {ys = ys} x∈ = refl

∈-++⁻∘∈-++⁺ʳ : (y∈ : y ∈ ys)
  → ∈-++⁻ xs {ys} (∈-++⁺ʳ xs {ys} y∈)
  ≡ inj₂ y∈
∈-++⁻∘∈-++⁺ʳ {xs = []} _ = refl
∈-++⁻∘∈-++⁺ʳ {xs = _ ∷ xs} y∈ rewrite ∈-++⁻∘∈-++⁺ʳ {xs = xs} y∈ = refl

-- ** _⊆_

⊆-tail : x ∷ xs ⊆ ys → xs ⊆ ys
⊆-tail = _∘ there

module _ {P : Pred A ℓ} (P? : Decidable¹ P) where
  ⊆-filter : xs ⊆ ys → filter P? xs ⊆ filter P? ys
  ⊆-filter {xs = xs}{ys} xs⊆ y∈ =
    let x∈ , Px = ∈-filter⁻ P? y∈
    in ∈-filter⁺ P? (xs⊆ x∈) Px

-- ** Any

module _ {A : Set ℓ} {P : Pred A ℓ′} {xs : List A} where
  Is-here Is-there : Pred₀ (Any P xs)
  Is-here = λ where
    (here _)  → ⊤
    (there _) → ⊥
  Is-there = λ where
    (here _)  → ⊥
    (there _) → ⊤

-- ** mapWith∈

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
  mapWith∈-id :  mapWith∈ xs (λ {x} _ → x) ≡ xs
  map∘mapWith∈ : ∀ {xs : List A} {f : B → C} {g : ∀ {x} → x ∈ xs → B} → map f (mapWith∈ xs g) ≡ mapWith∈ xs (f ∘ g)

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

-- ** Any/All

All∉[] : All (_∉ []) ys
All∉[] {ys = []}     = []
All∉[] {ys = y ∷ ys} = (λ ()) ∷ All∉[] {ys = ys}

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


-- ** drop

∈-drop⁻ : ∀ {n} {A : Set} {x : A} {xs : List A}
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

indexℕ-++⁻ : ∀ (y∈ : y ∈ ys) (y∈′ : y ∈ xs ++ ys) →
  indexℕ y∈′ ≡ length xs + indexℕ y∈
  ──────────────────────────────────
  ∈-++⁻ xs {ys} y∈′ ≡ inj₂ y∈
indexℕ-++⁻ {xs = []}     y∈ y∈′         i≡ = cong inj₂ $ indexℕ-injective y∈′ y∈ i≡
indexℕ-++⁻ {xs = x ∷ xs} y∈ (there y∈′) i≡ = qed
  where
    IH : ∈-++⁻ xs y∈′ ≡ inj₂ y∈
    IH = indexℕ-++⁻ {xs = xs} y∈ y∈′ (Nat.suc-injective i≡)

    qed : ∈-++⁻ (x ∷ xs) (there y∈′) ≡ inj₂ y∈
    qed rewrite IH = refl

-- ** Last∈

Last∈ : Pred₀ (x ∈ xs)
-- Last = Null ∘ Any-tail
Last∈ {xs = _ ∷ []}      (here _)   = ⊤
Last∈ {xs = _ ∷ (_ ∷ _)} (here _)   = ⊥
Last∈ {xs = _ ∷ (_ ∷ _)} (there x∈) = Last∈ x∈

Last∈-there⁺ : ∀ (x∈ : x ∈ xs) →
  Last∈ x∈
  ─────────────────────────
  Last∈ (there {x = x′} x∈)
Last∈-there⁺ = λ where
  (here _)  → id
  (there _) → id

Last∈-there⁻ : ∀ (x∈ : x ∈ xs) →
  Last∈ (there {x = x′} x∈)
  ─────────────────────────
  Last∈ x∈
Last∈-there⁻ = λ where
  (here _)  → id
  (there _) → id

Last∈-here⁻ :
  Last∈ (here {x = x}{xs} refl)
  ─────────────────────────────
  Null xs
Last∈-here⁻ {xs = []} tt = refl

Last∈-here⁺ :
  Null xs
  ─────────────────────────────
  Last∈ (here {x = x}{xs} refl)
Last∈-here⁺ {xs = []} refl = tt


Last∈-map⁺ : ∀ (f : A → B) (x∈ : x ∈ xs) →
  Last∈ x∈
  ───────────────────
  Last∈ (∈-map⁺ f x∈)
Last∈-map⁺ {xs = _ ∷ []}    f (here refl) p = tt
Last∈-map⁺ {xs = _ ∷ _ ∷ _} f (there x∈)  p = Last∈-map⁺ f x∈ p