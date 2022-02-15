module Prelude.Lists.Mappings2 where

open import Prelude.Init
open L.Mem using (_∈_; mapWith∈; ∈-++⁻)
open L.Perm using (∈-resp-↭; Any-resp-↭)
open import Prelude.Lists.Mappings
open import Prelude.Lists.Permutations

private variable
  a b : Level
  A : Set a
  B : Set b

  x y z : A
  xs xs′ ys zs : List A
  P : Pred₀ A

open import Prelude.Lists
open L.Mem
open Nat using (_≤_; s≤s)
open F using (toℕ)
open import Prelude.Lists.Indexed
open import Prelude.Lists.Empty

Last∈ : Pred₀ (x ∈ xs)
-- Last = Null ∘ Any-tail
Last∈ {xs = _ ∷ []}      (here _)   = ⊤
Last∈ {xs = _ ∷ (_ ∷ _)} (here _)   = ⊥
Last∈ {xs = _ ∷ (_ ∷ _)} (there x∈) = Last∈ x∈

Last∈-map⁺ : (f : A → B) (x∈ : x ∈ xs)
  → Last∈ x∈
    --——————————————————
  → Last∈ (∈-map⁺ f x∈)
Last∈-map⁺ {xs = _ ∷ []}    f (here refl) p = tt
Last∈-map⁺ {xs = _ ∷ _ ∷ _} f (there x∈)  p = Last∈-map⁺ f x∈ p

Suffix⊆ : ∀ {A : Set} {xs ys : List A} → Pred₀ (xs ⊆ ys)
Suffix⊆ {A}{xs}{ys} xs⊆ =
  ∀ {x : A} (x∈ : x ∈ xs) →
      indexℕ (xs⊆ x∈)
    ≡ (length ys ∸ length xs) + indexℕ x∈
  -- ∃ λ ys₀ → (ys ≡ ys₀ ++ xs)
  --         × xs⊆ ≡ {!subst (!} -- (xs⊆

length-++-∸ : ∀ {A : Set} {xs ys : List A} →
  length (xs ++ ys) ∸ length ys ≡ length xs
length-++-∸ {xs = xs}{ys}
  rewrite L.length-++ xs {ys}
        | Nat.m+n∸n≡m (length xs) (length ys)
        = refl

Suffix⊆-++⁺ʳ : ∀ {A : Set} {xs ys : List A} →
  Suffix⊆ (∈-++⁺ʳ xs {ys})
Suffix⊆-++⁺ʳ {xs = []}     {ys} x∈
  rewrite Nat.n∸n≡0 (length ys)
    = refl
Suffix⊆-++⁺ʳ {xs = x ∷ xs} {ys} x∈
  rewrite Suffix⊆-++⁺ʳ {xs = xs} x∈
        | length-++-∸ {xs = xs}{ys}
        | length-++-∸ {xs = x ∷ xs}{ys}
  = refl

Suffix⊆-++⁺ˡ : ∀ {A : Set} {xs ys : List A}
  → Null ys
  → Suffix⊆ (∈-++⁺ˡ {xs = xs} {ys})
Suffix⊆-++⁺ˡ {xs = xs} {.[]} refl x∈ = {!!}

-- H : ∀ {A : Set} {xs ys zs : List A} {k : ℕ}
--   → length (ys ++ xs) ∸ length xs + length xs ∸ length zs + k
--   ≡ length (ys ++ xs) ∸ length zs + k
-- H {xs = xs}{ys}{zs}{k}
--   rewrite L.length-++ ys {xs}
--         | Nat.m+n∸n≡m (length ys) (length xs)
--         = refl

Last∈-concat : ∀ {A : Set} {xs : List A} {xss : List (List A)}
  → (xs∈ : xs ∈ xss)
  → Last∈ xs∈
  → Suffix⊆ (⊆-concat⁺ xs∈)
Last∈-concat {xs = xs} {.(xs ∷ [])} (here {xs = []} refl) last-x∈ =
  Suffix⊆-++⁺ˡ refl
Last∈-concat {xs = xs′} {xss = ys ∷ xss@(zs ∷ _)} (there x∈) last-x∈ y∈
  rewrite Suffix⊆-++⁺ʳ {xs = ys} {ys = concat xss} (⊆-concat⁺ x∈ y∈)
        | Last∈-concat x∈ last-x∈ y∈
        | L.length-++ ys {concat xss}
        | Nat.m+n∸n≡m (length ys) (length $ concat xss)
        = H {length ys}{length $ concat xss}{length xs′}{indexℕ y∈} (length-concat x∈)
  where
    H : ∀ {m r n k} → n ≤ r → m + (r ∸ n + k) ≡ m + r ∸ n + k
    H {m} {r} {n} {k} n≤r =
      begin m + (r ∸ n + k)   ≡⟨⟩
            m + ((r ∸ n) + k) ≡⟨ sym $ Nat.+-assoc m (r ∸ n) k ⟩
            m + (r ∸ n) + k   ≡⟨ cong (_+ k) $ sym $ Nat.+-∸-assoc m {r}{n} n≤r ⟩
            ((m + r) ∸ n) + k ≡⟨⟩
            m + r ∸ n + k     ∎ where open ≡-Reasoning

Last∈-there⁺ : ∀ {A : Set} {x x′ : A} {xs : List A}
  → (x∈ : x ∈ xs)
  → Last∈ x∈
    --—————————————————————
  → Last∈ (there {x = x′} x∈)
Last∈-there⁺ = λ where
  (here _)  → id
  (there _) → id

Suffix⊆-there⁺ : ∀ {A : Set} {y : A} {xs ys : List A}
  → (l≤ : length xs ≤ length ys)
  → (p : xs ⊆ ys)
  → Suffix⊆ p
    --————————————————————————————
  → Suffix⊆ {xs = xs}{y ∷ ys} (there {x = y} ∘ p)
Suffix⊆-there⁺ {y = y}{xs}{ys} l≤ p suffix-p x∈
  rewrite suffix-p x∈
        | Nat.+-suc (length ys ∸ length xs) (indexℕ x∈)
        = H (length ys) (length xs) (indexℕ x∈) l≤
  where
    H : ∀ m n k → n ≤ m → suc (m ∸ n + k) ≡ suc m ∸ n + k
    H m       zero    k _         = refl
    H (suc m) (suc n) k (s≤s n≤m) rewrite H m n k n≤m = refl

Last∈-there⁻ : ∀ {A : Set} {x x′ : A} {xs : List A}
  → (x∈ : x ∈ xs)
  → Last∈ (there {x = x′} x∈)
    --—————————————————————
  → Last∈ x∈
Last∈-there⁻ = λ where
  (here _)  → id
  (there _) → id

Last∈-here⁻ : ∀ {A : Set} {x : A} {xs : List A}
  → Last∈ (here {x = x}{xs} refl)
    --—————————————————————
  → Null xs
Last∈-here⁻ {xs = []} tt = refl

Last∈-here⁺ : ∀ {A : Set} {x : A} {xs : List A}
  → Null xs
  → Last∈ (here {x = x}{xs} refl)
    --—————————————————————
Last∈-here⁺ {xs = []} refl = tt


module _ {A B : Set} (f : A → Maybe B) where

  -- Last∈-mapMaybe⁻ : ∀ {y : B} {xs : List A}
  --   → (y∈ : y ∈ mapMaybe f xs)
  --   → Last∈ y∈
  --     --——————————————————
  --   → let _ , x∈ , _ = ∈-mapMaybe⁻ f {xs = xs} y∈
  --     in Last∈ x∈
  -- Last∈-mapMaybe⁻ {y = y} {x ∷ xs} y∈ last-y∈
  --   with f x | inspect f x
  -- ... | nothing | _   = Last∈-there⁺ (∈-mapMaybe⁻ f {xs = xs} y∈ .proj₂ .proj₁)
  --                                    (Last∈-mapMaybe⁻ {xs = xs} y∈ last-y∈)
  -- ... | just fx | fx≡
  --   with y∈

  -- ... | here refl = Last∈-here⁺ {xs = xs} {! Last∈-here⁻ {x = fx}{mapMaybe f xs} last-y∈ !}
  -- ... | there y∈′
  --   = Last∈-there⁺ (∈-mapMaybe⁻ f {xs = xs} y∈′ .proj₂ .proj₁)
  --                  (Last∈-mapMaybe⁻ {xs = xs} y∈′ (Last∈-there⁻ y∈′ last-y∈))

  Last∈-mapMaybe⁺ : ∀ {x : A} {y : B} {xs : List A}
    → (x∈ : x ∈ xs)
    → (f≡ : f x ≡ just y)
    → Last∈ x∈
      --——————————————————————————
    → Last∈ $ ∈-mapMaybe⁺ f x∈ f≡
  Last∈-mapMaybe⁺ {x = x} {y} {.x ∷ []} (here refl) f≡ tt
    with f x | ∈-mapMaybe⁺ f {x = x} {xs = [ x ]} (here refl) f≡
  ... | nothing | ()
  ... | just _  | here refl = tt
  Last∈-mapMaybe⁺ {x = x} {y} {.(_ ∷ _)} (there {x = z} x∈) f≡ last-x∈
    with f z
  ... | nothing = Last∈-mapMaybe⁺ x∈ f≡ $ Last∈-there⁻ x∈ last-x∈
  ... | just fz = Last∈-there⁺ (∈-mapMaybe⁺ f x∈ f≡) (Last∈-mapMaybe⁺ x∈ f≡ $ Last∈-there⁻ x∈ last-x∈)

  indexℕ-mapMaybe⁺ : ∀ {y : B} {xs ys : List A}
    (xs⊆ : xs ⊆ ys)
    (x∈ : x ∈ xs)
    (fx≡ : f x ≡ just y)
    → indexℕ (xs⊆ x∈)                     ≡ length ys ∸ length xs + indexℕ x∈
    → indexℕ (∈-mapMaybe⁺ f (xs⊆ x∈) fx≡) ≡ length (mapMaybe f ys) ∸ length (mapMaybe f xs) + indexℕ x∈
  indexℕ-mapMaybe⁺ xs⊆ x∈ eq = {!!}

  open import Prelude.Bifunctor
  Suffix⊆-mapMaybe : ∀ {xs ys : List A}
    → (xs⊆ : xs ⊆ ys)
    → Suffix⊆ xs⊆
      --——————————————————
    → Suffix⊆ (mapMaybe-⊆ f xs⊆)
  Suffix⊆-mapMaybe {xs = x ∷ xs}{ys} xs⊆ p {y} y∈
    -- mapMaybe-⊆ f xs⊆ =
    --   let x , x∈ , fx≡ = ∈-mapMaybe⁻ y∈
    --   in  ∈-mapMaybe⁺ (xs⊆ x∈) fx≡
    with f x | inspect f x
  ... | nothing | _
    with k , k∈ , fk≡ ← (∃ λ k → (k ∈ x ∷ xs) × (f k ≡ just y))
                      ∋ map₂′ (map₁′ there) (∈-mapMaybe⁻ f {xs = xs} y∈)
    -- * mapMaybe-⊆ f xs⊆ =
    --     let x , x∈ , fx≡ = map₂′ (map₁′ there) (∈-mapMaybe⁻ y∈)
    --     in  ∈-mapMaybe⁺ (xs⊆ x∈) fx≡
    = {!!}
    where
      -- ∃r : ∃ λ r → (r ∈ xs) × (f r ≡ just y)
      -- ∃r = ∈-mapMaybe⁻ f {xs = xs} y∈

      -- ∃k : ∃ λ k → (k ∈ x ∷ xs) × (f k ≡ just y)
      -- ∃k = map₂′ (map₁′ there) (∈-mapMaybe⁻ f {xs = xs} y∈)

      -- k = ∃k .proj₁; k∈ = ∃k .proj₂ .proj₁; fk≡ = ∃k .proj₂ .proj₂

      k∈′ : k ∈ ys
      k∈′ = xs⊆ k∈

      pk : indexℕ k∈′ ≡ length ys ∸ suc (length xs) + indexℕ k∈
      pk = p k∈

      -- y∈ : y ∈ mayMaybe f xs
      y∈′ : y ∈ mapMaybe f ys
      y∈′ = ∈-mapMaybe⁺ f (xs⊆ k∈) fk≡

      qed : indexℕ y∈′
          ≡ length (mapMaybe f ys) ∸ length (mapMaybe f xs) + indexℕ y∈
      qed = {!!}


      -------

      xs⊆′ : xs ⊆ ys
      xs⊆′ = xs⊆ ∘ there

      -- p : Suffix⊆ xs⊆
      --     ∀ y ∈ x ∷ xs. indexℕ (xs⊆ y∈) ≡ length ys ∸ suc (length xs) + indexℕ y∈
      --     indexℕ (xs⊆ (there y∈)) ≡ length ys ∸ suc (length xs) + indexℕ (there y∈)
      --     indexℕ (xs⊆ (there y∈)) ≡ length ys ∸ suc (length xs) + suc (indexℕ y∈)

      p′ : Suffix⊆ xs⊆′
      --   ∀ y ∈ xs. indexℕ (xs⊆ (there y∈)) ≡ length ys ∸ length xs + indexℕ y∈
      p′ y∈ =
        begin
          indexℕ (xs⊆ (there y∈))
        ≡⟨ p (there y∈) ⟩
          length ys ∸ suc (length xs) + suc (indexℕ y∈)
        ≡⟨ Nat.+-suc (length ys ∸ suc (length xs)) (indexℕ y∈) ⟩
          suc (length ys ∸ suc (length xs) + indexℕ y∈)
        ≡⟨ {!!} ⟩
          length ys ∸ length xs + indexℕ y∈
        ∎ where open ≡-Reasoning

      H : Suffix⊆ (mapMaybe-⊆ f xs⊆′)
      H = Suffix⊆-mapMaybe xs⊆′ p′
  ... | just _ | ≡[ fx≡ ]
    with y∈
  ... | there y∈′ = {!!} -- {!p (there ?)!}
  ... | here refl
    with xs⊆ (here refl)
  ... | here refl = {!!}
  ... | there {x = y′}{xs = ys′} x∈′
    with y∈′ ← ∈-mapMaybe⁺ f x∈′ fx≡
    with f y′
  ... | nothing
    = {!!}
  ... | just fy
    = {!p (here refl)!}
    where
      x∈ : x ∈ x ∷ xs
      x∈ = here refl

      i≡ : indexℕ (xs⊆ x∈) ≡ length ys ∸ suc (length xs) + 0
      i≡ = p (here refl)

      xs⊆′ : xs ⊆ ys
      xs⊆′ = xs⊆ ∘ there

      p′ : Suffix⊆ xs⊆′
      p′ x∈ = {! !}
        where
          j≡ : indexℕ (xs⊆ $ there x∈) ≡ length ys ∸ suc (length xs) + suc (indexℕ x∈)
          j≡ = p (there x∈)

          j≡′ : indexℕ (xs⊆′ x∈) ≡ length ys ∸ length xs + indexℕ x∈
          j≡′ =
            begin
              indexℕ (xs⊆′ x∈)
            ≡⟨⟩
              indexℕ (xs⊆ $ there x∈)
            ≡⟨ j≡ ⟩
              length ys ∸ suc (length xs) + suc (indexℕ x∈)
            ≡⟨ {!!} ⟩
              length ys ∸ length xs + indexℕ x∈ ∎
            where open ≡-Reasoning


      i≡′ : indexℕ (∈-mapMaybe⁺ f (xs⊆ x∈) fx≡) ≡ (length $ mapMaybe f ys) ∸ suc (length $ mapMaybe f xs) + 0
      i≡′ = {!Suffix⊆-mapMaybe {xs = xs}{ys} f xs⊆′ p′!}

indexℕ-injective : ∀ {A : Set} {x : A} {xs : List A}
  (p q : x ∈ xs)
  (i≡ : indexℕ p ≡ indexℕ q)
  --—————————
  → p ≡ q
indexℕ-injective {xs = .(_ ∷ _)} (here refl) (here refl) i≡ = refl
indexℕ-injective {xs = .(_ ∷ _)} (there p) (there q) i≡
  = cong there $ indexℕ-injective p q $ Nat.suc-injective {indexℕ p} {indexℕ q} i≡

map≡inj₂ : ∀ {A B C D : Set} {f : A → C} {g : B → D} {x : B}
  → Sum.map f g (inj₂ x) ≡ inj₂ (g x)
map≡inj₂ = refl

⊆-drop :
  (p⊆  : ys ⊆ x ∷ xs)
  (y∈  : y ∈ ys) (y∈′ : y ∈ xs)
  (p≡  : p⊆ y∈ ≡ there y∈′)
  --————————————————————————
  → Σ[ p⊆′ ∈ (ys ⊆ xs) ] (y∈′ ≡ p⊆′ y∈)
⊆-drop p⊆ y∈ y∈′ p≡ = {!!}


H : ∀ {A : Set} {xs ys : List A} {y : A}
  → (y∈ : y ∈ ys) (y∈′ : y ∈ xs ++ ys)
  → indexℕ y∈′ ≡ length xs + indexℕ y∈
  → ∈-++⁻ xs {ys} y∈′ ≡ inj₂ y∈
H {xs = []}{ys} y∈ y∈′ i≡ = cong inj₂ $ indexℕ-injective y∈′ y∈ i≡
H {xs = x ∷ xs}{ys} y∈ (here refl) ()
H {xs = x ∷ xs}{ys} y∈ (there y∈′) i≡ = qed
  where
    i≡′ : indexℕ y∈′ ≡ length xs + indexℕ y∈
    i≡′ = Nat.suc-injective i≡

    qedH : ∈-++⁻ xs y∈′ ≡ inj₂ y∈
    qedH = H {xs = xs} y∈ y∈′ i≡′

    qed : ∈-++⁻ (x ∷ xs) (there y∈′) ≡ inj₂ y∈
     -- ≈ Sum.map there id (∈-++⁻ xs y∈′) ≡ inj₂ y∈
    qed rewrite qedH = refl

Suffix⊆-++⁻-HELP :
  ∀ {A : Set} {xs ys : List A} {y : A}
  → (y∈ : y ∈ ys)
  → (p⊆ : ys ⊆ xs ++ ys)
  → indexℕ (p⊆ y∈) ≡ length xs + indexℕ y∈
  → ∈-++⁻ xs {ys} (p⊆ y∈) ≡ inj₂ y∈
Suffix⊆-++⁻-HELP {xs = xs}{ys} y∈ p⊆ p = H y∈ (p⊆ y∈) p

Suffix⊆-++⁻ :
  ∀ {A : Set} {xs ys : List A} {y : A}
  → (y∈ : y ∈ ys)
  → (p⊆ : ys ⊆ xs ++ ys)
  → (suffix-p : Suffix⊆ p⊆)
  → ∈-++⁻ xs {ys} (p⊆ y∈) ≡ inj₂ y∈
Suffix⊆-++⁻ {xs = xs}{ys} y∈ p⊆ suffix-p = Suffix⊆-++⁻-HELP y∈ p⊆ $
  begin
    indexℕ (p⊆ y∈)
  ≡⟨ suffix-p y∈ ⟩
    length (xs ++ ys) ∸ length ys + indexℕ y∈
  ≡⟨ cong (_+ _) (length-++-∸ {xs = xs}{ys}) ⟩
    length xs + indexℕ y∈
  ∎ where open ≡-Reasoning
{-
Suffix⊆-++⁻ {xs = []}{ys} y∈ p⊆ suffix-p = cong inj₂ p≡
  where
    i≡ : indexℕ (p⊆ y∈) ≡ indexℕ y∈
    i≡ rewrite Nat.n∸n≡0 (length ys) = suffix-p y∈

    p≡ : p⊆ y∈ ≡ y∈
    p≡ = indexℕ-injective (p⊆ y∈) y∈ i≡
Suffix⊆-++⁻ {xs = x ∷ xs}{ys} y∈ p⊆ suffix-p
  with p⊆ y∈ in p≡ | suffix-p y∈
... | here refl | eq
  = ⊥-elim $ contra {xs = xs}{ys = ys} eq
  where
    contra : ∀ {A : Set}{xs ys : List A}{k}
      → 0 ≢ suc (length (xs ++ ys)) ∸ length ys + k
    contra {xs = xs}{ys}{k} = ≢-sym $ Nat.m<n⇒n≢0 {m = length xs} $
      begin-strict
        length xs
      <⟨ Nat.≤-refl ⟩
        suc (length xs)
      ≤⟨ Nat.m≤m+n _ _ ⟩
        suc (length xs) + (length ys ∸ length ys)
      ≡⟨ sym $ Nat.+-∸-assoc (suc $ length xs) (Nat.≤-refl {x = length ys}) ⟩
        (suc $ length xs + length ys) ∸ length ys
      ≡⟨ refl ⟩
        suc (length xs + length ys) ∸ length ys
      ≡⟨ cong (_∸ length ys) $ cong suc $ sym $ L.length-++ xs ⟩
        suc (length (xs ++ ys)) ∸ length ys
      ≤⟨ Nat.m≤m+n _ k ⟩
        suc (length (xs ++ ys)) ∸ length ys + k
      ∎
      where open ≤-Reasoning
... | there y∈′ | eq
  = {!!}
-}
{- Goal: Sum.map there id (∈-++⁻ xs y∈′) ≡ inj₂ y∈
       ↔ ∈-++⁻ xs y∈′ ≡ inj₂ y∈
————————————————————————————————————————————————————————————
y∈       : y ∈ ys
p⊆       : ys ⊆ x ∷ xs ++ ys
suffix-p : Suffix⊆ p⊆
p≡       : p⊆ y∈ ≡ there y∈′
y∈′      : y ∈ xs ++ ys
eq       : suc (indexℕ y∈′) ≡⟨ p≡ ⟩
           index (p⊆ y∈) ≡
           suc (length xs + indexℕ y∈)
-}
{-
  = {!!}
  where
    i≡ : indexℕ (p⊆ y∈) ≡ suc (length xs + indexℕ y∈)
    i≡ rewrite p≡ =
      begin
        suc (indexℕ y∈′)
      ≡⟨ eq ⟩
        suc (length (xs ++ ys)) ∸ length ys + indexℕ y∈
      ≡⟨ cong (λ x → suc x ∸ length ys + indexℕ y∈) (L.length-++ xs) ⟩
        suc (length xs + length ys) ∸ length ys + indexℕ y∈
      ≡⟨ cong (λ x → x + indexℕ y∈) (Nat.m+n∸n≡m (suc $ length xs) (length ys)) ⟩
        suc (length xs) + indexℕ y∈
      ≡⟨⟩
        suc (length xs + indexℕ y∈)
      ∎ where open ≡-Reasoning

    IH : ∀ y∈. (p⊆ : ys ⊆ xs ++ ys) → Suffix⊆ p⊆ → ∈-++⁻ xs (p⊆ y∈) ≡ inj₂ y∈
    IH = Suffix⊆-++⁻ {xs = xs}{ys}

    -- qed : ∈-++⁻ xs y∈′ ≡ inj₂ y∈
-}
{-
  with ∈-++⁻ xs y∈′ | Suffix⊆-++⁻ {xs = xs}{ys} y∈
... | inj₁ y∈xs | IH
  = {!!}
... | inj₂ y∈ys | IH
  = cong inj₂ (indexℕ-injective y∈ys y∈ {!!})
-}

  {-

     qed : indexℕ y∈ys ≡ index y∈
  -}
  -- Suffix⊆-++⁻ {xs = xs}{ys} y∈ p⊆
  -- where
  --   qed : Sum.map there id (L.Any.++⁻ xs y∈′) ≡ inj₂ y∈
  --   qed = {!!}
-- Suffix⊆-++⁻ {xs = x ∷ xs} (here px) p⊆ suffix-p = {!suffix-p (here px)!}
-- Suffix⊆-++⁻ {xs = x ∷ xs} (there y∈) p⊆ suffix-p = {!suffix-p y∈!}
--   where
--     p⊆′ :

-- HELP :
--   ∀ {X X′ A B : Set}
--     {ys : List X′}

-- -- xs : List X
-- -- xs = map g ys

-- -- y : X
-- -- y = g y′

--     (f : X → List (A ⊎ B)
--     (g : X′ → X)
--     (eq : filter₂ (concat $ f <$> g <$> ys) ≡ xsᵇ ++ ys)
--   → ∀ {y′ : X′} (y∈ : y′ ∈ ys) (last-y∈ : Last y∈)
--     --————————————————
--   → ∈-++⁻ xs {ys}
--       (subst (y ∈_) eq
--           $ ( mapMaybe-⊆ isInj₂
--             $ ⊆-concat⁺ (∈-map⁺ f $ ∈-map⁺ g $ y∈})
--             $ p
--             ) y∈)
--   ≡ inj₂ y∈

-- -- ysᵃᵇ : List (A ⊎ B)
-- -- ysᵃᵇ = f y

-- -- ysᵇ : List B
-- -- ysᵇ = filter₂ ysᵃᵇ

-- -- xyssᵃᵇ = List $ List (A ⊎ B)
-- -- xyssᵃᵇ = map f xs

-- -- xysᵃᵇ : List (A ⊎ B)
-- -- xysᵃᵇ = concat xyssᵃᵇ

-- -- xysᵇ : List B
-- -- xysᵇ = filter₂ xysᵃᵇ

-- -- H : ysᵇ ⊆ xysᵇ
-- -- H = mapMaybe-⊆ isInj₂ ?₁
-- --   where
-- --     ?₁ : ysᵃᵇ ⊆ xysᵃᵇ
-- --           -- ≈ concat xss
-- --     ?₁ = ⊆-concat⁺ ?₂

-- --     ?₂ : ysᵃᵇ ∈ xyssᵃᵇ
-- --     -- ≈ f ys
-- --           -- ≈ map f xs
-- --     ?₂ = ∈-map⁺ f ?₃

-- --     ?₃ : y ∈ xs
-- --     -- ≈ g y′
-- --         -- ≈ map g xs′
-- --     ?₃ = ∈-map⁺ g ?₄

-- --     y∈ : y′ ∈ ys
-- --     y∈ = p
