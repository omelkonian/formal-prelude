module Prelude.Lists.SuffixSubset where

open import Prelude.Init
open L.Mem
open Nat; open Nat.Ord
open import Prelude.General
open import Prelude.InferenceRules
open import Prelude.Split

open import Prelude.Lists.Core
open import Prelude.Lists.Indexed
open import Prelude.Lists.Empty
open import Prelude.Lists.Concat
open import Prelude.Lists.Count
open import Prelude.Lists.Mappings
open import Prelude.Lists.Membership
open import Prelude.Lists.MapMaybe

-- ** Suffix⊆
module _ {A : Set ℓ} where

  Suffix⊆ : ∀ {xs ys : List A} → Pred (xs ⊆ ys) ℓ
  Suffix⊆ {xs = xs}{ys} xs⊆ = ∀ {x} (x∈ : x ∈ xs) →
    indexℕ (xs⊆ x∈) ≡ (length ys ∸ length xs) + indexℕ x∈

  infix 4 _⊆ʳ_
  _⊆ʳ_ : Rel (List A) ℓ
  xs ⊆ʳ ys = Σ (xs ⊆ ys) Suffix⊆

  Suffix≗ : ∀ {xs ys : List A} → Pred (xs ⊆ ys) ℓ
  Suffix≗ {xs = xs} xs⊆ = ∀ {x} (x∈ : x ∈ xs) → indexℕ (xs⊆ x∈) ≡ indexℕ x∈

private variable
  A : Set ℓ
  B : Set ℓ′
  x x′ y z : A
  xs xs′ ys zs : List A
  xss yss : List (List A)
  P : Pred₀ A

Suffix⊆-++⁺ʳ : Suffix⊆ (∈-++⁺ʳ xs {ys})
Suffix⊆-++⁺ʳ {xs = []}     {ys} x∈
  rewrite Nat.n∸n≡0 (length ys) = refl
Suffix⊆-++⁺ʳ {xs = x ∷ xs} {ys} x∈
  rewrite Suffix⊆-++⁺ʳ {xs = xs} x∈
        | length-++-∸ {xs = xs}{ys}
        | length-++-∸ {xs = x ∷ xs}{ys}
        = refl

Suffix⊆-++⁺ˡ : Null ys → Suffix⊆ (∈-++⁺ˡ {xs = xs} {ys})
Suffix⊆-++⁺ˡ {ys = .[]} {xs = xs} refl x∈ =
  begin
    indexℕ (∈-++⁺ˡ x∈)
  ≡⟨ indexℕ-++⁺ˡ x∈ ⟩
    indexℕ x∈
  ≡⟨ cong (_+ indexℕ x∈) $ sym $ Nat.n∸n≡0 (length xs) ⟩
    length xs ∸ length xs + indexℕ x∈
  ≡⟨ cong (λ ◆ → length ◆ ∸ length xs + indexℕ x∈) $ sym $ L.++-identityʳ xs ⟩
    length (xs ++ []) ∸ length xs + indexℕ x∈
  ∎ where open ≡-Reasoning

Last∈-concat : ∀ (xs∈ : xs ∈ xss) →
  Last∈ xs∈
  ───────────────────────
  Suffix⊆ (⊆-concat⁺ xs∈)
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

Suffix⊆-there⁺ : ∀ (xs⊆ : xs ⊆ ys) →
  ∙ length xs ≤ length ys
  ∙ Suffix⊆ xs⊆
    ───────────
    Suffix⊆ {xs = xs}{y ∷ ys} (there {x = y} ∘ xs⊆)
Suffix⊆-there⁺ {xs = xs} {ys = ys} {y = y} p l≤ suffix-p x∈
  rewrite suffix-p x∈
        | Nat.+-suc (length ys ∸ length xs) (indexℕ x∈)
        = H (length ys) (length xs) (indexℕ x∈) l≤
  where
    H : ∀ m n k → n ≤ m → suc (m ∸ n + k) ≡ suc m ∸ n + k
    H m       zero    k _         = refl
    H (suc m) (suc n) k (s≤s n≤m) rewrite H m n k n≤m = refl

-- ** Suffix⊆
Σ-over-∀′ : ∀ {A : Set ℓ} {X : A → Set ℓ′} {Y : (a : A) → X a → Set ℓ″}
  → ({a : A} → Σ (X a) (Y a))
  → Σ ({a : A} → X a) λ x → ({a : A} → Y a x)
Σ-over-∀′ go = (λ {a} → go {a} .proj₁) , (λ {a} → go {a} .proj₂)

Σ-over-∀ : ∀ {A : Set ℓ} {X : A → Set ℓ′} {Y : (a : A) → X a → Set ℓ″}
  → ((a : A) → Σ (X a) (Y a))
  → Σ ((a : A) → X a) λ x → ((a : A) → Y a (x a))
Σ-over-∀ go = (proj₁ ∘ go) , (proj₂ ∘ go)

Suffix⊆⇒len≤ :
  xs ⊆ʳ ys
  ─────────────────────
  length xs ≤ length ys
Suffix⊆⇒len≤ {xs = []} {ys}         _         = z≤n
Suffix⊆⇒len≤ {xs = x ∷ xs} {[]}     (xs⊆ , _) = case xs⊆ (here refl) of λ ()
Suffix⊆⇒len≤ {xs = x ∷ xs} {y ∷ ys} (xs⊆ , p)
  = s≤s $ Suffix⊆⇒len≤ $ Σ-over-∀′ $ Σ-over-∀ go
  where
    go : ∀ {x} (x∈ : x ∈ xs) → Σ (x ∈ ys) λ y∈ → indexℕ y∈ ≡ length ys ∸ length xs + indexℕ x∈
    go x∈ with xs⊆ (there x∈) | p (there x∈)
    ... | here refl | absurd
      rewrite Nat.+-suc (length ys ∸ length xs) (indexℕ x∈)
      = case absurd of λ ()
    ... | there y∈  | i≡
      rewrite Nat.+-suc (length ys ∸ length xs) (indexℕ x∈)
      = y∈ , Nat.suc-injective i≡

Suffix≗-tail : ∀ (xs⊆ : x ∷ xs ⊆ y ∷ ys) →
  Suffix≗ xs⊆
  ───────────────────
  Σ (xs ⊆ ys) Suffix≗
Suffix≗-tail {xs = xs} {ys = ys} xs⊆ p = Σ-over-∀′ $ Σ-over-∀ go
  where
    go : ∀ {x} (x∈ : x ∈ xs) → Σ (x ∈ ys) λ y∈ → indexℕ y∈ ≡ indexℕ x∈
    go z∈ with xs⊆ (there z∈) | p (there z∈)
    ... | there z∈′ | eq = z∈′ , Nat.suc-injective eq

Suffix⊆-tail :
  ∙ length xs ≤ length ys
  ∙ xs ⊆ʳ y ∷ ys
    ─────────────────────
    xs ⊆ʳ ys
Suffix⊆-tail {xs = xs} {ys = ys} len≤ (xs⊆ , p) = Σ-over-∀′ $ Σ-over-∀ go
  where
    go : ∀ {x} (x∈ : x ∈ xs) → Σ (x ∈ ys) λ y∈ → indexℕ y∈ ≡ (length ys ∸ length xs) + indexℕ x∈
    go x∈ with xs⊆ x∈ | p x∈
    ... | here refl | absurd
      rewrite Nat.+-∸-assoc 1  {length ys} {length xs} len≤
      = case absurd of λ ()
    ... | there y∈  | eq
      = y∈ , Nat.suc-injective qed
      where
        qed : suc (indexℕ y∈) ≡ suc (length ys ∸ length xs + indexℕ x∈)
        qed rewrite eq | Nat.+-∸-assoc 1 {length ys} {length xs} len≤ = refl

Suffix⊆⇒Suffix≗ :
  ∀ (xs⊆ : xs ⊆ ys)
  → length ys ≤ length xs
  ∙ Suffix⊆ xs⊆
    ─────────────────────
    Suffix≗ xs⊆
Suffix⊆⇒Suffix≗ {xs = xs} {ys = ys} xs⊆ len≤ suffix-xs⊆ x∈
  rewrite suffix-xs⊆ x∈ | Nat.m≤n⇒m∸n≡0 len≤ = refl

Suffix≗→≡ :
  ∀ (xs⊆ : xs ⊆ ys)
  → length ys ≤ length xs
  ∙ Suffix≗ xs⊆
    ─────────────────────
    xs ≡ ys
Suffix≗→≡ {xs = []} {[]} _ _ _ = refl
Suffix≗→≡ {xs = x ∷ xs} {[]} xs⊆ len≤ p = case xs⊆ (here refl) of λ ()
Suffix≗→≡ {xs = x ∷ xs} {y ∷ ys} xs⊆ (s≤s len≤) p
  with xs⊆ (here refl) | p (here refl)
... | there _ | ()
... | here refl | _
  = let xs⊆′ , p′ = Suffix≗-tail xs⊆ p
    in cong (x ∷_) (Suffix≗→≡ xs⊆′ len≤ p′)

Suffix⊆∧len≤⇒≡ :
  ∙ xs ⊆ʳ ys
  ∙ length ys ≤ length xs
    ─────────────────────
    xs ≡ ys
Suffix⊆∧len≤⇒≡ (xs⊆ , p) len≤ = Suffix≗→≡ xs⊆ len≤ $ Suffix⊆⇒Suffix≗ xs⊆ len≤ p

private
  Suffix⊆⇒∃++/≡ :
    ∙ length ys ≡ length xs
    ∙ xs ⊆ʳ ys
      ────────────────────────
      ∃ λ ysˡ → ys ≡ ysˡ ++ xs
  Suffix⊆⇒∃++/≡ {ys = ys} {xs = xs} len≡ p
    rewrite Suffix⊆∧len≤⇒≡ p (Nat.≤-reflexive len≡)
    = [] , refl

  Suffix⊆⇒∃++/> :
    ∙ length ys > length xs
    ∙ xs ⊆ʳ ys
      ────────────────────────
      ∃ λ ysˡ → ys ≡ ysˡ ++ xs
  Suffix⊆⇒∃++/> {ys = y ∷ ys} {xs = xs} (s≤s len≤) p
    with xs⊆′ , p′ ← Suffix⊆-tail len≤ p
    with length ys ≟ length xs
  ... | yes len≡ = [ y ] , cong (y ∷_) ys≡
    where
      ys≡ : ys ≡ xs
      ys≡ = sym $ Suffix⊆∧len≤⇒≡ (xs⊆′ , p′) (Nat.≤-reflexive len≡)
  ... | no  len≢ = qed
    where
      len< : length xs < length ys
      len< = Nat.≤∧≢⇒< len≤ (≢-sym len≢)

      IH : ∃ λ ysˡ → ys ≡ ysˡ ++ xs
      IH = Suffix⊆⇒∃++/> len< (xs⊆′ , p′)

      qed : ∃ λ ysˡ → y ∷ ys ≡ ysˡ ++ xs
      qed = let ysˡ , ys≡ = IH
            in y ∷ ysˡ , cong (y ∷_) ys≡

Suffix⊆⇒∃++ :
  xs ⊆ʳ ys
  ────────────────────────
  ∃ λ ysˡ → ys ≡ ysˡ ++ xs
Suffix⊆⇒∃++ {xs = xs} {ys = ys} p
  with length ys ≟ length xs
... | yes len≡ = Suffix⊆⇒∃++/≡ len≡ p
... | no  len≢ = Suffix⊆⇒∃++/> len< p
  where len< : length xs < length ys
        len< = Nat.≤∧≢⇒< (Suffix⊆⇒len≤ p) $ ≢-sym len≢

Suffix⊆-++ : ∀ (xs⊆ : xs ⊆ ys ++ xs) →
  Suffix⊆ xs⊆
  ─────────────────────────────────────────────
  ∀ {x} (x∈ : x ∈ xs) → xs⊆ x∈ ≡ ∈-++⁺ʳ ys x∈
Suffix⊆-++ {xs = xs} {ys = []} xs⊆ p x∈
  rewrite L.++-identityʳ xs
        | Nat.n∸n≡0 (length xs)
        = indexℕ-injective (xs⊆ x∈) x∈ (p x∈)
Suffix⊆-++ {xs = xs} {ys = y ∷ ys} xs⊆ p x∈
  with len≤ ←
    (let open ≤-Reasoning in
      begin length xs             ≤⟨ Nat.≤-stepsʳ _ Nat.≤-refl ⟩
            length xs + length ys ≡⟨ Nat.+-comm (length xs) _ ⟩
            length ys + length xs ≡⟨ sym $ L.length-++ ys ⟩
            length (ys ++ xs)     ∎)
  -- with xs⊆′ , p′ ← Suffix⊆-tail len≤ (xs⊆ , p)
  -- with IH ← Suffix⊆-++ xs⊆′ p′ x∈
  with xs⊆ x∈ | p x∈ | uncurry Suffix⊆-++ (Suffix⊆-tail len≤ (xs⊆ , p)) x∈
... | here refl | absurd | _
  rewrite Nat.+-∸-assoc 1  {length (ys ++ xs)} {length xs} len≤
  = case absurd of λ ()
... | there y∈  | _ | IH
  = cong there IH

Suffix⊆-length? :
  xs ⊆ʳ ys
  ───────────────────────────────────
  (xs ≡ ys) ⊎ (length xs < length ys)
Suffix⊆-length? {xs = xs}{ys} p
  with length xs ≟ length ys
... | yes len≡ = inj₁ xs≡
  where
    xs≡ : xs ≡ ys
    xs≡ = Suffix⊆∧len≤⇒≡ p (Nat.≤-reflexive $ sym len≡)
... | no len≢ = inj₂ len<
  where
    len< : length xs < length ys
    len< = Nat.≤∧≢⇒< (Suffix⊆⇒len≤ p) len≢

module _ (P? : Decidable¹ P) where
  ⊆ʳ-count : xs ⊆ʳ ys → count P? xs ≤ count P? ys
  ⊆ʳ-count {xs = xs} {ys} p
    with ysˡ , refl ← Suffix⊆⇒∃++ p
    = begin count P? xs                ≤⟨ Nat.m≤n+m _ _ ⟩
            count P? ysˡ + count P? xs ≡⟨ sym $ count-++ P? ysˡ ⟩
            count P? (ysˡ ++ xs)       ∎ where open ≤-Reasoning

Suffix⊆-step? : ∀ {x y : A} (xs⊆ : (x ∷ xs ⊆ y ∷ ys)) →
  Suffix⊆ xs⊆
  ───────────────────────────────────
  (case xs⊆ (here refl) of λ where
    (here  _) → xs ≡ ys
    (there _) → x ∷ xs ⊆ʳ ys
  )
Suffix⊆-step? {xs = xs} {ys = ys} {x = x} {y = y} xs⊆ p
  with Suffix⊆-length? (xs⊆ , p)
Suffix⊆-step? {xs = xs} {ys = ys} {x = x} {y = y} xs⊆ p | inj₁ refl
  with xs⊆ (here refl) | p (here refl)
... | here refl | _
  = refl
... | there y∈  | absurd
  rewrite Nat.n∸n≡0 (length xs)
  = case absurd of λ ()
Suffix⊆-step? {xs = xs} {ys = ys} {x = x} {y = y} xs⊆ p | inj₂ (s≤s len<)
  with xs⊆ (here refl) | p (here refl)
... | here refl | ♯ys∸♯xs≡0
  rewrite Nat.+-identityʳ (length ys ∸ length xs)
  = L.∷-injectiveʳ $ Suffix⊆∧len≤⇒≡ (xs⊆ , p) (Nat.m∸n≡0⇒m≤n $ sym ♯ys∸♯xs≡0)
... | there y∈ | pp
  = xs⊆′ , p′
  where
    xs⊆′ : x ∷ xs ⊆ ys
    xs⊆′ (here refl) = y∈
    xs⊆′ (there x∈) with xs⊆ (there x∈) | p (there x∈)
    ... | here refl | absurd
      rewrite Nat.+-suc (length ys ∸ length xs) (indexℕ x∈)
      = case absurd of λ ()
    ... | there y∈ | _ = y∈

    p′ : Suffix⊆ xs⊆′
    p′ (here refl)
      rewrite Nat.+-identityʳ $ length ys ∸ length (x ∷ xs)
      = Nat.suc-injective
      $ begin
        suc (indexℕ y∈)
      ≡⟨ pp ⟩
        length ys ∸ length xs + 0
      ≡⟨ Nat.+-identityʳ $ length ys ∸ length xs ⟩
        length ys ∸ length xs
      ≡⟨ sym $ 1+[m∸[1+n]]≡m∸n (length ys) (length xs) len< ⟩
        suc (length ys ∸ suc (length xs))
      ∎ where open ≡-Reasoning
    p′ (there x∈) with xs⊆ (there x∈) | p (there x∈)
    ... | here refl | absurd
      rewrite Nat.+-suc (length ys ∸ length xs) (indexℕ x∈)
      = case absurd of λ ()
    ... | there y∈ | ppp
      = Nat.suc-injective
      $ begin
        suc (indexℕ y∈)
      ≡⟨ ppp ⟩
        length ys ∸ length xs + suc (indexℕ x∈)
      ≡⟨ cong (_+ suc (indexℕ x∈)) $ sym $ 1+[m∸[1+n]]≡m∸n (length ys) (length xs) len< ⟩
        suc (length ys ∸ suc (length xs) + suc (indexℕ x∈))
      ∎ where open ≡-Reasoning

⊆ʳ-spiltAtʳ : ∀ (xs⊆ : xs ⊆ ys) →
  Suffix⊆ xs⊆
  ───────────────────────────────────────
  ∀ {x} (x∈ : x ∈ xs) →
      splitAtʳ xs (index⁺ x∈)
    ≡ splitAtʳ ys (index⁺ $ xs⊆ x∈)
⊆ʳ-spiltAtʳ {xs = xs} {ys} xs⊆ p {x} x∈
  with ys , refl ← Suffix⊆⇒∃++ (xs⊆ , p)
  = begin
    splitAt xs (index⁺ x∈) .proj₂
  ≡⟨ splitAt-∈-++⁺ʳ {ys = ys} x∈ ⟩
    splitAtʳ (ys ++ xs) (index⁺ $ ∈-++⁺ʳ ys x∈)
  ≡⟨ cong (λ ◆ → splitAtʳ (ys ++ xs) (index⁺ ◆)) (sym $ Suffix⊆-++ xs⊆ p x∈) ⟩
    splitAtʳ (ys ++ xs) (index⁺ $ xs⊆ x∈)
  ∎ where open ≡-Reasoning

⊆ʳ-splitAtˡ : ∀ (x∈ : x ∈ xs) (xs⊆ : xs ⊆ ys) →
  Suffix⊆ xs⊆
  ───────────────────────────────
     splitAtˡ xs (index⁺ x∈)
  ⊆ʳ splitAtˡ ys (index⁺ $ xs⊆ x∈)
⊆ʳ-splitAtˡ  {x = x} {xs = xs} {ys = ys} x∈ xs⊆ p
  with ys , refl ← Suffix⊆⇒∃++ (xs⊆ , p)
  rewrite Suffix⊆-++ xs⊆ p x∈
        | splitAt-∈-++⁺ˡ {ys = ys} x∈
  = ∈-++⁺ʳ ys , Suffix⊆-++⁺ʳ

module _ {A B : Set} (f : A → Maybe B) where

  open MapMaybeDSL f

  Suffix⊆⇒⊥⋯ : ∀ (xs⊆ : xs ⊆ ys) →
    Suffix⊆ xs⊆
    ─────────────────────
    ∀ {x} (x∈ : x ∈ xs) →
      (x∈ ⋯⊥) ≡ (xs⊆ x∈ ⋯⊥)
  Suffix⊆⇒⊥⋯ {xs = _ ∷ _} {ys = []} xs⊆ _ _
    = case xs⊆ (here refl) of λ ()
  Suffix⊆⇒⊥⋯ {xs = x ∷ xs} {ys = y ∷ ys} xs⊆ p x∈ =
    cong (countNothing f) $ ⊆ʳ-spiltAtʳ xs⊆ p x∈

  Suffix⊆-mapMaybe : ∀ (xs⊆ : xs ⊆ ys) →
    Suffix⊆ xs⊆
    ──────────────────────────
    Suffix⊆ (mapMaybe-⊆ f xs⊆)
  Suffix⊆-mapMaybe {xs = xs@(_ ∷ _)}{ys} xs⊆ p {y} y∈ =
    begin
      indexℕ (mapMaybe-⊆ f xs⊆ y∈)
    ≡⟨⟩
      indexℕ (∈-mapMaybe⁺ f x∈′ fx≡)
    ≡⟨ indexℕ-mapMaybe⁺ f x∈′ fx≡ ⟩
      indexℕ x∈′ ∸ ⊥⋯ x∈′
    ≡⟨ cong (_∸ ⊥⋯ x∈′) (p x∈) ⟩
      (♯ys ∸ ♯xs + x∈ⁱ) ∸ ⊥⋯ x∈′
    ≡⟨ cong (λ ◆ → (♯ys ∸ ♯xs + ◆) ∸ ⊥⋯ x∈′) (indexℕ-mapMaybe⁻ f y∈) ⟩
      (♯ys ∸ ♯xs + (⊥⋯ x∈ + y∈ⁱ)) ∸ ⊥⋯ x∈′
    ≡⟨⟩
      ((♯ys ∸ ♯xs) + (⊥⋯ x∈ + y∈ⁱ)) ∸ ⊥⋯ x∈′
    ≡⟨ cong (_∸ ⊥⋯ x∈′) $ sym $ Nat.+-assoc (♯ys ∸ ♯xs) _ _ ⟩
      (((♯ys ∸ ♯xs) + ⊥⋯ x∈) + y∈ⁱ) ∸ ⊥⋯ x∈′
    ≡⟨ Nat.+-∸-comm y∈ⁱ p≤ ⟩
      (((♯ys ∸ ♯xs) + ⊥⋯ x∈) ∸ ⊥⋯ x∈′) + y∈ⁱ
    ≡⟨ cong (_+ y∈ⁱ) HELP ⟩
      ((♯ys ∸ ⊥⋯ x∈′) ∸ (♯xs ∸ ⊥⋯ x∈)) + y∈ⁱ
    ≡⟨ cong (_+ y∈ⁱ) $
       begin
         ((♯ys ∸ ⊥⋯ x∈′) ∸ (♯xs ∸ ⊥⋯ x∈))
       ≡⟨ sym $ m∸[z+o]∸n∸[w+o]≡[m∸z]∸[n∸w] ♯ys ♯xs (⊥⋯ x∈′) (x∈ ⋯⊥) (⊥⋯ x∈) o≤ ⟩
         ((♯ys ∸ (⊥⋯ x∈′ + x∈ ⋯⊥)) ∸ (♯xs ∸ (⊥⋯ x∈ + x∈ ⋯⊥)))
       ≡⟨ cong (λ ◆ → ((♯ys ∸ (⊥⋯ x∈′ + ◆)) ∸ (♯xs ∸ (⊥⋯ x∈ + x∈ ⋯⊥)))) $ Suffix⊆⇒⊥⋯ xs⊆ p x∈ ⟩
         ((♯ys ∸ (⊥⋯ x∈′ + x∈′ ⋯⊥)) ∸ (♯xs ∸ (⊥⋯ x∈ + x∈ ⋯⊥)))
       ≡⟨ cong (λ ◆ → ((♯ys ∸ (⊥⋯ x∈′ + x∈′ ⋯⊥)) ∸ (♯xs ∸ ◆))) $ sym $ countNothing≡⊥⋯⊥ x∈ ⟩
         ((♯ys ∸ (⊥⋯ x∈′ + x∈′ ⋯⊥)) ∸ (♯xs ∸ ♯xs˘))
       ≡⟨ cong (λ ◆ → ((♯ys ∸ ◆) ∸ (♯xs ∸ ♯xs˘))) $ sym $ countNothing≡⊥⋯⊥ x∈′ ⟩
         ((♯ys ∸ ♯ys˘) ∸ (♯xs ∸ ♯xs˘))
       ∎ ⟩
      ((♯ys ∸ ♯ys˘) ∸ (♯xs ∸ ♯xs˘)) + y∈ⁱ
    ≡⟨ cong (λ ◆ → (♯ys ∸ ♯ys˘) ∸ ◆ + indexℕ y∈) (sym $ length-mapMaybe f {xs = xs}) ⟩
      (♯ys ∸ ♯ys˘) ∸ length (mapMaybe f xs) + indexℕ y∈
    ≡⟨ cong (λ ◆ → ◆ ∸ length (mapMaybe f xs) + indexℕ y∈) (sym $ length-mapMaybe f {xs = ys}) ⟩
      length (mapMaybe f ys) ∸ length (mapMaybe f xs) + indexℕ y∈
    ∎
    where
      ∈⁻ = ∈-mapMaybe⁻ f {xs = xs} y∈; x∈ = ∈⁻ .proj₂ .proj₁; fx≡ = ∈⁻ .proj₂ .proj₂; x∈′ = xs⊆ x∈
      ♯xs = length xs; ♯xs˘ = countNothing f xs
      ♯ys = length ys; ♯ys˘ = countNothing f ys
      x∈ⁱ = indexℕ x∈; y∈ⁱ = indexℕ y∈
      ♯xs⊤ = countJust f xs; ♯ys⊤ = countJust f ys

      len≤ : ♯xs ≤ ♯ys
      len≤ = Suffix⊆⇒len≤ (xs⊆ , p)

      len⊤≤ : ♯xs⊤ ≤ ♯ys⊤
      len⊤≤ = ⊆ʳ-count (is-just? ∘ f) (xs⊆ , p)

      p≤ : ⊥⋯ x∈′ ≤ (♯ys ∸ ♯xs) + ⊥⋯ x∈
      p≤ =
        begin
          ⊥⋯ x∈′
        ≤⟨ Nat.m≤n+m _ _ ⟩
          (♯ys⊤ ∸ ♯xs⊤) + ⊥⋯ x∈′
        ≡⟨ sym $ Nat.+-∸-comm (⊥⋯ x∈′) len⊤≤ ⟩
          (♯ys⊤ + ⊥⋯ x∈′) ∸ ♯xs⊤
        ≡⟨ sym $ Nat.m∸n+n≡m $
           begin
             ⊥⋯ x∈
           ≤⟨ ⊆ʳ-count (is-nothing? ∘ f) (⊆ʳ-splitAtˡ x∈ xs⊆ p) ⟩
             ⊥⋯ x∈′
           ≤⟨ Nat.m≤n+m _ _ ⟩
             (♯ys⊤ ∸ ♯xs⊤) + ⊥⋯ x∈′
           ≡⟨ sym $ Nat.+-∸-comm (⊥⋯ x∈′) len⊤≤ ⟩
             (♯ys⊤ + ⊥⋯ x∈′) ∸ ♯xs⊤
           ∎ ⟩
          (((♯ys⊤ + ⊥⋯ x∈′) ∸ ♯xs⊤) ∸ ⊥⋯ x∈) + ⊥⋯ x∈
        ≡⟨ cong (_+ ⊥⋯ x∈) $ Nat.∸-+-assoc (♯ys⊤ + ⊥⋯ x∈′) ♯xs⊤ (⊥⋯ x∈) ⟩
          ((♯ys⊤ + ⊥⋯ x∈′) ∸ (♯xs⊤ + ⊥⋯ x∈)) + ⊥⋯ x∈
        ≡⟨ cong (_+ ⊥⋯ x∈) $ sym $ Nat.[m+n]∸[m+o]≡n∸o (x∈ ⋯⊥) (♯ys⊤ + ⊥⋯ x∈′) (♯xs⊤ + ⊥⋯ x∈) ⟩
          ((x∈ ⋯⊥ + (♯ys⊤ + ⊥⋯ x∈′)) ∸ (x∈ ⋯⊥ + (♯xs⊤ + ⊥⋯ x∈))) + ⊥⋯ x∈
        ≡⟨ cong (λ ◆ → ((x∈ ⋯⊥ + (♯ys⊤ + ⊥⋯ x∈′)) ∸ ◆) + ⊥⋯ x∈) $ +-reassoc (x∈ ⋯⊥) ♯xs⊤ (⊥⋯ x∈) ⟩
          ((x∈ ⋯⊥ + (♯ys⊤ + ⊥⋯ x∈′)) ∸ (♯xs⊤ + (⊥⋯ x∈ + x∈ ⋯⊥))) + ⊥⋯ x∈
        ≡⟨ cong (λ ◆ → (◆ ∸ (♯xs⊤ + (⊥⋯ x∈ + x∈ ⋯⊥))) + ⊥⋯ x∈) $ +-reassoc (x∈ ⋯⊥) ♯ys⊤ (⊥⋯ x∈′) ⟩
          ((♯ys⊤ + (⊥⋯ x∈′ + x∈ ⋯⊥)) ∸ (♯xs⊤ + (⊥⋯ x∈ + x∈ ⋯⊥))) + ⊥⋯ x∈
        ≡⟨ cong (λ ◆ → ((♯ys⊤ + (⊥⋯ x∈′ + ◆)) ∸ (♯xs⊤ + (⊥⋯ x∈ + x∈ ⋯⊥))) + ⊥⋯ x∈) $ Suffix⊆⇒⊥⋯ xs⊆ p x∈ ⟩
          ((♯ys⊤ + (⊥⋯ x∈′ + x∈′ ⋯⊥)) ∸ (♯xs⊤ + (⊥⋯ x∈ + x∈ ⋯⊥))) + ⊥⋯ x∈
        ≡⟨ cong (λ ◆ → ((♯ys⊤ + ◆) ∸ (♯xs⊤ + (⊥⋯ x∈ + x∈ ⋯⊥))) + ⊥⋯ x∈) (sym $ countNothing≡⊥⋯⊥ x∈′) ⟩
          ((♯ys⊤ + ♯ys˘) ∸ (♯xs⊤ + (⊥⋯ x∈ + x∈ ⋯⊥))) + ⊥⋯ x∈
        ≡⟨ cong (λ ◆ → ((♯ys⊤ + ♯ys˘) ∸ (♯xs⊤ + ◆)) + ⊥⋯ x∈) (sym $ countNothing≡⊥⋯⊥ x∈) ⟩
          ((♯ys⊤ + ♯ys˘) ∸ (♯xs⊤ + ♯xs˘)) + ⊥⋯ x∈
        ≡⟨ cong (λ ◆ → ((♯ys⊤ + ♯ys˘) ∸ ◆) + ⊥⋯ x∈) $′ sym $ count-⊤⊥ f {xs = xs} ⟩
          ((♯ys⊤ + ♯ys˘) ∸ ♯xs) + ⊥⋯ x∈
        ≡⟨ cong (λ ◆ → (◆ ∸ ♯xs) + ⊥⋯ x∈) $′ sym $ count-⊤⊥ f {xs = ys} ⟩
          (♯ys ∸ ♯xs) + ⊥⋯ x∈
        ∎ where open ≤-Reasoning

      ⊥⋯x∈≤ : ⊥⋯ x∈ ≤ ♯xs
      ⊥⋯x∈≤ = begin ⊥⋯ x∈            ≤⟨ length-count (is-nothing? ∘ f) ⟩
                   length (x∈ ∙left) ≡⟨ length-∈∙left x∈ ⟩
                   suc (indexℕ x∈)   ≤⟨ F.toℕ<n (L.Any.index x∈) ⟩
                   ♯xs               ∎ where open ≤-Reasoning

      o≤ : x∈ ⋯⊥ ≤ ♯xs ∸ ⊥⋯ x∈
      o≤ =
        begin
          x∈ ⋯⊥
        ≤⟨ Nat.m≤n+m (x∈ ⋯⊥) (♯xs ∸ ♯xs˘) ⟩
          (♯xs ∸ ♯xs˘) + x∈ ⋯⊥
        ≡⟨ sym $ Nat.+-∸-comm (x∈ ⋯⊥) (length-count (is-nothing? ∘ f) {xs = xs}) ⟩
          (♯xs + x∈ ⋯⊥) ∸ ♯xs˘
        ≡⟨ cong ((♯xs + x∈ ⋯⊥) ∸_) $ countNothing≡⊥⋯⊥ x∈ ⟩
          (♯xs + x∈ ⋯⊥) ∸ (⊥⋯ x∈ + x∈ ⋯⊥)
        ≡⟨ m+z∸n+z≡m∸n ♯xs (⊥⋯ x∈) (x∈ ⋯⊥) ⟩
          ♯xs ∸ ⊥⋯ x∈
        ∎ where open ≤-Reasoning

      open ≡-Reasoning

      HELP : ((♯ys ∸ ♯xs) + ⊥⋯ x∈) ∸ ⊥⋯ x∈′ ≡ (♯ys ∸ ⊥⋯ x∈′) ∸ (♯xs ∸ ⊥⋯ x∈)
      HELP with ♯xs ≟ ♯ys
      ... | yes len≡
        rewrite ∸-∸-comm ♯ys (⊥⋯ x∈′) (♯xs ∸ ⊥⋯ x∈)
        = cong (_∸ (⊥⋯ x∈′)) $ sym $
          begin
            ♯ys ∸ (♯xs ∸ ⊥⋯ x∈)
          ≡⟨ cong (λ ◆ → ♯ys ∸ (◆ ∸ ⊥⋯ x∈)) len≡ ⟩
            ♯ys ∸ (♯ys ∸ ⊥⋯ x∈)
          ≡⟨ Nat.m∸[m∸n]≡n $ ≤-trans ⊥⋯x∈≤ len≤ ⟩
            ⊥⋯ x∈
          ≡⟨ cong (_+ ⊥⋯ x∈) $ sym $ Nat.n∸n≡0 ♯ys ⟩
            ♯ys ∸ ♯ys + ⊥⋯ x∈
          ≡⟨ cong (λ ◆ → ♯ys ∸ ◆ + ⊥⋯ x∈) $ sym len≡ ⟩
            ♯ys ∸ ♯xs + ⊥⋯ x∈
          ∎
      ... | no  len≢ =
        begin
          ((♯ys ∸ ♯xs) + ⊥⋯ x∈) ∸ ⊥⋯ x∈′
        ≡⟨ cong (_∸ ⊥⋯ x∈′) $ sym $ ∸-∸-assoc ♯ys ♯xs (⊥⋯ x∈) (Nat.≤∧≢⇒< len≤ len≢) ⊥⋯x∈≤ ⟩
          (♯ys ∸ (♯xs ∸ ⊥⋯ x∈)) ∸ ⊥⋯ x∈′
        ≡⟨ ∸-∸-comm ♯ys (♯xs ∸ ⊥⋯ x∈) (⊥⋯ x∈′) ⟩
          (♯ys ∸ ⊥⋯ x∈′) ∸ (♯xs ∸ ⊥⋯ x∈)
        ∎

Suffix⊆-++⁻ :
  ∀ (y∈ : y ∈ ys)
  → (p⊆ : ys ⊆ xs ++ ys)
  → Suffix⊆ p⊆
    ───────────────────────────────
    ∈-++⁻ xs {ys} (p⊆ y∈) ≡ inj₂ y∈
Suffix⊆-++⁻ {ys = ys} {xs = xs} y∈ p⊆ suffix-p = indexℕ-++⁻ y∈ (p⊆ y∈) $
  begin indexℕ (p⊆ y∈)                            ≡⟨ suffix-p y∈ ⟩
        length (xs ++ ys) ∸ length ys + indexℕ y∈ ≡⟨ cong (_+ _) (length-++-∸ {xs = xs}{ys}) ⟩
        length xs + indexℕ y∈                     ∎ where open ≡-Reasoning
