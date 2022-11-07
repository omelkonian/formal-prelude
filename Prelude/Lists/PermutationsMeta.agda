------------------------------------------------------------------------
-- Meta-properties of permuting lists with _↭_.

module Prelude.Lists.PermutationsMeta where

open import Prelude.Init; open SetAsType
open L.Mem using (_∈_; mapWith∈; ∈-map⁻)
open L.Perm hiding (trans)
open import Prelude.InferenceRules
open import Prelude.Decidable
open import Prelude.General
open import Prelude.Bifunctor

open import Prelude.Lists.Permutations
open import Prelude.Lists.Membership
open import Prelude.Lists.Concat
open import Prelude.Lists.MapMaybe

private variable
  A : Type ℓ
  B : Type ℓ′
  x y : A
  xs ys zs ws : List A
  xss yss : List (List A)

open ≡-Reasoning

sym∘cong : ∀ {x y : A} (f : A → B) (eq : x ≡ y)
  → sym (cong f eq) ≡ cong f (sym eq)
sym∘cong _ refl = refl

↭-trans∘reflˡ : (p↭ : xs ↭ ys) → L.Perm.↭-trans refl p↭ ≡ p↭
↭-trans∘reflˡ _ = refl

↭-trans∘reflʳ : (p↭ : xs ↭ ys) → L.Perm.↭-trans p↭ refl ≡ p↭
↭-trans∘reflʳ = λ where
  refl → refl
  (prep _ _) → refl
  (swap _ _ _) → refl
  (↭-trans _ _) → refl

↭-sym∘↭-reflexive :
  (eq : xs ≡ ys)
  --————————————————————————————————————————————————
  → ↭-sym (↭-reflexive eq) -- Any P ys
  ≡ ↭-reflexive (sym eq)   -- Any P xs
↭-sym∘↭-reflexive refl = refl

IsRefl : Pred₀ (xs ↭ ys)
IsRefl = λ where
  refl → ⊤
  _    → ⊥

IsRefl? : Decidable¹ (IsRefl {xs = xs}{ys})
IsRefl? = λ where
  refl → yes tt
  (↭-prep _ _) → no λ ()
  (swap _ _ _) → no λ ()
  (↭-trans _ _) → no λ ()

↭-trans≗trans : ∀ (p : xs ↭ ys) (q : ys ↭ zs) →
  ∙ ¬ IsRefl p
  ∙ ¬ IsRefl q
    ────────────────────
      L.Perm.↭-trans p q
    ≡ _↭_.trans p q
↭-trans≗trans refl _ p≢ _ = ⊥-elim (p≢ tt)
↭-trans≗trans _ refl _ q≢ = ⊥-elim (q≢ tt)
↭-trans≗trans (prep _ _) (↭-prep _ _) _ _ = refl
↭-trans≗trans (prep _ _) (swap _ _ _) _ _ = refl
↭-trans≗trans (prep _ _) (↭-trans _ _) _ _ = refl
↭-trans≗trans (swap _ _ p) (↭-prep _ _) _ _ = refl
↭-trans≗trans (swap _ _ p) (swap _ _ _) _ _ = refl
↭-trans≗trans (swap _ _ p) (↭-trans _ _) _ _ = refl
↭-trans≗trans (↭-trans _ _) (prep _ _) _ _ = refl
↭-trans≗trans (↭-trans _ _) (swap _ _ _) _ _ = refl
↭-trans≗trans (↭-trans _ _) (↭-trans _ _) _ _ = refl

Any-resp-↭∘Any-map : ∀ {P : Pred A ℓ} {Q : Pred A ℓ′}
  (f : P ⊆¹ Q)
  (xs↭ : xs ↭ ys)
  (x∈ : Any P xs) →
  --————————————————————————————————————————————————
    ( Any-resp-↭ xs↭ -- Any Q ys
    ∘ L.Any.map f    -- Any Q xs
    ) x∈             -- Any P xs
  ≡ ( L.Any.map f    -- Any Q ys
    ∘ Any-resp-↭ xs↭ -- Any P ys
    ) x∈             -- Any P xs
Any-resp-↭∘Any-map f xs↭ x∈
  with xs↭         | x∈
... | refl         | _                = refl
... | prep _ xs↭   | here _           = refl
... | prep _ xs↭   | there x∈         = cong there $ Any-resp-↭∘Any-map f xs↭ x∈
... | swap _ _ xs↭ | here _           = refl
... | swap _ _ xs↭ | there (here _)   = refl
... | swap _ _ xs↭ | there (there x∈) = cong (there ∘′ there) $ Any-resp-↭∘Any-map f xs↭ x∈
... | ↭-trans p q  | x∈
  rewrite Any-resp-↭∘Any-map f p x∈
  = Any-resp-↭∘Any-map f q (Any-resp-↭ p x∈)

Any-map∘∈-resp-↭ : ∀ {A : Type} {x y : A} {xs ys : List A}
  (f : (x ≡_) ⊆¹ (y ≡_))
  (p : xs ↭ ys)
  (x∈ : x ∈ xs)
  --—————————————————————
  → ( L.Any.map f -- y ∈ ys
    ∘ ∈-resp-↭ p  -- x ∈ ys
    ) x∈          -- x ∈ xs
  ≡ ( ∈-resp-↭ p  -- y ∈ ys
    ∘ L.Any.map f -- y ∈ xs
    ) x∈          -- x ∈ xs
Any-map∘∈-resp-↭ _ refl _ = refl
Any-map∘∈-resp-↭ f (↭-trans p p′) x∈
  rewrite sym $ Any-map∘∈-resp-↭ f p x∈
        | sym $ Any-map∘∈-resp-↭ f p′ (∈-resp-↭ p x∈)
        = refl
Any-map∘∈-resp-↭ f (prep x p) x∈ with x∈
... | here _ = refl
... | there x∈ = cong there $ Any-map∘∈-resp-↭ f p x∈
Any-map∘∈-resp-↭ f (swap x y p) x∈ with x∈
... | here _ = refl
... | there (here _) = refl
... | there (there x∈) = cong there $ cong there $ Any-map∘∈-resp-↭ f p x∈

module _ {P : Pred A ℓ} where

  find∘Any-resp-↭ :
    (p : xs ↭ ys)
    (x∈ : Any P xs)
    --—————————————————————
    → ( find         -- ∃x. x ∈ ys × P x
      ∘ Any-resp-↭ p -- Any P ys
      ) x∈           -- Any P xs
    ≡ ( map₂′ (map₁ $ Any-resp-↭ p) -- ∃x. x ∈ ys × P x
      ∘ find                        -- ∃x. x ∈ xs × P x
      ) x∈                          -- Any P xs
  find∘Any-resp-↭ refl x∈ = refl
  find∘Any-resp-↭ (prep x p) x∈ with x∈
  ... | here _ = refl
  ... | there x∈ rewrite find∘Any-resp-↭ p x∈ = refl
  find∘Any-resp-↭ (swap x y p) x∈ with x∈
  ... | here _ = refl
  ... | there (here _) = refl
  ... | there (there x∈) rewrite find∘Any-resp-↭ p x∈ = refl
  find∘Any-resp-↭ (↭-trans p p′) x∈
    rewrite find∘Any-resp-↭ p′ (Any-resp-↭ p x∈)
          | find∘Any-resp-↭ p x∈
          = refl

  -- ** ++

  Any-resp-↭∘Any-++⁺ʳˡ :
    (xs↭ : xs ↭ ys)
    (x∈ : Any P xs) →
    --—————————————————————————————————————————————————————
      ( Any-resp-↭ (++⁺ʳ zs xs↭) -- Any P (ys ++ zs)
      ∘ L.Any.++⁺ˡ               -- Any P (xs ++ zs)
      ) x∈                       -- Any P xs
    ≡ ( L.Any.++⁺ˡ     -- Any P (ys ++ zs)
      ∘ Any-resp-↭ xs↭ -- Any P ys
      ) x∈             -- Any P xs
  Any-resp-↭∘Any-++⁺ʳˡ {zs = zs} xs↭ x∈
    with xs↭            | x∈
  ... | refl            | _                = refl
  ... | ↭-prep _ xss↭   | here _           = refl
  ... | ↭-prep _ xss↭   | there x∈         = cong there $ Any-resp-↭∘Any-++⁺ʳˡ xss↭ x∈
  ... | swap _ _ xss↭ | here _           = refl
  ... | swap _ _ xss↭ | there (here _)   = refl
  ... | swap _ _ xss↭ | there (there x∈) = cong (there ∘′ there) $ Any-resp-↭∘Any-++⁺ʳˡ xss↭ x∈
  ... | ↭-trans p q   | x∈
    rewrite Any-resp-↭∘Any-++⁺ʳˡ {zs = zs} p x∈
    = Any-resp-↭∘Any-++⁺ʳˡ {zs = zs} q (Any-resp-↭ p x∈)

  Any-resp-↭∘Any-++⁺ˡʳ :
    (xs↭ : xs ↭ ys)
    (x∈ : Any P xs) →
    --————————————————————————————————————————————————
      ( Any-resp-↭ (++⁺ˡ zs xs↭) -- Any P (zs ++ ys)
      ∘ L.Any.++⁺ʳ zs            -- Any P (zs ++ xs)
      ) x∈                       -- Any P xs
    ≡ ( L.Any.++⁺ʳ zs  -- Any P (zs ++ ys)
      ∘ Any-resp-↭ xs↭ -- Any P ys
      ) x∈             -- Any P xs
  Any-resp-↭∘Any-++⁺ˡʳ {zs = zs} xs↭ x∈ with zs
  ... | []     = refl
  ... | _ ∷ zs rewrite Any-resp-↭∘Any-++⁺ˡʳ {zs = zs} xs↭ x∈ = refl

  Any-resp-↭∘Any-++⁺ˡˡ :
    (xs↭ : xs ↭ ys)
    (x∈ : Any P zs) →
    --—————————————————————————————————
      ( Any-resp-↭ (++⁺ˡ zs xs↭)
      ∘ L.Any.++⁺ˡ
      ) x∈
    ≡ L.Any.++⁺ˡ x∈
  Any-resp-↭∘Any-++⁺ˡˡ xs↭ = λ where
    (here _)   → refl
    (there x∈) → cong there (Any-resp-↭∘Any-++⁺ˡˡ xs↭ x∈)

  Any-resp-↭∘Any-++⁺ʳʳ :
    (xs↭ : xs ↭ ys)
    (x∈ : Any P zs) →
    --————————————————————————————————————————————————
      ( Any-resp-↭ (++⁺ʳ zs xs↭) -- Any P (ys ++ zs)
      ∘ L.Any.++⁺ʳ xs            -- Any P (xs ++ zs)
      ) x∈                       -- Any P zs
    ≡ L.Any.++⁺ʳ ys  -- Any P (ys ++ zs)
      x∈             -- Any P zs
  Any-resp-↭∘Any-++⁺ʳʳ refl             = λ _ → refl
  Any-resp-↭∘Any-++⁺ʳʳ (↭-prep _ xs↭)   = cong there ∘ Any-resp-↭∘Any-++⁺ʳʳ xs↭
  Any-resp-↭∘Any-++⁺ʳʳ (swap _ _ xs↭) = cong there ∘ cong there ∘ Any-resp-↭∘Any-++⁺ʳʳ xs↭
  Any-resp-↭∘Any-++⁺ʳʳ (↭-trans xs↭ ↭ys) x∈
    rewrite Any-resp-↭∘Any-++⁺ʳʳ xs↭ x∈ = Any-resp-↭∘Any-++⁺ʳʳ ↭ys x∈

  Any-++⁺ˡ∘here :
    (px : P x)
    --————————————————————————————————————————————————
    → ( L.Any.++⁺ˡ {ys = ys}   -- Any P (x ∷ xs ++ ys)
      ∘ here {P = P} {xs = xs} -- Any P (x ∷ xs)
      ) px                     -- P x
    ≡ here {x = x} -- Any P (x ∷ xs ++ ys)
      px           -- P x
  Any-++⁺ˡ∘here _ = refl

  Any-++⁺ˡ∘there :
    (x∈ : Any P xs)
    --————————————————————————————————————————————————
    → ( L.Any.++⁺ˡ {ys = ys} -- Any P (x ∷ xs ++ ys)
      ∘ there {x = x}        -- Any P (x ∷ xs)
      ) x∈                   -- Any P xs
    ≡ ( there {x = x} -- Any P (x ∷ xs ++ ys)
      ∘ L.Any.++⁺ˡ    -- Any P (xs ++ ys)
      ) x∈            -- Any P xs
  Any-++⁺ˡ∘there _ = refl

  Any-resp-↭-prep∘here :
    (xs↭ : xs ↭ ys)
    (px : P x)
    --————————————————————————————————————————————————
    → Any-resp-↭ (prep x xs↭) -- Any P (x ∷ ys)
      (here {P = P} px)       -- Any P (x ∷ xs)
    ≡ here px -- Any P (x ∷ ys)
  Any-resp-↭-prep∘here _ _ = refl

  Any-resp-↭-prep∘there :
    (xs↭ : xs ↭ ys)
    (x∈ : Any P xs)
    --————————————————————————————————————————————————
    → ( Any-resp-↭ (prep x xs↭) -- Any P (x ∷ ys)
      ∘ there                   -- Any P (x ∷ xs)
      ) x∈                      -- Any P xs
    ≡ ( there          -- Any P (x ∷ ys)
      ∘ Any-resp-↭ xs↭ -- Any P ys
      ) x∈             -- Any P xs
  Any-resp-↭-prep∘there _ _ = refl

  Any-resp-↭∘˘shift∘here :
    (px : P x)
    --————————————————————————————————————————————————
    → ( Any-resp-↭ (↭-sym $ shift x ys xs) -- Any P (ys ++ x ∷ xs)
      ) (here {P = P} px)                  -- Any P (x ∷ ys ++ xs)
    ≡ L.Any.++⁺ʳ ys -- Any P (ys ++ x ∷ xs)
      (here px)     -- Any P (x ∷ xs)
  Any-resp-↭∘˘shift∘here {ys = []}    _  = refl
  Any-resp-↭∘˘shift∘here {ys = _ ∷ _} px = cong there $ Any-resp-↭∘˘shift∘here px

  Any-resp-↭∘˘shift∘++⁺ˡ∘there :
    (x∈ : Any P xs)
    --————————————————————————————————————
    → ( Any-resp-↭ (↭-sym $ shift y xs ys) -- Any P (xs ++ y ∷ ys)
      ∘ L.Any.++⁺ˡ                         -- Any P (y ∷ xs ++ ys)
      ∘ there                              -- Any P (y ∷ xs)
      ) x∈                                 -- Any P xs
    ≡ L.Any.++⁺ˡ -- Any P (xs ++ y ∷ ys)
      x∈         -- Any P xs
  Any-resp-↭∘˘shift∘++⁺ˡ∘there {x ∷ xs} = λ where
    (here _)   → refl
    (there x∈) → cong there $ Any-resp-↭∘˘shift∘++⁺ˡ∘there x∈

  Any-resp-↭∘˘shift∘++⁺ʳ :
    (x∈ : Any P xs)
    --————————————————————————————————————————————————
    → ( Any-resp-↭ (↭-sym $ shift x ys xs) -- Any P (ys ++ x ∷ xs)
      ∘ L.Any.++⁺ʳ (x ∷ ys)                -- Any P (x ∷ ys ++ xs)
      ) x∈                                 -- Any P xs
    ≡ ( L.Any.++⁺ʳ ys -- Any P (ys ++ x ∷ xs)
      ∘ there         -- Any P (x ∷ xs)
      ) x∈            -- Any P xs
  Any-resp-↭∘˘shift∘++⁺ʳ {ys = []}    _  = refl
  Any-resp-↭∘˘shift∘++⁺ʳ {ys = _ ∷ _} px = cong there (Any-resp-↭∘˘shift∘++⁺ʳ px)

  -- ** trans

  Any-resp-↭∘↭-trans :
    ∀ (x∈ : Any P xs) (p : xs ↭ ys) (q : ys ↭ zs)
    --———————————————————————————————————————————
    → Any-resp-↭ (L.Perm.↭-trans p q) x∈
    ≡ Any-resp-↭ q (Any-resp-↭ p x∈)
  Any-resp-↭∘↭-trans {xs = xs}{ys} x∈ p q
    with p   | IsRefl? p
  ... | refl | yes tt = refl
  ... | p    | no p≢
    with q   | IsRefl? q
  ... | refl | yes tt rewrite ↭-trans∘reflʳ p = refl
  ... | q    | no  q≢ rewrite ↭-trans≗trans p q p≢ q≢ = refl

  -- ** reflexive

  Any-resp-↭∘↭-reflexive :
    (x∈ : Any P xs)
    (eq : xs ≡ ys)
    --————————————————————————————————————————————————
    → Any-resp-↭ (↭-reflexive eq) -- Any P ys
      x∈                          -- Any P xs
    ≡ subst (Any P) eq -- Any P ys
      x∈               -- Any P xs
  Any-resp-↭∘↭-reflexive _ refl = refl

  Any-resp-↭∘↭-reflexive∘here :
    (px : P x)
    (eq : xs ≡ ys)
    --————————————————————————————————————————————————
    → ( Any-resp-↭ (↭-reflexive (cong (x ∷_) eq)) -- Any P (x ∷ ys)
      ∘ here {P = P}                              -- Any P (x ∷ xs)
      ) px                                        -- P x
    ≡ here -- Any P (x ∷ ys)
      px   -- P x
  Any-resp-↭∘↭-reflexive∘here _ refl = refl

  Any-resp-↭∘↭-reflexive∘there :
    (x∈ : Any P xs)
    (eq : xs ≡ ys)
    --————————————————————————————————————————————————
    → ( Any-resp-↭ (↭-reflexive (cong (x ∷_) eq)) -- Any P (x ∷ ys)
      ∘ there                                     -- Any P (x ∷ xs)
      ) x∈                                        -- Any P xs
    ≡ ( there                       -- Any P (x ∷ ys)
      ∘ Any-resp-↭ (↭-reflexive eq) -- Any P ys
      ) x∈                          -- Any P xs
  Any-resp-↭∘↭-reflexive∘there _ refl = refl

  Any-resp-↭∘↭-reflexive∘++-identityʳ :
    (x∈ : Any P xs)
    --————————————————————————————————————————————————
    → Any-resp-↭ (↭-reflexive $ sym $ L.++-identityʳ xs) x∈
    ≡ L.Any.++⁺ˡ x∈
  Any-resp-↭∘↭-reflexive∘++-identityʳ {xs = x ∷ xs} x∈
    with x∈
  ... | here px
    rewrite sym∘cong (x L.∷_) (L.++-identityʳ xs)
          = Any-resp-↭∘↭-reflexive∘here px (sym $ L.++-identityʳ xs)
  ... | there x∈
    rewrite sym∘cong (x L.∷_) (L.++-identityʳ xs)
          | Any-resp-↭∘↭-reflexive∘there {x = x} x∈ (sym $ L.++-identityʳ xs)
          = cong there (Any-resp-↭∘↭-reflexive∘++-identityʳ x∈)

  -- ** assoc

  Any-resp-↭∘++-assocˡˡ :
    (x∈ : Any P xs)
    --————————————————————————————————————————————————
    → ( Any-resp-↭ (++-assoc xs ys zs) -- Any P (xs ++ ys ++ zs)
      ∘ L.Any.++⁺ˡ                     -- Any P ((xs ++ ys) ++ zs)
      ∘ L.Any.++⁺ˡ                     -- Any P (xs ++ ys)
      ) x∈                             -- Any P xs
    ≡ ( L.Any.++⁺ˡ -- Any P (xs ++ ys ++ zs)
      ) x∈         -- Any P xs
  Any-resp-↭∘++-assocˡˡ {xs = x ∷ xs} {ys} {zs} (here px)
    rewrite L.++-assoc xs ys zs
    = refl
  Any-resp-↭∘++-assocˡˡ {xs = x ∷ xs} {ys} {zs} (there x∈)
    with IH ← Any-resp-↭∘++-assocˡˡ {xs = xs} {ys} {zs} x∈
    = trans (Any-resp-↭∘↭-reflexive∘there (L.Any.++⁺ˡ $ L.Any.++⁺ˡ x∈) (L.++-assoc xs ys zs))
            (cong there IH)

  Any-resp-↭∘++-assocˡʳ :
    (x∈ : Any P xs)
    --————————————————————————————————————————————————
    → ( Any-resp-↭ (++-assoc ys xs zs) -- Any P (ys ++ xs ++ zs)
      ∘ L.Any.++⁺ˡ                     -- Any P ((ys ++ xs) ++ zs)
      ∘ L.Any.++⁺ʳ ys                  -- Any P (ys ++ xs)
      ) x∈                             -- Any P xs
    ≡ ( L.Any.++⁺ʳ ys -- Any P (ys ++ xs ++ zs)
      ∘ L.Any.++⁺ˡ    -- Any P (xs ++ zs)
      ) x∈            -- Any P xs
  Any-resp-↭∘++-assocˡʳ {ys = []} _ = refl
  Any-resp-↭∘++-assocˡʳ {xs = xs} {y ∷ ys} {zs} x∈
    = begin
      ( Any-resp-↭ (++-assoc (y ∷ ys) xs zs) -- Any P (y ∷ ys ++ xs ++ zs)
      ∘ L.Any.++⁺ˡ {ys = zs}                 -- Any P ((y ∷ ys ++ xs) ++ zs)
      ∘ there                                -- Any P (y ∷ ys ++ xs)
      ∘ L.Any.++⁺ʳ ys                        -- Any P (ys ++ xs)
      ) x∈                                   -- Any P xs
    ≡⟨ Any-resp-↭∘↭-reflexive∘there (L.Any.++⁺ˡ {ys = zs} $ L.Any.++⁺ʳ ys x∈) (L.++-assoc ys xs zs) ⟩
      ( there                          -- Any P (y ∷ ys ++ xs ++ zs)
      ∘ Any-resp-↭ (++-assoc ys xs zs) -- Any P (ys ++ xs ++ zs)
      ∘ L.Any.++⁺ˡ {ys = zs}           -- Any P ((ys ++ xs) ++ zs)
      ∘ L.Any.++⁺ʳ ys                  -- Any P (ys ++ xs)
      ) x∈                             -- Any P xs
    ≡⟨ cong there $ Any-resp-↭∘++-assocˡʳ {ys = ys} x∈ ⟩
      ( there         -- Any P (y ∷ ys ++ xs ++ zs)
      ∘ L.Any.++⁺ʳ ys -- Any P (ys ++ xs ++ zs)
      ∘ L.Any.++⁺ˡ    -- Any P (xs ++ zs)
      ) x∈            -- Any P xs
    ∎

  Any-resp-↭∘˘++-assocˡ :
    (x∈ : Any P xs)
    --————————————————————————————————————————————————
    → ( Any-resp-↭ (↭-sym $ ++-assoc xs ys zs) -- Any P ((xs ++ ys) ++ zs)
      ∘ L.Any.++⁺ˡ                             -- Any P (xs ++ ys ++ zs)
      ) x∈                                     -- Any P xs
    ≡ ( L.Any.++⁺ˡ -- Any P ((xs ++ ys) ++ zs)
      ∘ L.Any.++⁺ˡ -- Any P (xs ++ ys)
      ) x∈         -- Any P xs
  Any-resp-↭∘˘++-assocˡ {xs = x ∷ xs} {ys} {zs} x∈
    with x∈
  ... | here px
    rewrite L.++-assoc xs ys zs = refl
  ... | there x∈
    with IH ← Any-resp-↭∘˘++-assocˡ {xs = xs} {ys} {zs} x∈
    rewrite ↭-sym∘↭-reflexive (cong (x ∷_) (L.++-assoc xs ys zs))
          | ↭-sym∘↭-reflexive (L.++-assoc xs ys zs)
          | sym∘cong (x L.∷_) (L.++-assoc xs ys zs)
          | Any-resp-↭∘↭-reflexive∘there {x = x} (L.Any.++⁺ˡ {ys = ys ++ zs} x∈)
                                     (sym (L.++-assoc xs ys zs))
    = cong there IH

  Any-resp-↭∘˘++-assocʳˡ :
    (x∈ : Any P xs)
    --————————————————————————————————————————————————
    → ( Any-resp-↭ (↭-sym $ ++-assoc ys xs zs) -- Any P ((ys ++ xs) ++ zs)
      ∘ L.Any.++⁺ʳ ys                          -- Any P (ys ++ xs ++ zs)
      ∘ L.Any.++⁺ˡ                             -- Any P (xs ++ zs)
      ) x∈                                     -- Any P xs
    ≡ ( L.Any.++⁺ˡ    -- Any P ((ys ++ xs) ++ zs)
      ∘ L.Any.++⁺ʳ ys -- Any P (ys ++ xs)
      ) x∈            -- Any P xs
  Any-resp-↭∘˘++-assocʳˡ {ys = []} _ = refl
  Any-resp-↭∘˘++-assocʳˡ {xs = xs}{y ∷ ys}{zs} x∈
    rewrite ↭-sym∘↭-reflexive (cong (y ∷_) (L.++-assoc ys xs zs))
          | sym∘cong (y L.∷_) (L.++-assoc ys xs zs)
          | Any-resp-↭∘↭-reflexive∘there {x = y} (L.Any.++⁺ʳ ys $ L.Any.++⁺ˡ x∈) (sym $ L.++-assoc ys xs zs)
          | sym $ ↭-sym∘↭-reflexive (L.++-assoc ys xs zs)
    = cong there $ Any-resp-↭∘˘++-assocʳˡ {ys = ys} x∈

  Any-resp-↭∘++-assocʳ :
    (x∈ : Any P zs)
    --————————————————————————————————————————————————
    → ( Any-resp-↭ (++-assoc xs ys zs) -- Any P (xs ++ ys ++ zs)
      ∘ L.Any.++⁺ʳ (xs ++ ys)          -- Any P ((xs ++ ys) ++ zs)
      ) x∈                             -- Any P xs
    ≡ ( L.Any.++⁺ʳ xs -- Any P (xs ++ ys ++ zs)
      ∘ L.Any.++⁺ʳ ys -- Any P (ys ++ zs)
      ) x∈            -- Any P zs
  Any-resp-↭∘++-assocʳ {xs = []} _ = refl
  Any-resp-↭∘++-assocʳ {zs = zs}{x ∷ xs}{ys} x∈
    rewrite Any-resp-↭∘↭-reflexive∘there {x = x} (L.Any.++⁺ʳ (xs ++ ys) x∈)
                                                 (L.++-assoc xs ys zs)
    = cong there $ Any-resp-↭∘++-assocʳ {zs = zs}{xs}{ys} x∈

  Any-resp-↭∘˘++-assocʳʳ :
    (x∈ : Any P zs)
    --————————————————————————————————————————————————
    → ( Any-resp-↭ (↭-sym $ ++-assoc xs ys zs) -- Any P ((xs ++ ys) ++ zs)
      ∘ L.Any.++⁺ʳ xs                          -- Any P (xs ++ ys ++ zs)
      ∘ L.Any.++⁺ʳ ys                          -- Any P (ys ++ zs)
      ) x∈                                     -- Any P xs
    ≡ ( L.Any.++⁺ʳ (xs ++ ys) -- Any P ((xs ++ ys) ++ zs)
      ) x∈                    -- Any P zs
  Any-resp-↭∘˘++-assocʳʳ {xs = []} _ = refl
  Any-resp-↭∘˘++-assocʳʳ {zs = zs}{x ∷ xs}{ys} x∈
    rewrite ↭-sym∘↭-reflexive (cong (x ∷_) (L.++-assoc xs ys zs))
          | sym∘cong (x L.∷_) (L.++-assoc xs ys zs)
          | Any-resp-↭∘↭-reflexive∘there {x = x}
              (L.Any.++⁺ʳ xs $ L.Any.++⁺ʳ ys x∈) (sym $ L.++-assoc xs ys zs)
          | sym $ ↭-sym∘↭-reflexive (L.++-assoc xs ys zs)
    = cong there $ Any-resp-↭∘˘++-assocʳʳ {zs = zs}{xs}{ys} x∈

  -- ** comm
  -- T0D0: comment out postulates when my fix of `++-comm` is released in the next `stdlib` version

  postulate
    Any-resp-↭∘++-commˡ :
      (x∈ : Any P xs)
      --————————————————————————————————————————————————
      → ( Any-resp-↭ (++-comm xs ys) -- Any P (ys ++ xs)
        ∘ L.Any.++⁺ˡ                  -- Any P (xs ++ ys)
        ) x∈                          -- Any P xs
      ≡ L.Any.++⁺ʳ ys -- Any P (ys ++ xs)
        x∈            -- Any P xs
{-
  Any-resp-↭∘++-commˡ {x ∷ xs}{ys} x∈
    rewrite ↭-trans∘reflʳ (↭-sym $ shift x ys xs)
          | Any-resp-↭∘↭-trans (L.Any.++⁺ˡ x∈) (prep x $ ++-comm xs ys) (↭-sym $ shift x ys xs)
    with x∈
  ... | here px
    = begin
      ( Any-resp-↭ (↭-sym $ shift x ys xs)   -- Any P (ys ++ x ∷ xs)
      ∘ Any-resp-↭ (prep x $ ++-comm xs ys) -- Any P (x ∷ ys ++ xs)
      ∘ L.Any.++⁺ˡ {ys = ys}                 -- Any P (x ∷ xs ++ ys)
      ) (here px)                            -- Any P (x ∷ xs)
    ≡⟨ cong (Any-resp-↭ (↭-sym $ shift x ys xs) ∘ Any-resp-↭ (prep x $ ++-comm xs ys))
          $ Any-++⁺ˡ∘here {xs = xs} px ⟩
      ( Any-resp-↭ (↭-sym $ shift x ys xs)   -- Any P (ys ++ x ∷ xs)
      ∘ Any-resp-↭ (prep x $ ++-comm xs ys) -- Any P (x ∷ ys ++ xs)
      ) (here px)                            -- Any P (x ∷ xs ++ ys)
    ≡⟨ cong (Any-resp-↭ (↭-sym $ shift x ys xs)) $ Any-resp-↭-prep∘here (++-comm xs ys) px ⟩
      ( Any-resp-↭ (↭-sym $ shift x ys xs)   -- Any P (ys ++ x ∷ xs)
      ) (here px)                            -- Any P (x ∷ ys ++ xs)
    ≡⟨ Any-resp-↭∘˘shift∘here px ⟩
      L.Any.++⁺ʳ ys -- Any P (ys ++ x ∷ xs)
      (here px)     -- Any P (x ∷ xs)
    ∎
  ... | there x∈
    = begin
      ( Any-resp-↭ (↭-sym $ shift x ys xs)   -- Any P (ys ++ x ∷ xs)
      ∘ Any-resp-↭ (prep x $ ++-comm xs ys) -- Any P (x ∷ ys ++ xs)
      ∘ L.Any.++⁺ˡ                           -- Any P (x ∷ xs ++ ys)
      ∘ there                                -- Any P (x ∷ xs)
      ) x∈                                   -- Any P xs
    ≡⟨⟩
      ( Any-resp-↭ (↭-sym $ shift x ys xs)   -- Any P (ys ++ x ∷ xs)
      ∘ Any-resp-↭ (prep x $ ++-comm xs ys) -- Any P (x ∷ ys ++ xs)
      ∘ there                                -- Any P (x ∷ xs ++ ys)
      ∘ L.Any.++⁺ˡ                           -- Any P (xs ++ ys)
      ) x∈                                   -- Any P xs
    ≡⟨⟩
      ( Any-resp-↭ (↭-sym $ shift x ys xs) -- Any P (ys ++ x ∷ xs)
      ∘ there                              -- Any P (x ∷ ys ++ xs)
      ∘ Any-resp-↭ (++-comm xs ys)        -- Any P (ys ++ xs)
      ∘ L.Any.++⁺ˡ                         -- Any P (xs ++ ys)
      ) x∈                                 -- Any P xs
    ≡⟨ cong (Any-resp-↭ (↭-sym $ shift x ys xs) ∘ there) $ Any-resp-↭∘++-commˡ x∈ ⟩
      ( Any-resp-↭ (↭-sym $ shift x ys xs) -- Any P (ys ++ x ∷ xs)
      ∘ there                              -- Any P (x ∷ ys ++ xs)
      ∘ L.Any.++⁺ʳ ys                      -- Any P (ys ++ xs)
      ) x∈                                 -- Any P xs
    ≡⟨⟩
      ( Any-resp-↭ (↭-sym $ shift x ys xs) -- Any P (ys ++ x ∷ xs)
      ∘ L.Any.++⁺ʳ (x ∷ ys)                -- Any P (x ∷ ys ++ xs)
      ) x∈                                 -- Any P xs
    ≡⟨ Any-resp-↭∘˘shift∘++⁺ʳ x∈ ⟩
      ( L.Any.++⁺ʳ ys -- Any P (ys ++ x ∷ xs)
      ∘ there         -- Any P (x ∷ xs)
      ) x∈            -- Any P xs
    ∎
-}

    Any-resp-↭∘++-commʳ :
      (x∈ : Any P xs)
      --————————————————————————————————————————————————
      → ( Any-resp-↭ (++-comm ys xs) -- Any P (xs ++ ys)
        ∘ L.Any.++⁺ʳ ys               -- Any P (ys ++ xs)
        ) x∈                          -- Any P xs
      ≡ L.Any.++⁺ˡ -- Any P (xs ++ ys)
        x∈         -- Any P xs
{-
  Any-resp-↭∘++-commʳ {xs}{[]} x∈
    rewrite ↭-sym∘↭-reflexive (L.++-identityʳ xs)
    = Any-resp-↭∘↭-reflexive∘++-identityʳ x∈
  Any-resp-↭∘++-commʳ {xs}{y ∷ ys} x∈
    rewrite ↭-trans∘reflʳ (↭-sym $ shift y xs ys)
          | Any-resp-↭∘↭-trans (L.Any.++⁺ʳ (y ∷ ys) x∈) (prep y $ ++-comm ys xs) (↭-sym $ shift y xs ys)
    = begin
      ( Any-resp-↭ (↭-sym $ shift y xs ys)   -- Any P (xs ++ y ∷ ys)
      ∘ Any-resp-↭ (prep y $ ++-comm ys xs) -- Any P (y ∷ xs ++ ys)
      ∘ L.Any.++⁺ʳ (y ∷ ys)                  -- Any P (y ∷ ys ++ xs)
      ) x∈                                   -- Any P xs
    ≡⟨⟩
      ( Any-resp-↭ (↭-sym $ shift y xs ys)   -- Any P (xs ++ y ∷ ys)
      ∘ Any-resp-↭ (prep y $ ++-comm ys xs) -- Any P (y ∷ xs ++ ys)
      ∘ there                                -- Any P (y ∷ ys ++ xs)
      ∘ L.Any.++⁺ʳ ys                        -- Any P (ys ++ xs)
      ) x∈                                   -- Any P xs
    ≡⟨⟩
      ( Any-resp-↭ (↭-sym $ shift y xs ys) -- Any P (xs ++ y ∷ ys)
      ∘ there                              -- Any P (y ∷ xs ++ ys)
      ∘ Any-resp-↭ (++-comm ys xs)        -- Any P (xs ++ ys)
      ∘ L.Any.++⁺ʳ ys                      -- Any P (ys ++ xs)
      ) x∈                                 -- Any P xs
    ≡⟨ cong (Any-resp-↭ (↭-sym $ shift y xs ys) ∘ there) $ Any-resp-↭∘++-commʳ x∈ ⟩
      ( Any-resp-↭ (↭-sym $ shift y xs ys) -- Any P (xs ++ y ∷ ys)
      ∘ there                              -- Any P (y ∷ xs ++ ys)
      ∘ L.Any.++⁺ˡ                         -- Any P (xs ++ ys)
      ) x∈                                 -- Any P xs
    ≡⟨⟩
      ( Any-resp-↭ (↭-sym $ shift y xs ys) -- Any P (xs ++ y ∷ ys)
      ∘ L.Any.++⁺ˡ                         -- Any P (y ∷ xs ++ ys)
      ∘ there                              -- Any P (y ∷ xs)
      ) x∈                                 -- Any P xs
    ≡⟨ Any-resp-↭∘˘shift∘++⁺ˡ∘there x∈ ⟩
      L.Any.++⁺ˡ -- Any P (xs ++ y ∷ ys)
      x∈         -- Any P xs
    ∎
-}

  -- ** shifts
  Any-resp-↭∘shifts : ∀ xs ys zs →
    (x∈ : Any P (xs ++ ys ++ zs))
    --————————————————————————————————————————————————
    → Any-resp-↭ (shifts xs ys {zs}) x∈
    ≡ ( Any-resp-↭ (++-assoc ys xs zs)
      ∘ Any-resp-↭ (++⁺ʳ zs $ ++-comm xs ys)
      ∘ Any-resp-↭ (↭-sym $ ++-assoc xs ys zs)
      ) x∈
  Any-resp-↭∘shifts xs ys zs x∈
    rewrite ↭-trans∘reflʳ (++-assoc ys xs zs)
    rewrite Any-resp-↭∘↭-trans x∈
                               (↭-sym $ ++-assoc xs ys zs)
                               (L.Perm.↭-trans (++⁺ʳ zs $ ++-comm xs ys) (++-assoc ys xs zs))
    rewrite Any-resp-↭∘↭-trans (Any-resp-↭ (↭-sym $ ++-assoc xs ys zs) x∈)
                               (++⁺ʳ zs $ ++-comm xs ys)
                               (++-assoc ys xs zs)
    = refl

  Any-resp-↭∘shiftsˡ :
    (x∈ : Any P xs)
    --————————————————————————————————————————————————
    → ( Any-resp-↭ (shifts xs ys {zs}) -- Any P (ys ++ xs ++ zs)
      ∘ L.Any.++⁺ˡ                     -- Any P (xs ++ ys ++ zs)
      ) x∈                             -- Any P xs
    ≡ ( L.Any.++⁺ʳ ys -- Any P (ys ++ xs ++ zs)
      ∘ L.Any.++⁺ˡ    -- Any P (xs ++ zs)
      ) x∈            -- Any P xs
  Any-resp-↭∘shiftsˡ {xs}{ys}{zs} x∈
    rewrite Any-resp-↭∘shifts xs ys zs (L.Any.++⁺ˡ x∈)
    = begin
      ( Any-resp-↭ (++-assoc ys xs zs)         -- Any P (ys ++ xs ++ zs)
      ∘ Any-resp-↭ (++⁺ʳ zs $ ++-comm xs ys)   -- Any P ((ys ++ xs) ++ zs)
      ∘ Any-resp-↭ (↭-sym $ ++-assoc xs ys zs) -- Any P ((xs ++ ys) ++ zs)
      ∘ L.Any.++⁺ˡ                             -- Any P (xs ++ ys ++ zs)
      ) x∈                                     -- Any P xs
    ≡⟨ cong (Any-resp-↭ (++-assoc ys xs zs) ∘ Any-resp-↭ (++⁺ʳ zs $ ++-comm xs ys)) $ Any-resp-↭∘˘++-assocˡ x∈ ⟩
      ( Any-resp-↭ (++-assoc ys xs zs)       -- Any P (ys ++ xs ++ zs)
      ∘ Any-resp-↭ (++⁺ʳ zs $ ++-comm xs ys) -- Any P ((ys ++ xs) ++ zs)
      ∘ L.Any.++⁺ˡ                           -- Any P ((xs ++ ys) ++ zs)
      ∘ L.Any.++⁺ˡ                           -- Any P (xs ++ ys)
      ) x∈                                   -- Any P xs
    ≡⟨ cong (Any-resp-↭ (++-assoc ys xs zs)) $ Any-resp-↭∘Any-++⁺ʳˡ (++-comm xs ys) (L.Any.++⁺ˡ x∈) ⟩
      ( Any-resp-↭ (++-assoc ys xs zs) -- Any P (ys ++ xs ++ zs)
      ∘ L.Any.++⁺ˡ                     -- Any P ((ys ++ xs) ++ zs)
      ∘ Any-resp-↭ (++-comm xs ys)     -- Any P (ys ++ xs)
      ∘ L.Any.++⁺ˡ                     -- Any P (xs ++ ys)
      ) x∈                             -- Any P xs
    ≡⟨ cong (Any-resp-↭ (++-assoc ys xs zs) ∘ L.Any.++⁺ˡ) $′ Any-resp-↭∘++-commˡ {ys = ys} x∈ ⟩
      ( Any-resp-↭ (++-assoc ys xs zs) -- Any P (ys ++ xs ++ zs)
      ∘ L.Any.++⁺ˡ                     -- Any P ((ys ++ xs) ++ zs)
      ∘ L.Any.++⁺ʳ ys                  -- Any P (ys ++ xs)
      ) x∈                             -- Any P xs
    ≡⟨ Any-resp-↭∘++-assocˡʳ x∈ ⟩
      ( L.Any.++⁺ʳ ys
      ∘ L.Any.++⁺ˡ
      ) x∈
    ∎

  Any-resp-↭∘shiftsʳˡ :
    (x∈ : Any P xs)
    --————————————————————————————————————————————————
    → ( Any-resp-↭ (shifts ys xs {zs}) -- Any P (xs ++ ys ++ zs)
      ∘ L.Any.++⁺ʳ ys                  -- Any P (ys ++ xs ++ zs)
      ∘ L.Any.++⁺ˡ                     -- Any P (xs ++ zs)
      ) x∈                             -- Any P xs
    ≡ L.Any.++⁺ˡ x∈ -- Any P (xs ++ ys ++ zs)
  Any-resp-↭∘shiftsʳˡ {xs}{ys}{zs} x∈
    rewrite Any-resp-↭∘shifts ys xs zs (L.Any.++⁺ʳ ys $ L.Any.++⁺ˡ x∈)
    = begin
      ( Any-resp-↭ (++-assoc xs ys zs)         -- Any P (xs ++ ys ++ zs)
      ∘ Any-resp-↭ (++⁺ʳ zs $ ++-comm ys xs)   -- Any P ((xs ++ ys) ++ zs)
      ∘ Any-resp-↭ (↭-sym $ ++-assoc ys xs zs) -- Any P ((ys ++ xs) ++ zs)
      ∘ L.Any.++⁺ʳ ys                          -- Any P (ys ++ xs ++ zs)
      ∘ L.Any.++⁺ˡ                             -- Any P (xs ++ zs)
      ) x∈                                     -- Any P xs
    ≡⟨ cong (Any-resp-↭ (++-assoc xs ys zs) ∘ Any-resp-↭ (++⁺ʳ zs $ ++-comm ys xs)) $ Any-resp-↭∘˘++-assocʳˡ x∈ ⟩
      ( Any-resp-↭ (++-assoc xs ys zs)         -- Any P (xs ++ ys ++ zs)
      ∘ Any-resp-↭ (++⁺ʳ zs $ ++-comm ys xs)   -- Any P ((xs ++ ys) ++ zs)
      ∘ L.Any.++⁺ˡ                             -- Any P ((ys ++ xs) ++ zs)
      ∘ L.Any.++⁺ʳ ys                          -- Any P (ys ++ xs)
      ) x∈                                     -- Any P xs
    ≡⟨ cong (Any-resp-↭ (++-assoc xs ys zs)) $ Any-resp-↭∘Any-++⁺ʳˡ (++-comm ys xs) (L.Any.++⁺ʳ ys x∈) ⟩
      ( Any-resp-↭ (++-assoc xs ys zs) -- Any P (xs ++ ys ++ zs)
      ∘ L.Any.++⁺ˡ                     -- Any P ((xs ++ ys) ++ zs)
      ∘ Any-resp-↭ (++-comm ys xs)     -- Any P (xs ++ ys)
      ∘ L.Any.++⁺ʳ ys                  -- Any P (ys ++ xs)
      ) x∈                             -- Any P xs
    ≡⟨ cong (Any-resp-↭ (++-assoc xs ys zs) ∘ L.Any.++⁺ˡ) $ Any-resp-↭∘++-commʳ x∈ ⟩
      ( Any-resp-↭ (++-assoc xs ys zs) -- Any P (xs ++ ys ++ zs)
      ∘ L.Any.++⁺ˡ                     -- Any P ((xs ++ ys) ++ zs)
      ∘ L.Any.++⁺ˡ                     -- Any P (xs ++ ys)
      ) x∈                             -- Any P xs
    ≡⟨ Any-resp-↭∘++-assocˡˡ x∈ ⟩
      L.Any.++⁺ˡ x∈ -- Any P (xs ++ ys ++ zs)
    ∎

  Any-resp-↭∘shiftsʳʳ :
    (x∈ : Any P zs)
    --————————————————————————————————————————————————
    → ( Any-resp-↭ (shifts xs ys {zs}) -- Any P (ys ++ xs ++ zs)
      ∘ L.Any.++⁺ʳ xs                  -- Any P (xs ++ ys ++ zs)
      ∘ L.Any.++⁺ʳ ys                  -- Any P (ys ++ zs)
      ) x∈                             -- Any P zs
    ≡ ( L.Any.++⁺ʳ ys -- Any P (ys ++ xs ++ zs)
      ∘ L.Any.++⁺ʳ xs -- Any P (xs ++ zs)
      ) x∈            -- Any P zs
  Any-resp-↭∘shiftsʳʳ {zs}{xs}{ys} x∈
    rewrite Any-resp-↭∘shifts xs ys zs (L.Any.++⁺ʳ xs $ L.Any.++⁺ʳ ys x∈)
    = begin
      ( Any-resp-↭ (++-assoc ys xs zs)
      ∘ Any-resp-↭ (++⁺ʳ zs $ ++-comm xs ys)
      ∘ Any-resp-↭ (↭-sym $ ++-assoc xs ys zs)
      ∘ L.Any.++⁺ʳ xs
      ∘ L.Any.++⁺ʳ ys
      ) x∈
    ≡⟨ cong (Any-resp-↭ (++-assoc ys xs zs) ∘ Any-resp-↭ (++⁺ʳ zs $ ++-comm xs ys)) $ Any-resp-↭∘˘++-assocʳʳ {xs = xs} x∈ ⟩
      ( Any-resp-↭ (++-assoc ys xs zs)
      ∘ Any-resp-↭ (++⁺ʳ zs $ ++-comm xs ys)
      ∘ L.Any.++⁺ʳ (xs ++ ys)
      ) x∈
    ≡⟨ cong (Any-resp-↭ (++-assoc ys xs zs)) $ Any-resp-↭∘Any-++⁺ʳʳ (++-comm xs ys) x∈ ⟩
      ( Any-resp-↭ (++-assoc ys xs zs)
      ∘ L.Any.++⁺ʳ (ys ++ xs)
      ) x∈
    ≡⟨ Any-resp-↭∘++-assocʳ {xs = ys} x∈ ⟩
      ( L.Any.++⁺ʳ ys
      ∘ L.Any.++⁺ʳ xs
      ) x∈
    ∎

  Any-resp-↭∘ˡshiftsˡ :
    (x∈ : Any P xs)
    (p↭ : xs ++ zs ↭ xs ++ ws)
    --————————————————————————————————————————————————
    → ( Any-resp-↭ (++⁺ˡ ys p↭)        -- Any P (ys ++ xs ++ ws)
      ∘ Any-resp-↭ (shifts xs ys {zs}) -- Any P (ys ++ xs ++ zs)
      ∘ L.Any.++⁺ˡ                     -- Any P (xs ++ ys ++ zs)
      ) x∈                             -- Any P xs
    ≡ ( L.Any.++⁺ʳ ys -- Any P (ys ++ xs ++ ws)
      ∘ Any-resp-↭ p↭ -- Any P (xs ++ ws)
      ∘ L.Any.++⁺ˡ    -- Any P (xs ++ zs)
      ) x∈            -- Any P xs
  Any-resp-↭∘ˡshiftsˡ {xs} {zs} {ws} {ys} x∈ p↭
    rewrite Any-resp-↭∘shifts xs ys zs (L.Any.++⁺ˡ {ys = ys ++ zs} x∈)
    = begin
      ( Any-resp-↭ (++⁺ˡ ys p↭)
      ∘ Any-resp-↭ (++-assoc ys xs zs)
      ∘ Any-resp-↭ (++⁺ʳ zs $ ++-comm xs ys)
      ∘ Any-resp-↭ (↭-sym $ ++-assoc xs ys zs)
      ∘ L.Any.++⁺ˡ
      ) x∈
    ≡⟨ cong ( Any-resp-↭ (++⁺ˡ ys p↭)
            ∘ Any-resp-↭ (++-assoc ys xs zs)
            ∘ Any-resp-↭ (++⁺ʳ zs $ ++-comm xs ys)
            ) $ Any-resp-↭∘˘++-assocˡ x∈ ⟩
      ( Any-resp-↭ (++⁺ˡ ys p↭)
      ∘ Any-resp-↭ (++-assoc ys xs zs)
      ∘ Any-resp-↭ (++⁺ʳ zs $ ++-comm xs ys)
      ∘ L.Any.++⁺ˡ
      ∘ L.Any.++⁺ˡ
      ) x∈
    ≡⟨ cong ( Any-resp-↭ (++⁺ˡ ys p↭)
            ∘ Any-resp-↭ (++-assoc ys xs zs)
            ) $ Any-resp-↭∘Any-++⁺ʳˡ (++-comm xs ys) (L.Any.++⁺ˡ x∈) ⟩
      ( Any-resp-↭ (++⁺ˡ ys p↭)
      ∘ Any-resp-↭ (++-assoc ys xs zs)
      ∘ L.Any.++⁺ˡ
      ∘ Any-resp-↭ (++-comm xs ys)
      ∘ L.Any.++⁺ˡ
      ) x∈
    ≡⟨ cong (Any-resp-↭ (++⁺ˡ ys p↭) ∘ Any-resp-↭ (++-assoc ys xs zs) ∘ L.Any.++⁺ˡ)
          $ Any-resp-↭∘++-commˡ {ys = ys} x∈ ⟩
      ( Any-resp-↭ (++⁺ˡ ys p↭)
      ∘ Any-resp-↭ (++-assoc ys xs zs)
      ∘ L.Any.++⁺ˡ
      ∘ L.Any.++⁺ʳ ys
      ) x∈
    ≡⟨ cong (Any-resp-↭ (++⁺ˡ ys p↭)) $ Any-resp-↭∘++-assocˡʳ x∈ ⟩
      ( Any-resp-↭ (++⁺ˡ ys p↭)
      ∘ L.Any.++⁺ʳ ys
      ∘ L.Any.++⁺ˡ
      ) x∈
    ≡⟨ Any-resp-↭∘Any-++⁺ˡʳ p↭ (L.Any.++⁺ˡ x∈) ⟩
      ( L.Any.++⁺ʳ ys
      ∘ Any-resp-↭ p↭
      ∘ L.Any.++⁺ˡ
      ) x∈
    ∎

  Any-resp-↭∘ˡˡshifts :
    (x∈ : Any P (xs ++ ys ++ zs))
    (p↭ : zs ↭ ws)
    --————————————————————————————————————————————————
    → ( Any-resp-↭ (++⁺ˡ ys $ ++⁺ˡ xs p↭) -- Any P (ys ++ xs ++ ws)
      ∘ Any-resp-↭ (shifts xs ys {zs})    -- Any P (ys ++ xs ++ zs)
      ) x∈                                -- Any P (xs ++ ys ++ zs)
    ≡ ( Any-resp-↭ (shifts xs ys {ws})    -- Any P (ys ++ xs ++ ws)
      ∘ Any-resp-↭ (++⁺ˡ xs $ ++⁺ˡ ys p↭) -- Any P (xs ++ ys ++ ws)
      ) x∈                                -- Any P (xs ++ ys ++ zs)
  Any-resp-↭∘ˡˡshifts {xs}{ys}{zs}{ws} x∈ p↭
    with destruct-Any-++² {xs = xs}{ys}{zs} x∈
  ... | inj₁ (x∈xs , refl)
    = begin
      ( Any-resp-↭ (++⁺ˡ ys $ ++⁺ˡ xs p↭)
      ∘ Any-resp-↭ (shifts xs ys {zs})
      ∘ L.Any.++⁺ˡ
      ) x∈xs
    ≡⟨ cong (Any-resp-↭ (++⁺ˡ ys $ ++⁺ˡ xs p↭)) $ Any-resp-↭∘shiftsˡ x∈xs ⟩
      ( Any-resp-↭ (++⁺ˡ ys $ ++⁺ˡ xs p↭)
      ∘ L.Any.++⁺ʳ ys
      ∘ L.Any.++⁺ˡ
      ) x∈xs
    ≡⟨ Any-resp-↭∘Any-++⁺ˡʳ (++⁺ˡ xs p↭) (L.Any.++⁺ˡ x∈xs) ⟩
      ( L.Any.++⁺ʳ ys
      ∘ Any-resp-↭ (++⁺ˡ xs p↭)
      ∘ L.Any.++⁺ˡ
      ) x∈xs
    ≡⟨ cong (L.Any.++⁺ʳ ys) $ Any-resp-↭∘Any-++⁺ˡˡ p↭ x∈xs ⟩
      ( L.Any.++⁺ʳ ys
      ∘ L.Any.++⁺ˡ
      ) x∈xs
    ≡˘⟨ Any-resp-↭∘shiftsˡ x∈xs ⟩
      ( Any-resp-↭ (shifts xs ys {ws})
      ∘ L.Any.++⁺ˡ
      ) x∈xs
    ≡˘⟨ cong (Any-resp-↭ (shifts xs ys {ws})) $ Any-resp-↭∘Any-++⁺ˡˡ (++⁺ˡ ys p↭) x∈xs ⟩
      ( Any-resp-↭ (shifts xs ys {ws})
      ∘ Any-resp-↭ (++⁺ˡ xs $ ++⁺ˡ ys p↭)
      ∘ L.Any.++⁺ˡ
      ) x∈xs
    ∎
  ... | inj₂ (inj₁ (x∈ys , refl))
    = begin
      ( Any-resp-↭ (++⁺ˡ ys $ ++⁺ˡ xs p↭)
      ∘ Any-resp-↭ (shifts xs ys {zs})
      ∘ L.Any.++⁺ʳ xs
      ∘ L.Any.++⁺ˡ
      ) x∈ys
    ≡⟨ cong (Any-resp-↭ (++⁺ˡ ys $ ++⁺ˡ xs p↭)) $ Any-resp-↭∘shiftsʳˡ {ys = xs} x∈ys ⟩
      ( Any-resp-↭ (++⁺ˡ ys $ ++⁺ˡ xs p↭)
      ∘ L.Any.++⁺ˡ
      ) x∈ys
    ≡⟨ Any-resp-↭∘Any-++⁺ˡˡ (++⁺ˡ xs p↭) x∈ys ⟩
      L.Any.++⁺ˡ x∈ys
    ≡˘⟨ Any-resp-↭∘shiftsʳˡ {ys = xs} x∈ys ⟩
      ( Any-resp-↭ (shifts xs ys {ws})
      ∘ L.Any.++⁺ʳ xs
      ∘ L.Any.++⁺ˡ
      ) x∈ys
    ≡˘⟨ (cong (Any-resp-↭ (shifts xs ys {ws}) ∘ L.Any.++⁺ʳ xs)
            $ Any-resp-↭∘Any-++⁺ˡˡ p↭ x∈ys) ⟩
      ( Any-resp-↭ (shifts xs ys {ws})
      ∘ L.Any.++⁺ʳ xs
      ∘ Any-resp-↭ (++⁺ˡ ys p↭)
      ∘ L.Any.++⁺ˡ
      ) x∈ys
    ≡˘⟨ cong (Any-resp-↭ (shifts xs ys {ws}))
           $ Any-resp-↭∘Any-++⁺ˡʳ (++⁺ˡ ys p↭) (L.Any.++⁺ˡ x∈ys) ⟩
      ( Any-resp-↭ (shifts xs ys {ws})
      ∘ Any-resp-↭ (++⁺ˡ xs $ ++⁺ˡ ys p↭)
      ∘ L.Any.++⁺ʳ xs
      ∘ L.Any.++⁺ˡ
      ) x∈ys
    ∎
  ... | inj₂ (inj₂ (x∈zs , refl))
    = begin
      ( Any-resp-↭ (++⁺ˡ ys $ ++⁺ˡ xs p↭)
      ∘ Any-resp-↭ (shifts xs ys {zs})
      ∘ L.Any.++⁺ʳ xs
      ∘ L.Any.++⁺ʳ ys
      ) x∈zs
    ≡⟨ cong (Any-resp-↭ (++⁺ˡ ys $ ++⁺ˡ xs p↭)) $ Any-resp-↭∘shiftsʳʳ {xs = xs} x∈zs ⟩
      ( Any-resp-↭ (++⁺ˡ ys $ ++⁺ˡ xs p↭)
      ∘ L.Any.++⁺ʳ ys
      ∘ L.Any.++⁺ʳ xs
      ) x∈zs
    ≡⟨ Any-resp-↭∘Any-++⁺ˡʳ (++⁺ˡ xs p↭) (L.Any.++⁺ʳ xs x∈zs) ⟩
      ( L.Any.++⁺ʳ ys
      ∘ Any-resp-↭ (++⁺ˡ xs p↭)
      ∘ L.Any.++⁺ʳ xs
      ) x∈zs
    ≡⟨ cong (L.Any.++⁺ʳ ys) $ Any-resp-↭∘Any-++⁺ˡʳ p↭ x∈zs ⟩
      ( L.Any.++⁺ʳ ys
      ∘ L.Any.++⁺ʳ xs
      ∘ Any-resp-↭ p↭
      ) x∈zs
    ≡˘⟨ Any-resp-↭∘shiftsʳʳ {zs = ws}{xs}{ys} (Any-resp-↭ p↭ x∈zs) ⟩
      ( Any-resp-↭ (shifts xs ys {ws})
      ∘ L.Any.++⁺ʳ xs
      ∘ L.Any.++⁺ʳ ys
      ∘ Any-resp-↭ p↭
      ) x∈zs
    ≡˘⟨ cong (Any-resp-↭ (shifts xs ys {ws}) ∘ L.Any.++⁺ʳ xs)
           $ Any-resp-↭∘Any-++⁺ˡʳ p↭ x∈zs ⟩
      ( Any-resp-↭ (shifts xs ys {ws})
      ∘ L.Any.++⁺ʳ xs
      ∘ Any-resp-↭ (++⁺ˡ ys p↭)
      ∘ L.Any.++⁺ʳ ys
      ) x∈zs
    ≡˘⟨ cong (Any-resp-↭ (shifts xs ys {ws}))
           $ Any-resp-↭∘Any-++⁺ˡʳ (++⁺ˡ ys p↭) (L.Any.++⁺ʳ ys x∈zs) ⟩
      ( Any-resp-↭ (shifts xs ys {ws})
      ∘ Any-resp-↭ (++⁺ˡ xs $ ++⁺ˡ ys p↭)
      ∘ L.Any.++⁺ʳ xs
      ∘ L.Any.++⁺ʳ ys
      ) x∈zs
    ∎

  Any-resp-↭∘shifts∘++⁺ˡ :
    ∀ (x∈ : Any P zs) (p↭ : xs ++ zs ↭ xs ++ ws)
    --——————————————————————————————————————————
    → ( Any-resp-↭ (L.Perm.↭-trans (shifts xs ys) (++⁺ˡ ys p↭))
      ∘ L.Any.++⁺ʳ xs
      ∘ L.Any.++⁺ʳ ys
      ) x∈
    ≡ ( L.Any.++⁺ʳ ys
      ∘ Any-resp-↭ p↭
      ∘ L.Any.++⁺ʳ xs
      ) x∈
  Any-resp-↭∘shifts∘++⁺ˡ {zs}{xs}{ws}{ys} x∈ p↭ =
    begin
      ( Any-resp-↭ (L.Perm.↭-trans (shifts xs ys) (++⁺ˡ ys p↭))
      ∘ L.Any.++⁺ʳ xs
      ∘ L.Any.++⁺ʳ ys
      ) x∈
    ≡⟨ Any-resp-↭∘↭-trans (L.Any.++⁺ʳ xs $ L.Any.++⁺ʳ ys x∈) (shifts xs ys) (++⁺ˡ ys p↭)  ⟩
      ( Any-resp-↭ (++⁺ˡ ys p↭)
      ∘ Any-resp-↭ (shifts xs ys)
      ∘ L.Any.++⁺ʳ xs
      ∘ L.Any.++⁺ʳ ys
      ) x∈
    ≡⟨ cong (Any-resp-↭ (++⁺ˡ ys p↭)) (Any-resp-↭∘shiftsʳʳ {xs = xs}{ys} x∈) ⟩
      ( Any-resp-↭ (++⁺ˡ ys p↭)
      ∘ L.Any.++⁺ʳ ys
      ∘ L.Any.++⁺ʳ xs
      ) x∈
    ≡⟨ Any-resp-↭∘Any-++⁺ˡʳ p↭ (L.Any.++⁺ʳ xs x∈) ⟩
      ( L.Any.++⁺ʳ ys
      ∘ Any-resp-↭ p↭
      ∘ L.Any.++⁺ʳ xs
      ) x∈
    ∎

  -- ** concat
  Any-resp-↭∘Any-concat⁺ :
    (xss↭ : xss ↭ yss)
    (xs∈ : Any (Any P) xss) →
    --————————————————————————————————————————————————
      ( Any-resp-↭ (↭-concat⁺ xss↭) -- Any P (concat yss)
      ∘ L.Any.concat⁺               -- Any P (concat xss)
      ) xs∈                         -- Any (Any P) xss
    ≡ ( L.Any.concat⁺   -- Any P (concat yss)
      ∘ Any-resp-↭ xss↭ -- Any (Any P) yss
      ) xs∈             -- Any (Any P) xss
  Any-resp-↭∘Any-concat⁺ refl _ = refl
  Any-resp-↭∘Any-concat⁺ (↭-prep {xs = xss}{yss} xs xss↭) xs∈
    with xs∈
  ... | here x∈ = Any-resp-↭∘Any-++⁺ˡˡ {zs = xs} (↭-concat⁺ xss↭) x∈
  ... | there xs∈
    rewrite Any-resp-↭∘Any-++⁺ˡʳ {zs = xs} (↭-concat⁺ xss↭) (L.Any.concat⁺ xs∈)
          | Any-resp-↭∘Any-concat⁺ xss↭ xs∈
          = refl
  Any-resp-↭∘Any-concat⁺ (↭-trans p q) x∈
    rewrite Any-resp-↭∘Any-concat⁺ p x∈
    = Any-resp-↭∘Any-concat⁺ q (Any-resp-↭ p x∈)
  Any-resp-↭∘Any-concat⁺ {xss = .xs ∷ .ys ∷ xss} {yss = .ys ∷ .xs ∷ yss} (swap xs ys xss↭) xs∈
    rewrite ↭-trans∘reflʳ (++⁺ˡ ys $ ++⁺ˡ xs $ ↭-concat⁺ xss↭)
    with xs∈
  ... | here x∈
    = begin
      ( Any-resp-↭ ( L.Perm.↭-trans (shifts xs ys)
                   $ (++⁺ˡ ys $ ++⁺ˡ xs $ ↭-concat⁺ xss↭)
                   )
      ∘ L.Any.++⁺ˡ
      ) x∈
    ≡⟨ Any-resp-↭∘↭-trans (L.Any.++⁺ˡ x∈) (shifts xs ys) (++⁺ˡ ys $ ++⁺ˡ xs $ ↭-concat⁺ xss↭) ⟩
      ( Any-resp-↭ (++⁺ˡ ys $ ++⁺ˡ xs $ ↭-concat⁺ xss↭) -- Any P (ys ++ xs ++ concat yss)
      ∘ Any-resp-↭ (shifts xs ys {concat xss})          -- Any P (ys ++ xs ++ concat xss)
      ∘ L.Any.++⁺ˡ                                      -- Any P (xs ++ ys ++ concat xss)
      ) x∈                                              -- Any P xs
    ≡⟨ Any-resp-↭∘ˡˡshifts {xs = xs} (L.Any.++⁺ˡ x∈) (↭-concat⁺ xss↭) ⟩
      ( Any-resp-↭ (shifts xs ys)                       -- Any P (ys ++ xs ++ concat yss)
      ∘ Any-resp-↭ (++⁺ˡ xs $ ++⁺ˡ ys $ ↭-concat⁺ xss↭) -- Any P (xs ++ ys ++ concat yss)
      ∘ L.Any.++⁺ˡ                                      -- Any P (xs ++ ys ++ concat xss)
      ) x∈                                              -- Any P xs
    ≡⟨ cong (Any-resp-↭ (shifts xs ys {concat yss})) $ Any-resp-↭∘Any-++⁺ˡˡ (++⁺ˡ ys $ ↭-concat⁺ xss↭) x∈ ⟩
      ( Any-resp-↭ (shifts xs ys {concat yss}) -- Any P (ys ++ xs ++ ws)
      ∘ L.Any.++⁺ˡ                             -- Any P (xs ++ ys ++ ws)
      ) x∈                                     -- Any P xs
    ≡⟨ Any-resp-↭∘shiftsˡ x∈ ⟩
      ( L.Any.++⁺ʳ ys -- Any P (ys ++ xs ++ ws)
      ∘ L.Any.++⁺ˡ    -- Any P (xs ++ ws)
      ) x∈            -- Any P xs
    ∎
  ... | there (here x∈)
    = begin
      ( Any-resp-↭ ( L.Perm.↭-trans (shifts xs ys)
                   $ (++⁺ˡ ys $ ++⁺ˡ xs $ ↭-concat⁺ xss↭)
                   )
      ∘ L.Any.++⁺ʳ xs
      ∘ L.Any.++⁺ˡ
      ) x∈
    ≡⟨ Any-resp-↭∘↭-trans _ (shifts xs ys) (++⁺ˡ ys $ ++⁺ˡ xs $ ↭-concat⁺ xss↭) ⟩
      ( Any-resp-↭ (++⁺ˡ ys $ ++⁺ˡ xs $ ↭-concat⁺ xss↭)  -- Any P (ys ++ xs ++ concat yss)
      ∘ Any-resp-↭ (shifts xs ys)                        -- Any P (ys ++ xs ++ concat xss)
      ∘ L.Any.++⁺ʳ xs                                    -- Any P (xs ++ ys ++ concat xss)
      ∘ L.Any.++⁺ˡ                                       -- Any P (ys ++ concat xss)
      ) x∈                                               -- Any P ys
    ≡⟨ Any-resp-↭∘ˡˡshifts {xs = xs} (L.Any.++⁺ʳ xs (L.Any.++⁺ˡ x∈)) (↭-concat⁺ xss↭) ⟩
      ( Any-resp-↭ (shifts xs ys)                        -- Any P (ys ++ xs ++ concat xss)
      ∘ Any-resp-↭ (++⁺ˡ xs $ ++⁺ˡ ys $ ↭-concat⁺ xss↭)  -- Any P (xs ++ ys ++ concat yss)
      ∘ L.Any.++⁺ʳ xs                                    -- Any P (xs ++ ys ++ concat xss)
      ∘ L.Any.++⁺ˡ                                       -- Any P (ys ++ concat xss)
      ) x∈                                               -- Any P ys
    ≡⟨ cong (Any-resp-↭ (shifts xs ys)) $ Any-resp-↭∘Any-++⁺ˡʳ (++⁺ˡ ys $ ↭-concat⁺ xss↭) (L.Any.++⁺ˡ x∈) ⟩
      ( Any-resp-↭ (shifts xs ys)              -- Any P (ys ++ xs ++ concat yss
      ∘ L.Any.++⁺ʳ xs                          -- Any P (xs ++ ys ++ concat yss)
      ∘ Any-resp-↭ (++⁺ˡ ys $ ↭-concat⁺ xss↭)  -- Any P (ys ++ concat yss)
      ∘ L.Any.++⁺ˡ                             -- Any P (ys ++ concat xss)
      ) x∈                                     -- Any P ys
    ≡⟨ cong (Any-resp-↭ (shifts xs ys) ∘ L.Any.++⁺ʳ xs) $ Any-resp-↭∘Any-++⁺ˡˡ (↭-concat⁺ xss↭) x∈ ⟩
      ( Any-resp-↭ (shifts xs ys)              -- Any P (ys ++ xs ++ concat yss)
      ∘ L.Any.++⁺ʳ xs                          -- Any P (xs ++ ys ++ concat yss)
      ∘ L.Any.++⁺ˡ                             -- Any P (ys ++ concat xss)
      ) x∈                                     -- Any P ys
    ≡⟨ Any-resp-↭∘shiftsʳˡ {ys = xs} x∈ ⟩
      L.Any.++⁺ˡ -- Any P (ys ++ xs ++ concat yss)
      x∈         -- Any P ys
    ∎
  ... | there (there xs∈)
    = begin
      ( Any-resp-↭ ( L.Perm.↭-trans (shifts xs ys)
                   $ (++⁺ˡ ys $ ++⁺ˡ xs $ ↭-concat⁺ xss↭)
                   )  -- Any P (ys ++ xs ++ concat yss)
      ∘ L.Any.++⁺ʳ xs -- Any P (xs ++ ys ++ concat xss)
      ∘ L.Any.++⁺ʳ ys -- Any P (ys ++ concat xss)
      ∘ L.Any.concat⁺ -- Any P (concat xss)
      ) xs∈           -- Any (Any P) xss
    ≡⟨ Any-resp-↭∘↭-trans _ (shifts xs ys) (++⁺ˡ ys $ ++⁺ˡ xs $ ↭-concat⁺ xss↭) ⟩
      ( Any-resp-↭ (++⁺ˡ ys $ ++⁺ˡ xs $ ↭-concat⁺ xss↭) -- Any P (ys ++ xs ++ concat yss)
      ∘ Any-resp-↭ (shifts xs ys)                       -- Any P (ys ++ xs ++ concat xss)
      ∘ L.Any.++⁺ʳ xs                                   -- Any P (xs ++ ys ++ concat xss)
      ∘ L.Any.++⁺ʳ ys                                   -- Any P (ys ++ concat xss)
      ∘ L.Any.concat⁺                                   -- Any P (concat xss)
      ) xs∈                                             -- Any (Any P) xss
    ≡⟨ Any-resp-↭∘ˡˡshifts {xs = xs} (L.Any.++⁺ʳ xs $ L.Any.++⁺ʳ ys $ L.Any.concat⁺ xs∈) (↭-concat⁺ xss↭) ⟩
      ( Any-resp-↭ (shifts xs ys)                       -- Any P (ys ++ xs ++ concat xss)
      ∘ Any-resp-↭ (++⁺ˡ xs $ ++⁺ˡ ys $ ↭-concat⁺ xss↭) -- Any P (xs ++ ys ++ concat yss)
      ∘ L.Any.++⁺ʳ xs                                   -- Any P (xs ++ ys ++ concat xss)
      ∘ L.Any.++⁺ʳ ys                                   -- Any P (ys ++ concat xss)
      ∘ L.Any.concat⁺                                   -- Any P (concat xss)
      ) xs∈                                             -- Any (Any P) xss
    ≡⟨ cong (Any-resp-↭ (shifts xs ys)) $ Any-resp-↭∘Any-++⁺ˡʳ (++⁺ˡ ys $ ↭-concat⁺ xss↭) _ ⟩
      ( Any-resp-↭ (shifts xs ys)             -- Any P (ys ++ xs ++ concat xss)
      ∘ L.Any.++⁺ʳ xs                         -- Any P (xs ++ ys ++ concat yss)
      ∘ Any-resp-↭ (++⁺ˡ ys $ ↭-concat⁺ xss↭) -- Any P (ys ++ concat yss)
      ∘ L.Any.++⁺ʳ ys                         -- Any P (ys ++ concat xss)
      ∘ L.Any.concat⁺                         -- Any P (concat xss)
      ) xs∈                                   -- Any (Any P) xss
    ≡⟨ cong (Any-resp-↭ (shifts xs ys) ∘ L.Any.++⁺ʳ xs) $ Any-resp-↭∘Any-++⁺ˡʳ (↭-concat⁺ xss↭) _ ⟩
      ( Any-resp-↭ (shifts xs ys)   -- Any P (ys ++ xs ++ concat yss)
      ∘ L.Any.++⁺ʳ xs               -- Any P (xs ++ ys ++ concat yss)
      ∘ L.Any.++⁺ʳ ys               -- Any P (ys ++ concat yss)
      ∘ Any-resp-↭ (↭-concat⁺ xss↭) -- Any P (concat yss)
      ∘ L.Any.concat⁺               -- Any P (concat xss)
      ) xs∈                         -- Any (Any P) xss
    ≡⟨ Any-resp-↭∘shiftsʳʳ {xs = xs} (Any-resp-↭ (↭-concat⁺ xss↭) $ L.Any.concat⁺ xs∈) ⟩
      ( L.Any.++⁺ʳ ys               -- Any P (ys ++ xs ++ concat yss)
      ∘ L.Any.++⁺ʳ xs               -- Any P (xs ++ concat yss)
      ∘ Any-resp-↭ (↭-concat⁺ xss↭) -- Any P (concat yss)
      ∘ L.Any.concat⁺               -- Any P (concat xss)
      ) xs∈                         -- Any (Any P) xss
    ≡⟨ cong (L.Any.++⁺ʳ ys ∘ L.Any.++⁺ʳ xs) $ Any-resp-↭∘Any-concat⁺ xss↭ xs∈ ⟩
      ( L.Any.++⁺ʳ ys   -- Any P (ys ++ xs ++ concat yss)
      ∘ L.Any.++⁺ʳ xs   -- Any P (xs ++ concat yss)
      ∘ L.Any.concat⁺   -- Any P (concat yss)
      ∘ Any-resp-↭ xss↭ -- Any (Any P) yss
      ) xs∈             -- Any (Any P) xss
    ∎

postulate
  ↭-sym∘shifts : ∀ (xs ys zs : List A)
    → ↭-sym (shifts xs ys {zs})
    ≡ shifts ys xs

postulate
  ↭-sym∘concat⁺ :
    (p : xss ↭ yss)
    --———————————————————
    → ↭-sym (↭-concat⁺ p)
    ≡ ↭-concat⁺ (↭-sym p)
{-
↭-sym∘concat⁺ ↭-refl = refl
↭-sym∘concat⁺ (↭-prep _ p)
  rewrite sym $ ↭-sym∘concat⁺ p
        = ↭-sym∘++⁺ˡ (↭-concat⁺ p)
↭-sym∘concat⁺ (↭-trans p q)
  rewrite ↭-sym∘concat⁺ p
        | ↭-sym∘concat⁺ q
        = refl
↭-sym∘concat⁺ {xss = _ ∷ _ ∷ xss} (↭-swap xs ys p)
-}
  {-
  = begin
    ↭-sym (↭-concat⁺ (↭-swap xs ys p))
  ≡⟨⟩
    ↭-sym ( L.Perm.↭-trans (shifts xs ys)
          $ L.Perm.↭-trans (++⁺ˡ ys $ ++⁺ˡ xs $ ↭-concat⁺ p) refl
          )
  ≡⟨ {!!} ⟩
    L.Perm.↭-trans
      (↭-sym $ L.Perm.↭-trans (++⁺ˡ ys $ ++⁺ˡ xs $ ↭-concat⁺ p) refl)
      (↭-sym $ shifts xs ys)
  ≡⟨ {!!} ⟩
    L.Perm.↭-trans
      (↭-sym $ L.Perm.↭-trans (++⁺ˡ ys $ ++⁺ˡ xs $ ↭-concat⁺ p) refl)
      (shifts ys xs)
  ≡⟨ {!!} ⟩
    L.Perm.↭-trans
      (L.Perm.↭-trans (↭-sym $ ++⁺ˡ ys $ ++⁺ˡ xs $ ↭-concat⁺ p) refl)
      (shifts ys xs)
  ≡⟨ {!!} ⟩
    L.Perm.↭-trans
      (L.Perm.↭-trans (++⁺ˡ ys $ ↭-sym $ ++⁺ˡ xs $ ↭-concat⁺ p) refl)
      (shifts ys xs)
  ≡⟨ {!!} ⟩
    L.Perm.↭-trans
      (L.Perm.↭-trans (++⁺ˡ ys $ ++⁺ˡ xs $ ↭-sym $ ↭-concat⁺ p) refl)
      (shifts ys xs)
  ≡⟨ {!!} ⟩
    L.Perm.↭-trans
      (L.Perm.↭-trans (++⁺ˡ ys $ ++⁺ˡ xs $ ↭-concat⁺ $ ↭-sym p) refl)
      (shifts ys xs)
  ≡⟨ {!!} ⟩
    L.Perm.↭-trans
      (shifts ys xs)
      (L.Perm.↭-trans (++⁺ˡ xs $ ++⁺ˡ ys $ ↭-concat⁺ $ ↭-sym p) refl)
  ≡⟨⟩
    ↭-concat⁺ (↭-swap ys xs $ ↭-sym p)
  ≡⟨⟩
    ↭-concat⁺ (↭-sym $ ↭-swap xs ys p)
  ∎ where open ≡-Reasoning
  -- ↭-sym $ trans (shifts xs ys) (trans (++ ys ++ xs $ concat p) refl)
  -- ≡ trans (shifts ys xs) (trans (++ xs ++ ys $ concat $ sym p) refl)
  rewrite ↭-sym∘↭trans (shifts xs ys)
            (L.Perm.↭-trans (++⁺ˡ ys (++⁺ˡ xs (↭-concat⁺ p))) ↭-refl)
  -- trans (↭-sym $ shifts xs ys) (↭-sym (...) refl)
        | ↭-sym∘shifts xs ys (concat xss)
        = {!cong (L.Perm.↭-trans (shifts ys xs)) ?!}
  -- trans (shifts xs ys) (sym $ trans (++ ys ++ xs $ concat p) refl)
  -- ≡ trans (shifts ys xs) (trans (++ xs ++ ys $ concat $ sym p) refl)
  -- trans (shifts ys xs) (↭-sym $ trans (...) refl)
        | ↭-sym∘↭trans (++⁺ˡ ys (++⁺ˡ xs (↭-concat⁺ p))) ↭-refl
  -- trans (shifts ys xs) (trans (↭-sym ...) refl)
        | ↭-sym∘++⁺ˡ {zs = ys} (++⁺ˡ xs (↭-concat⁺ p))
  -- trans (shifts ys xs) (trans (++⁺ˡ ys ↭-sym ...) refl)
        | ↭-sym∘++⁺ˡ {zs = xs} (↭-concat⁺ p)
  -- trans (shifts ys xs) (trans (++⁺ˡ ys $ ++⁺ˡ xs ↭-sym $ ↭-concat⁺ p) refl)
        | ↭-sym∘concat⁺ p
  -- trans (shifts ys xs) (trans (++⁺ˡ ys $ ++⁺ˡ xs $ ↭-concat⁺ $ ↭-sym p) refl)
        = {!!}
  -}

-- ** map
module _ {f : A → B} {P : Pred B ℓ} where

  Any-resp-↭∘map⁺ :
    (xs↭ : xs ↭ ys)
    (x∈ : Any (P ∘ f) xs) →
    --————————————————————————————————————————————————
      ( Any-resp-↭ {P = P} (map⁺ f xs↭) -- Any P (map f ys)
      ∘ L.Any.map⁺ {f = f}              -- Any P (map f xs)
      ) x∈                              -- Any (P ∘ f) xs
    ≡ ( L.Any.map⁺ {f = f} -- Any P (map f ys)
      ∘ Any-resp-↭ xs↭     -- Any (P ∘ f) ys
      ) x∈                 -- Any (P ∘ f) xs
  Any-resp-↭∘map⁺ xs↭ x∈
      with xs↭         | x∈
  ... | refl           | _                = refl
  ... | ↭-prep _ xs↭   | here _           = refl
  ... | ↭-prep _ xs↭   | there x∈         = cong there $ Any-resp-↭∘map⁺ xs↭ x∈
  ... | swap _ _ xs↭ | here _           = refl
  ... | swap _ _ xs↭ | there (here _)   = refl
  ... | swap _ _ xs↭ | there (there x∈) = cong (there ∘′ there) $ Any-resp-↭∘map⁺ xs↭ x∈
  ... | ↭-trans p q  | x∈
      rewrite Any-resp-↭∘map⁺ p x∈
      = Any-resp-↭∘map⁺ q (Any-resp-↭ p x∈)

  Any-map⁻∘Any-resp-↭∘map⁺ :
    (p : xs ↭ ys)
    (x∈ : Any P (map f xs))
    --—————————————————————
    → ( L.Any.map⁻            -- Any (P ∘ f) ys
      ∘ Any-resp-↭ (map⁺ f p) -- Any P (map f ys)
      ) x∈                    -- Any P (map f xs)
    ≡ ( Any-resp-↭ p -- Any (P ∘ f) ys
      ∘ L.Any.map⁻   -- Any (P ∘ f) xs
      ) x∈           -- Any P (map f xs)
  Any-map⁻∘Any-resp-↭∘map⁺ refl y∈ = refl
  Any-map⁻∘Any-resp-↭∘map⁺ (↭-prep x p) y∈ with y∈
  ... | here _ = refl
  ... | there y∈ rewrite Any-map⁻∘Any-resp-↭∘map⁺ p y∈ = refl
  Any-map⁻∘Any-resp-↭∘map⁺ (swap x y p) y∈ with y∈
  ... | here _ = refl
  ... | there (here _) = refl
  ... | there (there y∈) rewrite Any-map⁻∘Any-resp-↭∘map⁺ p y∈ = refl
  Any-map⁻∘Any-resp-↭∘map⁺ (↭-trans p p′) y∈
    rewrite Any-map⁻∘Any-resp-↭∘map⁺ p′ (Any-resp-↭ (map⁺ f p) y∈)
          | Any-map⁻∘Any-resp-↭∘map⁺ p y∈
          = refl

module _ {A B : Type} (f : A → B) where

  ∈-map⁻∘∈-resp-↭∘map⁺ : ∀ {y : B} {xs ys : List A}
    (p : xs ↭ ys)
    (y∈ : y ∈ map f xs)
    --—————————————————————
    → ( ∈-map⁻ f            -- ∃x. (x ∈ ys) × (y ≡ f x)
      ∘ ∈-resp-↭ (map⁺ f p) -- y ∈ map f ys
      ) y∈                  -- y ∈ map f xs
    ≡ ( map₂′ (map₁ $ ∈-resp-↭ p) -- ∃x. (x ∈ ys) × (y ≡ f x)
      ∘ ∈-map⁻ f                  -- ∃x. (x ∈ xs) × (y ≡ f x)
      ) y∈                        -- y ∈ map f xs
  ∈-map⁻∘∈-resp-↭∘map⁺ {y = y} p y∈
    rewrite Any-map⁻∘Any-resp-↭∘map⁺ {P = y ≡_} p y∈
          | find∘Any-resp-↭ p (L.Any.map⁻ y∈)
          = refl

-- ** concatMap
module _ {f : A → List B} where
  Any-resp-↭∘Any-concatMap⁺ : ∀ {P : Pred B ℓ}
    (xs↭ : xs ↭ ys)
    (x∈ : Any (Any P ∘ f) xs) →
    --————————————————————————————————————————————————
      ( Any-resp-↭ (↭-concatMap⁺ f xs↭) -- Any P (concatMap f ys)
      ∘ Any-concatMap⁺                  -- Any P (concatMap f xs)
      ) x∈                              -- Any (Any P ∘ f) xs
    ≡ ( Any-concatMap⁺ -- Any P (concatMap f ys)
      ∘ Any-resp-↭ xs↭ -- Any (Any P ∘ f) ys
      ) x∈             -- Any (Any P ∘ f) xs
  Any-resp-↭∘Any-concatMap⁺ xs↭ x∈ =
    begin
      ( Any-resp-↭ (↭-concatMap⁺ f xs↭)
      ∘ Any-concatMap⁺
      ) x∈
    ≡⟨⟩
      ( Any-resp-↭ (↭-concat⁺ $ map⁺ f xs↭)
      ∘ L.Any.concat⁺
      ∘ L.Any.map⁺
      ) x∈
    ≡⟨ Any-resp-↭∘Any-concat⁺ (map⁺ f xs↭) (L.Any.map⁺ x∈) ⟩
      ( L.Any.concat⁺
      ∘ Any-resp-↭ (map⁺ f xs↭)
      ∘ L.Any.map⁺
      ) x∈
    ≡⟨ cong L.Any.concat⁺ $ Any-resp-↭∘map⁺ xs↭ x∈ ⟩
      ( L.Any.concat⁺
      ∘ L.Any.map⁺
      ∘ Any-resp-↭ xs↭
      ) x∈
    ≡⟨⟩
      ( Any-concatMap⁺
      ∘ Any-resp-↭ xs↭
      ) x∈
    ∎

  ∈-resp-↭∘∈-concatMap⁺ :
    (xs↭ : xs ↭ ys)
    (x∈ : Any (λ x → y ∈ f x) xs) →
    --————————————————————————————————————————————————
      ( ∈-resp-↭ (↭-concatMap⁺ f xs↭)
      ∘ ∈-concatMap⁺
      ) x∈
    ≡ ( ∈-concatMap⁺
      ∘ Any-resp-↭ xs↭
      ) x∈
  ∈-resp-↭∘∈-concatMap⁺ = Any-resp-↭∘Any-concatMap⁺

↭-sym∘concatMap⁺ :
  (f : A → List B)
  (p : xs ↭ ys)
  --———————————————————
  → ↭-sym (↭-concatMap⁺ f p)
  ≡ ↭-concatMap⁺ f (↭-sym p)
↭-sym∘concatMap⁺ f p
  rewrite ↭-sym∘concat⁺ (map⁺ f p)
        | ↭-sym∘map⁺ f p
        = refl

-- ** catMaybes

Any-resp-↭∘Any-catMaybes⁺ : ∀ {P : Pred A ℓ″}
  (xs↭ : xs ↭ ys)
  (x∈ : Any (M.Any.Any P) xs)
  --————————————————————————————————————————————————
  → ( Any-resp-↭ (catMaybes-↭ xs↭) -- Any P (catMaybes ys)
    ∘ Any-catMaybes⁺               -- Any P (catMaybes xs)
    ) x∈                           -- Any (M.Any.Any P) xs
  ≡ ( Any-catMaybes⁺ -- Any P (mapMaybe′ f ys)
    ∘ Any-resp-↭ xs↭ -- Any (M.Any.Any P ∘ f) ys
    ) x∈             -- Any (M.Any.Any P ∘ f) xs
Any-resp-↭∘Any-catMaybes⁺ refl x∈ = refl
Any-resp-↭∘Any-catMaybes⁺ (↭-trans xs↭ ↭ys) x∈
  rewrite Any-resp-↭∘Any-catMaybes⁺ xs↭ x∈
        | Any-resp-↭∘Any-catMaybes⁺ ↭ys (Any-resp-↭ xs↭ x∈)
        = refl
Any-resp-↭∘Any-catMaybes⁺ (↭-prep (just _) xs↭) x∈
  with x∈
... | here (M.Any.just _) = refl
... | there x∈ = cong there $ Any-resp-↭∘Any-catMaybes⁺ xs↭ x∈
Any-resp-↭∘Any-catMaybes⁺ (↭-prep nothing xs↭) (there x∈)
  = Any-resp-↭∘Any-catMaybes⁺ xs↭ x∈
Any-resp-↭∘Any-catMaybes⁺ (swap (just _) (just _) xs↭) x∈
  with x∈
... | here (M.Any.just _) = refl
... | there (here (M.Any.just _)) = refl
... | there (there x∈) = cong (there ∘′ there) $ Any-resp-↭∘Any-catMaybes⁺ xs↭ x∈
Any-resp-↭∘Any-catMaybes⁺ (swap (just _) nothing xs↭) x∈
  with x∈
... | here (M.Any.just _) = refl
... | there (there x∈) = cong there $ Any-resp-↭∘Any-catMaybes⁺ xs↭ x∈
Any-resp-↭∘Any-catMaybes⁺ (swap nothing (just _) xs↭) (there x∈)
  with x∈
... | here (M.Any.just _) = refl
... | there x∈ = cong there $ Any-resp-↭∘Any-catMaybes⁺ xs↭ x∈
Any-resp-↭∘Any-catMaybes⁺ (swap nothing nothing xs↭) (there (there x∈))
  = Any-resp-↭∘Any-catMaybes⁺ xs↭ x∈

-- ** subst
subst-ƛ : ∀ {X : Type ℓ′} {Y : Type ℓ″} {y z : Y} {P : Pred Y ℓ}
  (eq : y ≡ z)
  (p : X → P y)
  (x : X)
  --———————————————————————————
  → subst (λ ◆ → X → P ◆) eq p x
  ≡ subst P eq (p x)
subst-ƛ refl _ _ = refl

module _ {P : Pred A ℓ} where

  Any-resp-↭∘subst :
    (xs↭ : xs ↭ ys)
    (eq : ys ≡ zs)
    (x∈ : Any P xs)
    --——————————————————————————————
    → Any-resp-↭ (subst (xs ↭_) eq xs↭) x∈
    ≡ subst (Any P) eq (Any-resp-↭ xs↭ x∈)
  Any-resp-↭∘subst _ refl _ = refl

  Any-resp-↭∘subst² :
    (xs↭ : xs ↭ ys)
    (eq : ys ≡ zs)
    (eq′ : xs ≡ ws)
    (x∈ : Any P ws)
    --——————————————————————————————
    → Any-resp-↭ (subst (_↭ zs) eq′ $ subst (xs ↭_) eq xs↭) x∈
    ≡ subst (Any P) eq (Any-resp-↭ (subst (_↭ ys) eq′ xs↭) x∈)
  Any-resp-↭∘subst² _ refl refl _ = refl

  Any-resp-↭∘subst∘subst :
    (xs↭ : xs ↭ ys)
    (eq : xs ≡ zs)
    (x∈ : Any P xs)
    --——————————————————————————————
    → Any-resp-↭ (subst (_↭ ys) eq xs↭) (subst (Any P) eq x∈)
    ≡ Any-resp-↭ xs↭ x∈
  Any-resp-↭∘subst∘subst _ refl _ = refl


-- ** mapMaybe
module _ (f : A → Maybe B) where

  Any-resp-↭∘Any-mapMaybe′⁺ : ∀ {P : Pred B ℓ″}
    (xs↭ : xs ↭ ys)
    (x∈ : Any (M.Any.Any P ∘ f) xs)
    --————————————————————————————————————————————————
    → ( Any-resp-↭ (mapMaybe′-↭ f xs↭) -- Any P (mapMaybe′ f ys)
      ∘ Any-mapMaybe′⁺ f               -- Any P (mapMaybe′ f xs)
      ) x∈                             -- Any (M.Any.Any P ∘ f) xs
    ≡ ( Any-mapMaybe′⁺ f -- Any P (mapMaybe′ f ys)
      ∘ Any-resp-↭ xs↭   -- Any (M.Any.Any P ∘ f) ys
      ) x∈               -- Any (M.Any.Any P ∘ f) xs
  Any-resp-↭∘Any-mapMaybe′⁺ xs↭ x∈
    = trans (Any-resp-↭∘Any-catMaybes⁺ (map⁺ f xs↭) (L.Any.map⁺ x∈))
            (cong Any-catMaybes⁺ (Any-resp-↭∘map⁺ xs↭ x∈))

  Any-resp-↭∘Any⇒ : ∀ {P : Pred B ℓ″}
    (xs↭ : xs ↭ ys)
    (x∈ : Any P (mapMaybe′ f xs))
    --————————————————————————————————————————————————————————————
    → ( Any-resp-↭ (mapMaybe-↭ f xs↭) -- Any P (mapMaybe f ys)
      ∘ Any[_]⇒_ f xs                 -- Any P (mapMaybe f xs)
      ) x∈                            -- Any P (mapMaybe′ f xs)
    ≡ ( Any[_]⇒_ f ys                  -- Any P (mapMaybe f ys)
      ∘ Any-resp-↭ (mapMaybe′-↭ f xs↭) -- Any P (mapMaybe′ f ys)
      ) x∈                             -- Any P (mapMaybe′ f xs)
  Any-resp-↭∘Any⇒ {xs = xs} {ys = ys} xs↭ x∈ =
    begin
      ( Any-resp-↭ (mapMaybe-↭ f xs↭)
      ∘ Any[_]⇒_ f xs
      ) x∈
    ≡⟨⟩
      ( Any-resp-↭ ( subst (_↭ _) (mapMaybe≗mapMaybe′ f xs)
                   $ subst (_ ↭_) (mapMaybe≗mapMaybe′ f ys)
                   $ mapMaybe′-↭ f xs↭
                   )
      ∘ Any[_]⇒_ f xs
      ) x∈
    ≡⟨ Any-resp-↭∘subst² (mapMaybe′-↭ f xs↭) (mapMaybe≗mapMaybe′ f ys) (mapMaybe≗mapMaybe′ f xs)
       $ Any[_]⇒_ f xs x∈ ⟩
      ( Any[_]⇒_ f ys
      ∘ Any-resp-↭ ( subst (_↭ _) (mapMaybe≗mapMaybe′ f xs)
                   $ mapMaybe′-↭ f xs↭
                   )
      ∘ Any[_]⇒_ f xs
      ) x∈
    ≡⟨ cong (Any[_]⇒_ f ys) (Any-resp-↭∘subst∘subst (mapMaybe′-↭ f xs↭) (mapMaybe≗mapMaybe′ f xs) x∈) ⟩
      ( Any[_]⇒_ f ys
      ∘ Any-resp-↭ (mapMaybe′-↭ f xs↭)
      ) x∈
    ∎

  Any-resp-↭∘Any-mapMaybe⁺ : ∀ {P : Pred B ℓ″}
    (xs↭ : xs ↭ ys)
    (x∈ : Any (M.Any.Any P ∘ f) xs)
    --————————————————————————————————————————————————
    → ( Any-resp-↭ (mapMaybe-↭ f xs↭) -- Any P (mapMaybe f ys)
      ∘ Any-mapMaybe⁺ f               -- Any P (mapMaybe f xs)
      ) x∈                            -- Any (M.Any.Any P ∘ f) xs
    ≡ ( Any-mapMaybe⁺ f -- Any P (mapMaybe f ys)
      ∘ Any-resp-↭ xs↭  -- Any (M.Any.Any P ∘ f) ys
      ) x∈              -- Any (M.Any.Any P ∘ f) xs
  Any-resp-↭∘Any-mapMaybe⁺ {xs = xs} {ys = ys} {P = P} xs↭ x∈ =
    begin
      ( Any-resp-↭ (mapMaybe-↭ f xs↭) -- Any P (mapMaybe f ys)
      ∘ Any-mapMaybe⁺ f               -- Any P (mapMaybe f xs)
      ) x∈                            -- Any (M.Any.Any P ∘ f) xs
    ≡⟨⟩
      ( Any-resp-↭ (mapMaybe-↭ f xs↭) -- Any P (mapMaybe f ys)
      ∘ Any[_]⇒_ f xs                 -- Any P (mapMaybe f xs)
      ∘ Any-mapMaybe′⁺ f              -- Any P (mapMaybe′ f xs)
      ) x∈                            -- Any (M.Any.Any P ∘ f) xs
    ≡⟨ Any-resp-↭∘Any⇒ xs↭ (Any-mapMaybe′⁺ f x∈) ⟩
      ( Any[_]⇒_ f ys                  -- Any P (mapMaybe f ys)
      ∘ Any-resp-↭ (mapMaybe′-↭ f xs↭) -- Any P (mapMaybe′ f ys)
      ∘ Any-mapMaybe′⁺ f               -- Any P (mapMaybe′ f xs)
      ) x∈                             -- Any (M.Any.Any P ∘ f) xs
    ≡⟨ cong (Any[_]⇒_ f ys) $ Any-resp-↭∘Any-mapMaybe′⁺ xs↭ x∈ ⟩
      ( Any[_]⇒_ f ys    -- Any P (mapMaybe f ys)
      ∘ Any-mapMaybe′⁺ f -- Any P (mapMaybe′ f ys)
      ∘ Any-resp-↭ xs↭   -- Any (M.Any.Any P ∘ f) ys
      ) x∈               -- Any (M.Any.Any P ∘ f) xs
    ≡⟨⟩
      ( Any-mapMaybe⁺ f -- Any P (mapMaybe f ys)
      ∘ Any-resp-↭ xs↭  -- Any (M.Any.Any P ∘ f) ys
      ) x∈              -- Any (M.Any.Any P ∘ f) xs
    ∎

  ∈-resp-↭∘∈-mapMaybe⁺ :
    (xs↭ : xs ↭ ys)
    (eq : f x ≡ just y)
    (x∈ : x ∈ xs)
    --————————————————————————————————————————————————
    → ( ∈-resp-↭ (mapMaybe-↭ f xs↭)
      ∘ flip (∈-mapMaybe⁺ f) eq
      ) x∈
    ≡ ( flip (∈-mapMaybe⁺ f) eq
      ∘ ∈-resp-↭ xs↭
      ) x∈
  ∈-resp-↭∘∈-mapMaybe⁺ {xs = xs} {ys = ys} xs↭ eq x∈
    = begin
      ( ∈-resp-↭ (mapMaybe-↭ f xs↭)
      ∘ flip (∈-mapMaybe⁺ f) eq
      ) x∈
    ≡⟨⟩
      ∈-resp-↭ (mapMaybe-↭ f xs↭) (∈-mapMaybe⁺ f x∈ eq)
    ≡⟨⟩
      Any-resp-↭ (mapMaybe-↭ f xs↭) (Any-mapMaybe⁺ f $ L.Any.map (≡just⇒MAny f eq) x∈)
    ≡⟨ Any-resp-↭∘Any-mapMaybe⁺ xs↭ $ L.Any.map (≡just⇒MAny f eq) x∈ ⟩
      Any-mapMaybe⁺ f (Any-resp-↭ xs↭ $ L.Any.map (≡just⇒MAny f eq) x∈)
    ≡⟨ cong (Any-mapMaybe⁺ f) $ Any-resp-↭∘Any-map (≡just⇒MAny f eq) xs↭ x∈ ⟩
      Any-mapMaybe⁺ f (L.Any.map (≡just⇒MAny f eq) $ Any-resp-↭ xs↭ x∈)
    ≡⟨⟩
      ∈-mapMaybe⁺ f (∈-resp-↭ xs↭ x∈) eq
    ≡⟨⟩
      ( flip (∈-mapMaybe⁺ f) eq
      ∘ ∈-resp-↭ xs↭
      ) x∈
    ∎

postulate
  ↭-sym∘mapMaybe⁺ :
    (f : A → Maybe B)
    (p : xs ↭ ys)
    --———————————————————
    → ↭-sym (mapMaybe-↭ f p)
    ≡ mapMaybe-↭ f (↭-sym p)
