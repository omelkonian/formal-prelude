------------------------------------------------------------------------
-- Properties of permuting lists with _↭_.

module Prelude.Lists.Permutations2 where

open import Prelude.Init
open L.Mem using (_∈_; mapWith∈)
open import Prelude.Lists.Permutations

private variable
  A : Set ℓ
  B : Set ℓ′
  x y : A
  xs ys zs ws : List A
  xss yss : List (List A)

open L.Perm using (shifts; ++⁺ˡ; ++⁺ʳ; map⁺; ↭-sym-involutive; ++-comm; ∈-resp-↭)

open import Prelude.Lists.Mappings

∈-resp-↭-≗↦ :
  (f : xs ↦ B)
  (p : xs ↭ ys)
  --——————————————————————————
  → {!∈-resp-↭!} ≗⟨ p ⟩↦ f -- (∈-resp-↭ p)
∈-resp-↭-≗↦ = {!!}


-- K :
--  (p : xs ≡ ys)
--  → ↭-reflexive p
--  ≡ subst (_↭ ys) (sym p) ↭-refl
-- K {xs = xs} refl = refl

-- ns : List ℕ
-- ns = 0 ∷ 1 ∷ 2 ∷ 3 ∷ []

-- private
--   p₁ : ns ↭ ns
--   p₁ = ↭-refl

--   p₂ : ns ↭ ns
--   p₂ = ↭-prep 0 $ ↭-prep 1 $ ↭-prep 2 $ ↭-prep 3 ↭-refl

--   _ : p₁ ≢ p₂
--   _ = λ ()

-- open import Prelude.Lists.Empty
-- H :
--  ¬Null xs
--  → ↭-reflexive (L.++-identityʳ xs)
--  ≢ ++-comm xs []
-- H {xs = x ∷ xs} _ eq with ↭-reflexive (cong (x ∷_) (L.++-identityʳ xs))
-- ... | p
--   = {!!}
-- -- rewrite sym $ H {xs = xs} | L.++-identityʳ xs = {!refl!}


-- shiftsˡ :
--   (shifts [] ys {zs})
--   ≡ {!!}
-- shiftsˡ = {!!}


-- shiftʳ :
--   shifts xs [] {zs}
--   ≡ {!!}
-- shiftʳ = {!!}

-- ↭-sym∘++-comm :
--   --——————————————————————————
--     ↭-sym (++-comm xs ys)
--   ≡ ++-comm ys xs
-- ↭-sym∘++-comm {xs = []} {ys} rewrite ↭-sym-involutive (L.Perm.++-identityʳ ys) = {!!}
-- ↭-sym∘++-comm {xs = x ∷ xs} {ys} = {!!}
--   -- begin
--   --   ↭-sym (++-comm xs ys) -- ∈ ys ++ xs ++ zs ↭ xs ++ ys ++ zs
--   -- ≡⟨ {!!} ⟩
--   --   ++-comm ys xs         -- ∈ ys ++ xs ++ zs ↭ xs ++ ys ++ zs
--   -- ∎ where open ≡-Reasoning

-- ↭-sym∘shifts :
--   --——————————————————————————
--     ↭-sym (shifts xs ys {zs})
--   ≡ shifts ys xs {zs}
-- ↭-sym∘shifts {xs = xs}{ys}{zs} =
--   begin
--     ↭-sym (shifts xs ys {zs}) -- ∈ ys ++ xs ++ zs ↭ xs ++ ys ++ zs
--   ≡⟨ {!!} ⟩
--     shifts ys xs {zs}         -- ∈ ys ++ xs ++ zs ↭ xs ++ ys ++ zs
--   ∎ where open ≡-Reasoning

-- {-
-- ↭-sym∘shifts {xs = []} {[]} {[]} = refl
-- ↭-sym∘shifts {xs = []} {[]} {x ∷ zs} = refl
-- ↭-sym∘shifts {xs = []} {x ∷ ys} {[]} = {!!}
-- ↭-sym∘shifts {xs = []} {x ∷ ys} {x₁ ∷ zs} = {!!}
-- ↭-sym∘shifts {xs = x ∷ xs} {[]} {[]} = {!!}
-- ↭-sym∘shifts {xs = x ∷ xs} {[]} {x₁ ∷ zs} = {!!}
-- ↭-sym∘shifts {xs = x ∷ xs} {x₁ ∷ ys} {[]} = {!!}
-- ↭-sym∘shifts {xs = x ∷ xs} {x₁ ∷ ys} {x₂ ∷ zs} = {!!}
-- -}

-- {-
-- ↭-sym∘shifts {xs = []}{ys}{zs}
--   rewrite L.++-identityˡ ys
--         | ↭trans∘↭-refl (↭-reflexive $ L.++-assoc ys [] zs)
--         | ↭trans∘↭-refl (++⁺ʳ zs $ ++-comm ys [])
--   =
--   begin
--     ↭-sym
--       (L.Perm.↭-trans (++⁺ʳ zs $ ↭-sym $ ↭-reflexive $ L.++-identityʳ ys)
--                       (↭-reflexive $ L.++-assoc ys [] zs))
--   ≡⟨ ↭-sym∘↭trans (++⁺ʳ zs $ ↭-sym $ ↭-reflexive $ L.++-identityʳ ys) _ ⟩
--     L.Perm.↭-trans (↭-sym $ ↭-reflexive $ L.++-assoc ys [] zs)
--                    (↭-sym $ ++⁺ʳ zs $ ↭-sym $ ↭-reflexive $ L.++-identityʳ ys)

--   ≡⟨ cong (L.Perm.↭-trans (↭-sym $ ↭-reflexive $ L.++-assoc ys [] zs))
--       (begin
--          ↭-sym (++⁺ʳ zs $ ↭-sym $ ↭-reflexive $ L.++-identityʳ ys)
--        ≡⟨ ↭-sym∘++⁺ʳ _  ⟩
--          ++⁺ʳ zs (↭-sym $ ↭-sym $ ↭-reflexive $ L.++-identityʳ ys)
--        ≡⟨ cong (++⁺ʳ zs) (↭-sym-involutive $ ↭-reflexive $ L.++-identityʳ ys) ⟩
--          ++⁺ʳ zs (↭-reflexive $ L.++-identityʳ ys)
--        ≡⟨ cong (++⁺ʳ zs) {!!} ⟩
--          ++⁺ʳ zs (++-comm ys [])
--        ∎) ⟩
--     L.Perm.↭-trans (↭-sym $ ↭-reflexive $ L.++-assoc ys [] zs)
--                    (++⁺ʳ zs $ ++-comm ys [])

--   ∎ where open ≡-Reasoning
--   -- = ↭-sym∘↭trans {!!} {!!}
-- ↭-sym∘shifts {xs = x ∷ xs} = {!!}
-- -}

-- ↭trans∘shifts : ∀ {A : Set ℓ} {xs ys zs ws : List A}
--   → (p : zs ↭ ws)
--   → L.Perm.↭-trans (++⁺ˡ xs $ ++⁺ˡ ys p)
--                    (shifts xs ys)
--   ≡ L.Perm.↭-trans (shifts xs ys)
--                     (++⁺ˡ ys $ ++⁺ˡ xs p)
-- -- ↭trans∘shifts {xs = xs}{ys}{zs}{ws} p = {!!}

-- -- ↭trans∘shifts {xs = []} {[]} {zs} {ws} p = {!refl!}
-- -- ↭trans∘shifts {xs = []} {x ∷ ys} {zs} {ws} p = {!!}
-- -- ↭trans∘shifts {xs = x ∷ xs} {ys} {zs} {ws} p = {!!}

-- -- ↭trans∘shifts {xs = []} {ys} {zs} {.zs} ↭-refl = {!!}
-- -- ↭trans∘shifts {xs = x ∷ xs} {ys} {zs} {.zs} ↭-refl = {!!}
-- -- ↭trans∘shifts {xs = xs} {ys} {.(x ∷ _)} {.(x ∷ _)} (↭-prep x p) = {!!}
-- -- ↭trans∘shifts {xs = xs} {ys} {.(x ∷ y ∷ _)} {.(y ∷ x ∷ _)} (↭-swap x y p) = {!!}
-- -- ↭trans∘shifts {xs = xs} {ys} {zs} {ws} (↭-trans p p₁) = {!!}

-- ↭trans∘shifts {xs = []} {ys} {zs} {ws} p
--   rewrite L.++-identityˡ ys
--   -- rewrite sym $ L.++-identityʳ ys
--   = {!!}
-- ↭trans∘shifts {xs = x ∷ xs} {ys} {zs} {ws} p = {!!}

-- ↭-sym∘↭-concat⁺ :
--   (p : xss ↭ yss)
--   --——————————————————————————
--   → ↭-sym (↭-concat⁺ p)
--   ≡ ↭-concat⁺ (↭-sym p)
-- ↭-sym∘↭-concat⁺ ↭-refl = refl
-- ↭-sym∘↭-concat⁺ (↭-prep xs p)
--   rewrite ↭-sym∘++⁺ˡ {zs = xs} (↭-concat⁺ p)
--         | ↭-sym∘↭-concat⁺ p
--         = refl
-- ↭-sym∘↭-concat⁺ (↭-trans p q)
--   rewrite ↭-sym∘↭-concat⁺ p
--         | ↭-sym∘↭-concat⁺ q
--         = refl
-- ↭-sym∘↭-concat⁺ (↭-swap xs ys p)
--   rewrite ↭trans∘↭-refl (++⁺ˡ ys (++⁺ˡ xs (↭-concat⁺ p)))
--         | ↭trans∘↭-refl (++⁺ˡ xs (++⁺ˡ ys (↭-concat⁺ $ ↭-sym p)))
--   =
--   begin
--     ↭-sym
--       (L.Perm.↭-trans (shifts xs ys)
--                       (++⁺ˡ ys $ ++⁺ˡ xs $ ↭-concat⁺ p))
--   ≡⟨ ↭-sym∘↭trans (shifts xs ys) (++⁺ˡ ys $ ++⁺ˡ xs $ ↭-concat⁺ p) ⟩
--     L.Perm.↭-trans (↭-sym $ ++⁺ˡ ys $ ++⁺ˡ xs $ ↭-concat⁺ p)
--                    (↭-sym $ shifts xs ys)
--   ≡⟨ cong (λ ◆ → L.Perm.↭-trans ◆ (↭-sym $ shifts xs ys)) (↭-sym∘++⁺ˡ∘++⁺ˡ {zs = ys}{xs} $ ↭-concat⁺ p) ⟩
--     L.Perm.↭-trans (++⁺ˡ ys $ ++⁺ˡ xs $ ↭-sym $ ↭-concat⁺ p)
--                    (↭-sym $ shifts xs ys)
--   ≡⟨ cong (λ ◆ → L.Perm.↭-trans (++⁺ˡ ys $ ++⁺ˡ xs ◆) (↭-sym $ shifts xs ys)) (↭-sym∘↭-concat⁺ p) ⟩
--     L.Perm.↭-trans (++⁺ˡ ys $ ++⁺ˡ xs $ ↭-concat⁺ $ ↭-sym p)
--                    (↭-sym $ shifts xs ys)
--   ≡⟨ cong (λ ◆ → L.Perm.↭-trans (++⁺ˡ ys $ ++⁺ˡ xs $ ↭-concat⁺ $ ↭-sym p) ◆) (↭-sym∘shifts {xs = xs}{ys}) ⟩
--     L.Perm.↭-trans (++⁺ˡ ys $ ++⁺ˡ xs $ ↭-concat⁺ $ ↭-sym p)
--                    (shifts ys xs)
--   ≡⟨ ↭trans∘shifts {xs = ys}{xs} (↭-concat⁺ $ ↭-sym p) ⟩
--     L.Perm.↭-trans (shifts ys xs)
--                    (++⁺ˡ xs $ ++⁺ˡ ys $ ↭-concat⁺ $ ↭-sym p)
--   ∎ where open ≡-Reasoning

-- ↭-sym∘↭-concat⁺∘map⁺ :
--   (f : A → List B)
--   (p : xs ↭ ys)
--   --——————————————————————————
--   → ↭-sym (↭-concat⁺ (map⁺ f p))
--   ≡ ↭-concat⁺ (map⁺ f (↭-sym p))
-- ↭-sym∘↭-concat⁺∘map⁺ f p rewrite ↭-sym∘↭-concat⁺ (map⁺ f p) | ↭-sym∘map⁺ f p = refl
