{-# OPTIONS -v Generics:100 #-}
module Prelude.Tactics.DeriveIso where

open import Prelude.Init
open Fun.Inv using (_↔_; inverse)
open import Prelude.Functor
open import Prelude.Semigroup
open import Prelude.Monad
open import Prelude.Show

open import Prelude.Generics
open Meta
open Debug ("Generics.DeriveIso" , 100)

record newtype (A : Set ℓ) : Set ℓ where
  constructor mk
  field unmk : A
open newtype public

private variable X : Set ℓ
newtype↔ : newtype X ↔ X
newtype↔ = inverse unmk mk (λ _ → refl) (λ _ → refl)

instance
  Functor-newtype : Functor newtype
  Functor-newtype ._<$>_ f = mk ∘ f ∘ unmk

mk-injective : ∀ (x y : X) → mk x ≡ mk y → x ≡ y
mk-injective _ _ refl = refl

ℕ˘ = newtype ℕ

_+˘_ : Op₂ ℕ˘
n +˘ m = case unmk m of λ where
  0        → n
  (suc m′) → suc <$> (n +˘ mk m′)

+˘-identityˡ : ∀ x → mk 0 +˘ x ≡ x
+˘-identityˡ (mk 0)       = refl
+˘-identityˡ (mk (suc n)) rewrite +˘-identityˡ (mk n) = refl

H˘ : ∀ {n : ℕ˘} → n +˘ mk 0 ≡ n
H˘ = refl

H˘′ : ∀ {n : ℕ} → mk n +˘ mk 0 ≡ mk n
H˘′ = H˘

+↔+˘ : ∀ (x y : ℕ) → x + y ≡ (mk x +˘ mk y) .unmk
+↔+˘ zero y rewrite +˘-identityˡ (mk y) = refl
+↔+˘ (suc x) zero    = cong suc (Nat.+-identityʳ x)
+↔+˘ (suc x) (suc y) = cong suc (trans (Nat.+-suc x y) (+↔+˘ (suc x) y))

H : ∀ {n : ℕ} → n + 0 ≡ n
H = trans (+↔+˘ _ 0) (cong unmk H˘′)


--  : Hole → Tactic → TC ⊤
-- intro hole k = do
--   ty ← inferType hole
--   case ty of λ where
--     (pi argTy@(arg (arg-info v _) _) (abs x ty′)) → do
--       ctx ← getContext
--       hole′ ← inContext (argTy ∷ ctx) $ do
--         hole′ ← newMeta ty′
--         return hole′
--       unifyStrict (hole , ty) (lam v (abs "_" hole′))
--       extendContext argTy $ do
--         k hole′
--     _ → k hole

-- {-# TERMINATING #-}
-- intros : Hole → Tactic → TC ⊤
-- intros hole k = do
--   ty ← inferType hole
--   case ty of λ where
--     (pi argTy@(arg (arg-info v _) _) (abs _ ty′)) → do
--       ctx ← getContext
--       print $ "\t* " ◇ show argTy
--       printContext ctx
--       hole′ ← inContext (argTy ∷ ctx) $ do
--         hole′ ← newMeta ty′
--         return hole′
--       unifyStrict (hole , ty) (lam v (abs "_" hole′))
--       extendContext argTy $ do
--         intros hole′ k
--     _ → k hole

-- private
--   fillFromContext : Tactic
--   fillFromContext hole = do
--     ty ← inferType hole
--     ctx ← getContext
--     printContext ctx
--     let n = length ctx
--     let vs = applyUpTo ♯ n
--     unifyStricts (hole , ty) vs

--   macro
--     intro→fill : Tactic
--     intro→fill hole = do
--       print "***********************"
--       inferType hole >>= printS
--       print "***********************"
--       intro hole fillFromContext

--     intros→fill : Tactic
--     intros→fill hole = do
--       print "***********************"
--       inferType hole >>= printS
--       print "***********************"
--       intros hole fillFromContext

--   _ : ℕ → ℕ
--   _ = intro→fill

--   _ : ∀ (n : ℕ) → ℕ
--   _ = intro→fill

--   _ : ∀ {n : ℕ} → ℕ
--   _ = intro→fill

--   _ : ∀ ⦃ n : ℕ ⦄ → ℕ
--   _ = intro→fill

--   _ : Bool → Bool
--   _ = intro→fill

--   _ : ∀ (n : Bool) → Bool
--   _ = intro→fill

--   _ : ∀ {n : Bool} → Bool
--   _ = intro→fill

--   _ : ℕ → Bool → ℕ
--   _ = intros→fill

--   _ : Bool → ℕ → ℕ
--   _ = intros→fill

--   _ : (n : ℕ) → Bool → ℕ
--   _ = intros→fill

--   _ : ℕ → (b : Bool) → ℕ
--   _ = intros→fill

--   _ : (n : ℕ) (b : Bool) → ℕ
--   _ = intros→fill

--   _ : (n : ℕ) {b : Bool} → ℕ
--   _ = intros→fill

--   _ : {n : ℕ} {b : Bool} → ℕ
--   _ = intros→fill

--   _ : ∀ {n : Bool} → Bool
--   _ = intros→fill

--   _ : {n : ℕ} (b : Bool) → Bool
--   _ = intros→fill

--   _ : (n : ℕ) → Bool → Bool
--   _ = intros→fill

--   _ : {b : Bool} {n : ℕ} → ℕ
--   _ = intros→fill

--   _ : (b : Bool) {n : ℕ} → ℕ
--   _ = intros→fill

--   _ : ∀ {b : Bool} (n : ℕ) → ℕ
--   _ = intros→fill

--   _ : ∀ (b : Bool) (n : ℕ) → Bool
--   _ = intros→fill

--   open L.Mem

--   _ : ∀ {x : ℕ} {xs} → x ∈ xs → x ∈ xs
--   _ = intro→fill

--   _ : ∀ {x y : ℕ} {xs ys} → x ∈ xs → y ∈ ys → x ∈ xs
--   _ = intros→fill

--   _ : ∀ {x y : ℕ} {xs} → x ∈ xs → y ∈ xs → y ∈ xs
--   _ = intros→fill
