open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Default
open import Prelude.Set'

module Prelude.Map' {K V : Set} {{_ : DecEq K}} where

_↦_ : Set⟨ K ⟩ → Set → Set
ks ↦ V = ∀ {k} → k ∈′ ks → V

map↦ = _↦_
syntax map↦ ks (λ k → f) = ∀[ k ∈ ks ] f

dom′ : ∀ {ks} → ks ↦ V → Set⟨ K ⟩
dom′ {ks = ks} _ = ks

codom′ : ∀ {ks} → ks ↦ V → List V
codom′ = mapWith∈ _

weaken-↦ : ∀ {ks ys} → ks ↦ V → ys ⊆′ ks → ys ↦ V
weaken-↦ f ys⊆ks = f ∘ ys⊆ks

-- extend-↦ : ∀ {ks ys zs : List K}
--   → zs ↭ ks ++ ys
--   → ks ↦′ P
--   → ys ↦′ P
--   → zs ↦′ P
-- extend-↦ zs↭ ks↦ ys↦ p∈ with ∈-++⁻ _ (∈-resp-↭ zs↭ p∈)
-- ... | inj₁ k∈ = ks↦ k∈
-- ... | inj₂ y∈ = ys↦ y∈

Map' : Set
Map' = ∃ (_↦ V)

dom : Map' → Set⟨ K ⟩
dom = proj₁

codom : Map' → List V
codom (ks , m) = codom′ {ks} m

lookup : ∀ {k} → (m : Map') → k ∈′ dom m → V
lookup (_ , k↦) k∈ = k↦ k∈

lookup′ : Map' → K → Maybe V
lookup′ m k with k ∈′? dom m
... | yes k∈ = just (lookup m k∈)
... | no  _  = nothing

update : Map' → K → (V → V) → Map'
update m@(ks , k↦) k′ f = ks , λ {k} → (if k == k′ then f else (λ x → x)) ∘ k↦

update-const : ∀ {m k f} → dom m ≡ dom (update m k f)
update-const = refl

updateWith : Map' → K → V → (V → V) → Map'
updateWith m@(ks , k↦) k k-def f with k ∈′? ks
... | yes k∈ = ks           , f ∘ k↦
... | no  k∉ = k ∷ ks ∶- k∉ , λ{ (here refl) → f k-def; (there k∈′) → k↦ k∈′ }

-- we get extra utilities if we can get a default value when there is no entry for a particular key
module _ {{_ : Default V}} where
  update-with-def : Map' → K → (V → V) → Map'
  update-with-def m k f = updateWith m k def f

union : Map' → Map' → Map'
union (xs , X) (ys , Y) = (xs ∪ ys) , X∪Y
  where
    X∪Y : (xs ∪ ys) ↦ V
    X∪Y xy∈ with ∈-∪ {xs = xs} {ys = ys} xy∈
    ... | inj₁ x∈ = X x∈
    ... | inj₂ y∈ = Y y∈

_≡ᵐ_ : Map' → Map' → Set
m ≡ᵐ m′ = (dom m ≡ dom m′) × (codom m ≡ codom m′)

postulate
  union-comm : ∀ {m m′} → union m m′ ≡ᵐ union m′ m
  ≡ᵐ-trans : ∀ {m m′ m″} → m ≡ᵐ m′ → m′ ≡ᵐ m″ → m ≡ᵐ m″
-- union-comm {m = xs , X} {m′ = ys , Y}
--   with _ , X∪Y ← union (xs , X) (ys , Y)
--   with _ , Y∪X ← union (ys , Y) (xs , X)
--   rewrite ∪-comm {xs = xs}{ys}
--     = refl , p
--     where
--       p : codom (_ , X∪Y) ≡ codom (_ , Y∪X)
--       p = ?

-- update-comm : ∀ {m k f k′ f′}
--   → [T0D0] f ∘ f' = f' ∘ f
--   → update (update m k f) k′ f′
--   ≡ update (update m k′ f′) k f
-- update-comm {m@(ks , k↦)}{k}{f}{k′}{f′}
--   with k ∈′? ks | k′ ∈′? ks
-- ... | yes k∈ | yes k∈′ = {!!}
-- ... | yes k∈ | no  k∉′ = {!!}
-- ... | no  k∉ | yes k∈′ = {!!}
-- ... | no  k∉ | no  k∉′ = {!!}


-- update m k f
-- m ∥ k ≔ f
-- m

-- update : ∀ {K V : Set} {{_ : DecEq K}} {ks : List K} {k : K}
--   → ks ↦ V
--   → (k ∈ ks) × (V → V)
--   → ks ↦ V
-- update {k = k} m (k∈ , f) {k′} k∈′
--   with v ← m k∈′
--   with k ≟ k′
-- ... | yes refl = f v
-- ... | no  ¬p   = v

-- updateˢ : S → Part × ℤ × (ℤ → ℤ) → S
-- updateˢ (ps , s) (p , pz , f)
--   with p ∈? ps
-- ... | yes p∈ = _ , update s (p∈ , f)
-- ... | no  p∉ = p ∷ ps , s′
--   where
--     s′ : (p ∷ ps) ↦ ℤ
--     s′ (here refl) = f pz
--     s′ (there p∈′) = s p∈′

-- update : ∀ {K V : Set} {xs : List K}
--   → ∃ (
--   → K
--   → (V → V)
--   → ∃ (_↦ V)
-- update {K}{V}{xs} (xs , f) x mod
--   with x ∈ xs
-- ... | yes x∈ = f x∈
-- ... | no  x∉ =

-----------------------------------------------------
-- Syntactic sugar
syntax Map' {K = K} {V = V} = Map⟨ K ↦ V ⟩
