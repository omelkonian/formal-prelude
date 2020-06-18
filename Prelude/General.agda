------------------------------------------------------------------------
-- General utilities
------------------------------------------------------------------------

module Prelude.General where

open import Level          using (0ℓ)
open import Function       using (case_of_)
open import Category.Monad using (RawMonad)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.Bool    using (Bool; true; false; T ; _∧_; if_then_else_)
open import Data.Nat
  hiding (_^_)
open import Data.Nat.Properties
open import Data.Maybe   using (Maybe; just; nothing; fromMaybe; Is-just)
open import Data.List    using (List; []; _∷_; [_]; foldr; filter)


import Data.Maybe.Relation.Unary.Any as M
import Data.Maybe.Categorical as MaybeCat
open RawMonad {f = 0ℓ} MaybeCat.monad renaming (_⊛_ to _<*>_)

open import Data.List.Membership.Propositional using (_∈_; mapWith∈)
open import Data.List.Relation.Unary.Any       using (here; there)

open import Relation.Nullary           using (yes; no; does; ¬_)
open import Relation.Nullary.Decidable using (isYes≗does)
import Relation.Unary  as Un
import Relation.Binary as Bi
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)

private
  variable
    A B : Set
    x : A
    xs : List A

-- ** N-ary tuples
_^_ : Set → ℕ → Set
A ^ 0     = A
A ^ suc n = A × (A ^ n)

-- ** Bools

true⇒T : ∀ {b} → b ≡ true → T b
true⇒T refl = tt

T⇒true : ∀ {b} → T b → b ≡ true
T⇒true {true}  tt = refl
T⇒true {false} ()

⊥-bool : ∀ {b} → ¬ ((b ≡ true) × (b ≡ false))
⊥-bool (refl , ())

T-∧ : ∀ {l r} → T (l ∧ r) → T l × T r
T-∧ {true} {true} _ = tt , tt

∧-falseˡ : ∀ {r} → ¬ (T (false ∧ r))
∧-falseˡ {r = true}  ()
∧-falseˡ {r = false} ()

∧-falseʳ : ∀ {l} → ¬ (T (l ∧ false))
∧-falseʳ {l = true}  ()
∧-falseʳ {l = false} ()

∧-falseʳ² : ∀ {x y} → ¬ (T (x ∧ (y ∧ false)))
∧-falseʳ² {x = true}  {y = true}  ()
∧-falseʳ² {x = true}  {y = false} ()
∧-falseʳ² {x = false} {y = true}  ()
∧-falseʳ² {x = false} {y = false} ()

if-true : ∀ {b} {t f : A}
  → b ≡ true
  → (if b then t else f) ≡ t
if-true refl = refl

if-false : ∀ {b} {t f : A}
  → b ≡ false
  → (if b then t else f) ≡ f
if-false refl = refl

infixr 6 _∧-×_
_∧-×_ : ∀ {x y}
  → x ≡ true
  → y ≡ true
  → x ∧ y ≡ true
refl ∧-× refl = refl

-- ** Nats

x+y+0≡y+x+0 : ∀ x y → x + (y + 0) ≡ (y + x) + 0
x+y+0≡y+x+0 x y rewrite sym (+-assoc x y 0) | +-comm x y = refl

postulate
  ¬x>0⇒x≡0 : ∀ {x} → ¬ (x > 0) → x ≡ 0
  x≡0⇒¬x>0 : ∀ {x} → x ≡ 0 → ¬ (x > 0)
  x≤0⇒x≡0 : ∀ {x} → x ≤ 0 → x ≡ 0
  x>0,x≤1⇒x≡1 : ∀ {x} → x > 0 → x ≤ 1 → x ≡ 1
  ≤-+ˡ : ∀ {x y z} → x + y ≤ z → x ≤ z
  ≤-+ʳ : ∀ {x y z} → x + y ≤ z → y ≤ z
  x+y≤y⇒x≡0 : ∀ {x y} → x + y ≤ y → x ≡ 0
  ¬>⇒≤ : ∀ {m n} → ¬ (m > n) → m ≤ n
  x+y>x⇒y>0 : ∀ {x y} → x + y > x → y > 0
  ≥-+-swapˡ : ∀ {x x′ y} → x ≥ x′ → x + y ≥ x′ + y
  ≥-+-swapʳ : ∀ {x y y′} → y ≥ y′ → x + y ≥ x + y′
  ≥-+-swapˡʳ : ∀ {x y x′ y′} → x ≥ x′ → y ≥ y′ → x + y ≥ x′ + y′
  ¬i≥x+y : ∀ {i x y} → i ≤ 1 → x > 0 → y > 0 → ¬ (i ≥ x + y)
  x<x+1 : ∀ x → x < x + 1
  +-helper : ∀ {x y z} → x ≡ y + z → y > 0 → z > 0 → (y < x) × (z < x)
  x<x+y : ∀ {y} x → y > 0 → x < x + y

x≤0⇒x≡0′ : ∀ {n m} → n ≡ 0 → m ≤ n → m ≡ 0
x≤0⇒x≡0′ refl = x≤0⇒x≡0

≥-trans : Bi.Transitive _≥_
≥-trans x≥y y≥z = ≤-trans y≥z x≥y

-- ** Maybes

toMaybe : List A → Maybe A
toMaybe []      = nothing
toMaybe (x ∷ _) = just x

toMaybe-≡ : ∀ {x : A} {xs : List A}
  → toMaybe xs ≡ just x
  → ∃[ ys ] (xs ≡ x ∷ ys)
toMaybe-≡ {xs = _ ∷ _} refl = _ , refl

ap-nothing : ∀ {r : B} {m : Maybe (A → B)} → (m <*> nothing) ≢ just r
ap-nothing {m = nothing} ()
ap-nothing {m = just _ } ()

Any-just : ∀ {x : A} {mx : Maybe A} {P : A → Set}
 → mx ≡ just x
 → M.Any P mx
 → P x
Any-just refl (M.just p) = p

Any⇒Is-just : ∀ {mx : Maybe A} {P : A → Set}
 → M.Any P mx
 → Is-just mx
Any⇒Is-just {mx = .(just _)} (M.just _) = M.just tt

Is-here : ∀ {A : Set} {x : A} {xs : List A} → x ∈ xs → Set
Is-here (here _)  = ⊤
Is-here (there _) = ⊥

Is-just⇒≢nothing : ∀ {A : Set} {mx : Maybe A} → Is-just mx → mx ≢ nothing
Is-just⇒≢nothing {mx = nothing} () _
Is-just⇒≢nothing {mx = just _} _ ()

destruct-Is-just : ∀ {A : Set} {mx : Maybe A}
  → Is-just mx
  → ∃ λ x → mx ≡ just x
destruct-Is-just {mx = nothing} ()
destruct-Is-just {mx = just _}  _ = _ , refl

-- ** Decidable

≟-refl : ∀ {A : Set} (_≟_ : Bi.Decidable {A = A} _≡_) (x : A)
  → x ≟ x ≡ yes refl
≟-refl _≟_ x with x ≟ x
... | no ¬p    = ⊥-elim (¬p refl)
... | yes refl = refl

-- ** Lists

sequence : List (Maybe A) → Maybe (List A)
sequence = foldr (λ c cs → ⦇ c ∷ cs ⦈) (just [])

singleton→∈ : ∃[ ys ] (xs ≡ x ∷ ys)
            → x ∈ xs
singleton→∈ (_ , refl) = here refl

mapWith∈⁺ : ∀ {x xs} {f : ∀ {x : A} → x ∈ xs → B}
  → (x∈ : x ∈ xs)
  → ∃[ y ] ( (y ∈ mapWith∈ xs f) × (f {x} x∈ ≡ y) )
mapWith∈⁺ {x = x} {xs = []}      ()
mapWith∈⁺ {x = x} {xs = .x ∷ xs} (here refl) = (_ , here refl , refl)
mapWith∈⁺ {x = x} {xs = x′ ∷ xs} (there x∈) with mapWith∈⁺ x∈
... | y , y∈ , refl = y , there y∈ , refl

filter-singleton : ∀ {P : A → Set} {P? : Un.Decidable P} {px : P x}
  → P? x ≡ yes px
  → filter P? [ x ] ≡ [ x ]
filter-singleton {P? = P?} p rewrite p = refl -- (trans (sym (isYes≗does (P? _))) p) = refl

case-singleton : ∀ {x xs} {f : A → B} {g : B}
  → xs ≡ [ x ]
  → (case xs of λ{ (x′ ∷ []) → f x′
                 ; _         → g }) ≡ f x
case-singleton refl = refl

-- ** Maybe-Bool

do-pure : ∀ {x : A} {mx : Maybe A} {f : A → Bool}
  → mx ≡ just x
  → f x ≡ true
  → (fromMaybe false do x ← mx
                        pure (f x)) ≡ true
do-pure refl f≡ rewrite f≡ = refl
