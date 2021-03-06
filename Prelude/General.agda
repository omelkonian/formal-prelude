------------------------------------------------------------------------
-- General utilities
------------------------------------------------------------------------

module Prelude.General where

open import Data.Nat.Properties
import Data.Maybe.Relation.Unary.Any as M

open import Prelude.Init
open import Prelude.Applicative
open import Prelude.Monad

private
  variable
    A : Set ℓ₁
    B : Set ℓ₂
    x y x′ y′ : A
    xs ys : List A

-- ** Functions and predicates
infix -1 _`→`_ _↔_ _⇔_ _⊢_

_`→`_ : Op₂ Set
A `→` B = A → B

_↔_ : Set ℓ → Set ℓ′ → Set (ℓ ⊔ₗ ℓ′)
A ↔ B = (A → B) × (B → A)

_⇔_ : Set ℓ → Set ℓ′ → Set _
A ⇔ B = (A → B) × (B → A)

_⊢_ : ∀ {A : Set ℓ} → (A → Set ℓ′) → (A → Set ℓ″) → Set _
P ⊢ Q = ∀ {x} → P x → Q x

_⊣⊢_ : ∀ {A : Set ℓ} → (A → Set ℓ′) → (A → Set ℓ″) → Set _
P ⊣⊢ Q = (P ⊢ Q) × (Q ⊢ P)

-- ** Equality

-- forward
substˡ = subst
substˡ′ = substˡ
infixl 4 substˡ″
substˡ″ : {P : Pred₀ A} → x ≡ y → P x → P y
substˡ″ = substˡ _
syntax substˡ  (λ ◆ → P) eq p = p :~ eq ⟪ ◆ ∣ P ⟫
syntax substˡ′ P         eq p = p :~ eq ⟪ P ⟫
syntax substˡ″           eq p = p :~ eq

-- backward
substʳ : (P : Pred₀ A) → y ≡ x → P x → P y
substʳ P eq p = subst P (sym eq) p
substʳ′ = substʳ
substʳ″ : {P : Pred₀ A} → y ≡ x → P x → P y
substʳ″ = substʳ _
infixl 4 substʳ″
syntax substʳ  (λ ◆ → P) eq p = ⟪ ◆ ∣ P ⟫ eq ~: p
syntax substʳ′ P         eq p =     ⟪ P ⟫ eq ~: p
syntax substʳ″           eq p =           eq ~: p

-- [T0D0] macro that automagically finds which context P to use


private
  postulate
    n m : ℕ
    n≡m : n ≡ m
    P : Pred₀ ℕ
    pₙ : P n
    pₘ : P m
    p : P m × P n
    p₇ : P 7

  -- backward
  _ : P n
  _ = ⟪ P ⟫ n≡m ~: pₘ

  -- forward
  _ : P m
  _ = pₙ :~ n≡m ⟪ P ⟫

  -- backward chain
  _ : P (n + 0) × P (0 + m)
  _ = ⟪ ◆ ∣ P ◆ × P (0 + m) ⟫ +-identityʳ _ ~:
      ⟪ ◆ ∣ P ◆ × P (0 + m) ⟫ n≡m           ~:
      ⟪ ◆ ∣ P m × P ◆       ⟫ +-identityˡ _ ~:
      ⟪ ◆ ∣ P m × P ◆       ⟫ sym n≡m       ~: p

  -- forward chain
  _ : P (n + 0) × P (0 + m)
  _ = p :~ n≡m                 ⟪ ◆ ∣ P m × P ◆       ⟫
        :~ sym (+-identityˡ _) ⟪ ◆ ∣ P m × P ◆       ⟫
        :~ sym n≡m             ⟪ ◆ ∣ P ◆ × P (0 + m) ⟫
        :~ sym (+-identityʳ _) ⟪ ◆ ∣ P ◆ × P (0 + m) ⟫

-- ** N-ary tuples
_^_ : Set ℓ → ℕ → Set ℓ
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

open Nat.Ord
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
  juxtapose-+/< : x < x′ → y < y′ → x + y < x′ + y′

x≤0⇒x≡0′ : ∀ {n m} → n ≡ 0 → m ≤ n → m ≡ 0
x≤0⇒x≡0′ refl = x≤0⇒x≡0

≥-trans : Transitive _≥_
≥-trans x≥y y≥z = ≤-trans y≥z x≥y

-- ** Maybes

toMaybe : List A → Maybe A
toMaybe []      = nothing
toMaybe (x ∷ _) = just x

toMaybe-≡ : ∀ {x : A} {xs : List A}
  → toMaybe xs ≡ just x
  → ∃[ ys ] (xs ≡ x ∷ ys)
toMaybe-≡ {xs = _ ∷ _} refl = _ , refl

ap-nothing : ∀ {B : Set ℓ₂} {r : B} {m : Maybe (A → B)} → (m <*> nothing) ≢ just r
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

Is-here : ∀ {A : Set} {P : Pred₀ A} {xs : List A} → Any P xs → Set
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

MAll⇒¬MAny : ∀ {m : Maybe A} → M.All.All (const ⊥) m → ¬ M.Any.Any (const ⊤) m
MAll⇒¬MAny {m = nothing} M.All.nothing ()

-- ** Decidable

≟-refl : ∀ {A : Set} (_≟_ : Decidable² {A = A} _≡_) (x : A)
  → x ≟ x ≡ yes refl
≟-refl _≟_ x with x ≟ x
... | no ¬p    = ⊥-elim (¬p refl)
... | yes refl = refl

-- ** Lists

sequence : List (Maybe A) → Maybe (List A)
sequence = foldr (λ c cs → ⦇ c ∷ cs ⦈) (just [])

open L.Mem using (_∈_)

singleton→∈ : ∃[ ys ] (xs ≡ x ∷ ys) → x ∈ xs
singleton→∈ (_ , refl) = here refl

mapWith∈⁺ : ∀ {x xs} {f : ∀ {x : A} → x ∈ xs → B}
  → (x∈ : x ∈ xs)
  → ∃[ y ] ( (y ∈ L.Mem.mapWith∈ xs f) × (f {x} x∈ ≡ y) )
mapWith∈⁺ {x = x} {xs = []}      ()
mapWith∈⁺ {x = x} {xs = .x ∷ xs} (here refl) = (_ , here refl , refl)
mapWith∈⁺ {x = x} {xs = x′ ∷ xs} (there x∈) with mapWith∈⁺ x∈
... | y , y∈ , refl = y , there y∈ , refl

filter-singleton : ∀ {P : A → Set} {P? : Decidable¹ P} {px : P x}
  → P? x ≡ yes px
  → filter P? [ x ] ≡ [ x ]
filter-singleton {P? = P?} p rewrite p = refl

case-singleton : ∀ {x xs} {f : A → B} {g : B}
  → xs ≡ [ x ]
  → (case xs of λ{ (x′ ∷ []) → f x′
                 ; _         → g }) ≡ f x
case-singleton refl = refl

-- ** Maybe-Bool

do-pure : ∀ {x : A} {mx : Maybe A} {f : A → Bool}
  → mx ≡ just x
  → f x ≡ true
  → M.fromMaybe false (mx >>= pure ∘ f) ≡ true
do-pure refl f≡ rewrite f≡ = refl
