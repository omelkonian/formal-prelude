------------------------------------------------------------------------
-- General utilities
------------------------------------------------------------------------

module Prelude.General where

open import Data.Nat.Properties

open import Prelude.Init hiding (_⊆_; _⊈_)
open SetAsType
open Nat.Ord
open import Prelude.Applicative
open import Prelude.Functor
open import Prelude.Bifunctor

private variable
  A : Type ℓ₁
  B : Type ℓ₂
  x y x′ y′ : A
  xs ys : List A

-- ** Functions
infix -1 _`→`_ _↔_ _⇔_ _⊢_

_`→`_ : Op₂ Type
A `→` B = A → B

_↔_ : Type ℓ → Type ℓ′ → Type (ℓ ⊔ₗ ℓ′)
A ↔ B = (A → B) × (B → A)

_⇔_ : Type ℓ → Type ℓ′ → Type _
A ⇔ B = (A → B) × (B → A)

IdFun : ∀ {A : Type ℓ} → Pred (A → A) ℓ
IdFun f = ∀ x → f x ≡ x

IdFun-fmap : ∀ {f : A → A} → IdFun f → IdFun (M.map f)
IdFun-fmap f≗id = λ where
  nothing  → refl
  (just x) → cong just $ f≗id x

module _ {A : Type ℓ} {B : Pred A ℓ′} where
  implicitly : (∀ {x} → B x) → (∀ x → B x)
  implicitly f x = f {x}

  explicitly : (∀ x → B x) → (∀ {x} → B x)
  explicitly f {x} = f x

  automatically : (∀ ⦃ x ⦄ → B x) → (∀ x → B x)
  automatically f x = f ⦃ x ⦄

  manually : (∀ x → B x) → (∀ ⦃ x ⦄ → B x)
  manually f ⦃ x ⦄ = f x

-- ** Products
module _ {A : Type ℓ} {B : Type ℓ′} {C : Type ℓ″} {D : Type ℓ‴} where
  map×-injective : ∀ {f : A → B} {g : C → D}
    → Injective≡ f → Injective≡ g
    → Injective≡ (Product.map f g)
  map×-injective inj-f inj-g {_ , _} {_ , _} eq
    with eqˡ , eqʳ ← Product.,-injective eq
    rewrite inj-f eqˡ | inj-g eqʳ = refl

-- ** Equality

≗-sym : ∀ {f g : A → B} → f ≗ g → g ≗ f
≗-sym eq x rewrite eq x = refl

open import Prelude.SubstDSL public

-- ** Predicates

_⊢_ : ∀ {A : Type ℓ} → (A → Type ℓ′) → (A → Type ℓ″) → Type _
P ⊢ Q = ∀ {x} → P x → Q x

_⊣⊢_ : ∀ {A : Type ℓ} → (A → Type ℓ′) → (A → Type ℓ″) → Type _
P ⊣⊢ Q = (P ⊢ Q) × (Q ⊢ P)

module ⊢-Reasoning where
  -- Reasoning newtype (for better type inference).
  record ℝ⟨_⊢_⟩ {A : Type ℓ} (P Q : Pred A ℓ′) : Type (ℓ ⊔ₗ ℓ′) where
    constructor mkℝ_
    field begin_ : P ⊢ Q
    infix -2 begin_
  open ℝ⟨_⊢_⟩ public
  infix  -2 mkℝ_
  infixr -1 _⊢⟨_⟩_ _≡⟨_⟩_ _≗⟨_⟩_ _≡˘⟨_⟩_ _≗˘⟨_⟩_ _≡⟨⟩_
  infix  0  _∎

  private variable Q R : Pred A ℓ

  _⊢⟨_⟩_ : ∀ P → P ⊢ Q → ℝ⟨ Q ⊢ R ⟩ → ℝ⟨ P ⊢ R ⟩
  P ⊢⟨ P⊢Q ⟩ (mkℝ Q⊢R) = mkℝ (Q⊢R ∘ P⊢Q)

  _≡⟨_⟩_ : ∀ P → P ≡ Q → ℝ⟨ Q ⊢ R ⟩ → ℝ⟨ P ⊢ R ⟩
  _ ≡⟨ refl ⟩ p = p

  _≡⟨⟩_ : ∀ P → ℝ⟨ P ⊢ Q ⟩ → ℝ⟨ P ⊢ Q ⟩
  _ ≡⟨⟩ p = p

  _≡˘⟨_⟩_ : ∀ P → Q ≡ P → ℝ⟨ Q ⊢ R ⟩ → ℝ⟨ P ⊢ R ⟩
  P ≡˘⟨ eq ⟩ PlQ = P ≡⟨ sym eq ⟩ PlQ

  _≗⟨_⟩_ : ∀ P → P ≗ Q → ℝ⟨ Q ⊢ R ⟩ → ℝ⟨ P ⊢ R ⟩
  _ ≗⟨ eq ⟩ (mkℝ QlR) = mkℝ (QlR ∘ subst id (eq _))

  _≗˘⟨_⟩_ : ∀ P → Q ≗ P → ℝ⟨ Q ⊢ R ⟩ → ℝ⟨ P ⊢ R ⟩
  P ≗˘⟨ eq ⟩ PlQ = P ≗⟨ ≗-sym eq ⟩ PlQ

  _∎ : ∀ (P : Pred A ℓ) → ℝ⟨ P ⊢ P ⟩
  _∎ _ = mkℝ id

_Respects˘_ : Rel A ℓ → Pred A ℓ′ → Type _
_~_ Respects˘ P = ∀ {x y} → x ~ y → P x → P y

-- ** N-ary tuples
_^_ : Type ℓ → ℕ → Type ℓ
A ^ 0     = A
A ^ suc n = A × (A ^ n)

-- ** Bools

true⇒T : ∀ {b} → b ≡ true → T b
true⇒T refl = tt

T⇒true : ∀ {b} → T b → b ≡ true
T⇒true {true} tt = refl

false⇒T∘not : ∀ {b} → b ≡ false → T (not b)
false⇒T∘not refl = tt

T∘not⇒false : ∀ {b} → T (not b) → b ≡ false
T∘not⇒false {false} tt = refl

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

∸-suc : ∀ m n → n ≤ m → suc (m ∸ n) ≡ suc m ∸ n
∸-suc zero    zero    _         = refl
∸-suc (suc m) zero    _         = refl
∸-suc (suc m) (suc n) (s≤s n≤m) = ∸-suc m n n≤m

∸-∸-comm : ∀ m n o → (m ∸ n) ∸ o ≡ (m ∸ o) ∸ n
∸-∸-comm m n o rewrite Nat.∸-+-assoc m n o | Nat.+-comm n o | Nat.∸-+-assoc m o n = refl

+-reassoc : ∀ m n o → m + (n + o) ≡ n + (o + m)
+-reassoc m n o =
  begin
    m + (n + o)
  ≡⟨ Nat.+-comm m (n + o) ⟩
    (n + o) + m
  ≡⟨ Nat.+-assoc n o m ⟩
    n + (o + m)
  ∎ where open ≡-Reasoning

+-reassoc˘ : ∀ m n o → m + (n + o) ≡ n + (m + o)
+-reassoc˘ m n o =
  begin
    m + (n + o)
  ≡⟨ sym $ Nat.+-assoc m n o ⟩
    (m + n) + o
  ≡⟨ cong (_+ o) $ Nat.+-comm m n ⟩
    (n + m) + o
  ≡⟨ Nat.+-assoc n m o ⟩
    n + (m + o)
  ∎ where open ≡-Reasoning

∸-∸-assoc : ∀ m n o → n < m → o ≤ n → m ∸ (n ∸ o) ≡ (m ∸ n) + o
∸-∸-assoc m _       zero    _     _       = sym $ Nat.+-identityʳ _
∸-∸-assoc m (suc n) (suc o) 1+n<m (s≤s p)
  with n<m ← ≤-trans Nat.pred[n]≤n 1+n<m
  rewrite ∸-∸-assoc m n o n<m p | Nat.+-suc (m ∸ suc n) o =
  begin
    m ∸ n + o
  ≡⟨ cong (_+ o) $ sym $ Nat.suc[pred[n]]≡n $ Nat.m>n⇒m∸n≢0 n<m ⟩
    suc (Nat.pred (m ∸ n)) + o
  ≡⟨ cong (λ ◆ → suc (◆ + o)) $ Nat.pred[m∸n]≡m∸[1+n] m n ⟩
    suc (m ∸ suc n + o)
  ∎ where open ≡-Reasoning

x+y+0≡y+x+0 : ∀ x y → x + (y + 0) ≡ (y + x) + 0
x+y+0≡y+x+0 x y rewrite sym (+-assoc x y 0) | +-comm x y = refl

1+[m∸[1+n]]≡m∸n : ∀ m n → n < m → suc (m ∸ suc n) ≡ m ∸ n
1+[m∸[1+n]]≡m∸n m n = sym ∘ Nat.+-∸-assoc 1

m+z∸n+z≡m∸n : ∀ m n z → (m + z) ∸ (n + z) ≡ m ∸ n
m+z∸n+z≡m∸n m n zero rewrite Nat.+-identityʳ m | Nat.+-identityʳ n = refl
m+z∸n+z≡m∸n m n (suc z) rewrite Nat.+-suc m z | Nat.+-suc n z = m+z∸n+z≡m∸n m n z
m∸[z+o]∸n∸[w+o]≡[m∸z]∸[n∸w] : ∀ m n z o w → o ≤ n ∸ w →
  (m ∸ (z + o)) ∸ (n ∸ (w + o)) ≡ (m ∸ z) ∸ (n ∸ w)
m∸[z+o]∸n∸[w+o]≡[m∸z]∸[n∸w] m n z o w o≤
  rewrite sym $ Nat.∸-+-assoc m z o | sym $ Nat.∸-+-assoc n w o
  = begin
    (m ∸ z ∸ o) ∸ (n ∸ w ∸ o)
  ≡⟨⟩
    ((m ∸ z) ∸ o) ∸ ((n ∸ w) ∸ o)
  ≡⟨ ∸-∸-comm (m ∸ z) o ((n ∸ w) ∸ o) ⟩
    ((m ∸ z) ∸ ((n ∸ w) ∸ o)) ∸ o
  ≡⟨ Nat.∸-+-assoc (m ∸ z) ((n ∸ w) ∸ o) o ⟩
    (m ∸ z) ∸ (((n ∸ w) ∸ o) + o)
  ≡⟨ cong ((m ∸ z) ∸_) $ Nat.m∸n+n≡m {(n ∸ w)} {o} o≤ ⟩
    (m ∸ z) ∸ (n ∸ w)
  ∎ where open ≡-Reasoning

m≡n⇒m∸n≡0 : ∀ {m n} → m ≡ n → m ∸ n ≡ 0
m≡n⇒m∸n≡0 {m}{.m} refl = Nat.n∸n≡0 m

1+n∸n≡1 : ∀ n → 1 + n ∸ n ≡ 1
1+n∸n≡1 n = trans (Nat.+-∸-assoc 1 {n = n} Nat.≤-refl) (cong suc $ Nat.n∸n≡0 n)

m≡n⇒1+m∸n≡1 : ∀ {m n} → m ≡ n → 1 + m ∸ n ≡ 1
m≡n⇒1+m∸n≡1 {m}{.m} refl = 1+n∸n≡1 m

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

ap-nothing : ∀ {A : Type ℓ} {B : Type ℓ′} {r : B} {m : Maybe (A → B)} → (m <*> nothing) ≢ just r
ap-nothing {m = nothing} ()
ap-nothing {m = just _ } ()

Any-just : ∀ {x : A} {mx : Maybe A} {P : A → Type}
 → mx ≡ just x
 → M.Any.Any P mx
 → P x
Any-just refl (M.Any.just p) = p

Any⇒Is-just : ∀ {mx : Maybe A} {P : A → Type}
 → M.Any.Any P mx
 → Is-just mx
Any⇒Is-just {mx = .(just _)} (M.Any.just _) = M.Any.just tt

module _ {A : Type ℓ} where
  is-nothing? : Decidable¹ (T ∘ M.is-nothing {A = A})
  is-nothing? = T? ∘ M.is-nothing

  is-just? : Decidable¹ (T ∘ M.is-just {A = A})
  is-just? = T? ∘ M.is-just

  is-just≡ : ∀ {mx : Maybe A} → T (M.is-just mx) → ∃ λ x → mx ≡ just x
  is-just≡ {mx = just _} _ = -, refl

  ¬is-just≡ : ∀ {mx : Maybe A} → ¬ T (M.is-just mx) → mx ≡ nothing
  ¬is-just≡ {mx = just _}  p = ⊥-elim $ p tt
  ¬is-just≡ {mx = nothing} _ = refl

  Is-just? : (mx : Maybe A) → Dec (Is-just mx)
  Is-just? = M.Any.dec λ _ → yes tt

  Is-just⇒≢nothing : ∀ {mx : Maybe A} → Is-just mx → mx ≢ nothing
  Is-just⇒≢nothing {mx = nothing} () _
  Is-just⇒≢nothing {mx = just _} _ ()

  Is-nothing≡ : ∀ {mx : Maybe A} → Is-nothing mx → mx ≡ nothing
  Is-nothing≡ {mx = nothing} _ = refl
  Is-nothing≡ {mx = just _} (M.All.just ())

  ¬Is-just⇒Is-nothing : ∀ {mx : Maybe A} → ¬ Is-just mx → Is-nothing mx
  ¬Is-just⇒Is-nothing {mx = nothing} _ = M.All.nothing
  ¬Is-just⇒Is-nothing {mx = just _}  p = ⊥-elim $ p (M.Any.just tt)

  destruct-Is-just : ∀ {mx : Maybe A}
    → Is-just mx
    → ∃ λ x → mx ≡ just x
  destruct-Is-just {mx = nothing} ()
  destruct-Is-just {mx = just _}  _ = _ , refl

  MAll⇒¬MAny : ∀ {m : Maybe A} → M.All.All (const ⊥) m → ¬ M.Any.Any (const ⊤) m
  MAll⇒¬MAny {m = nothing} M.All.nothing ()

  mk-Is-just : ∀ {mx : Maybe A} {x : A} → mx ≡ just x → Is-just mx
  mk-Is-just refl = M.Any.just tt

-- ** Deriving relations from more primitive ones.
module Derive-⊆-from-∈ {A : Type ℓ} {B : Type ℓ′} (_∈_ : A → B → Type ℓ″) where
  infix 4 _⊆_ _⊈_
  _⊆_ _⊈_ _⊇_ _⊉_ : Rel B _
  b ⊆ b′ = ∀ {a} → a ∈ b → a ∈ b′
  b ⊈ b′ = ¬ b ⊆ b′
  b ⊇ b′ = b′ ⊆ b
  b ⊉ b′ = ¬ b ⊇ b′

  ⊆-trans : Transitive _⊆_
  ⊆-trans ij jk = jk ∘ ij

  ⊇-trans : Transitive _⊇_
  ⊇-trans = flip ⊆-trans

-- ** Lists

[]-injective : [ x ] ≡ [ y ] → x ≡ y
[]-injective refl = refl

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

filter-singleton : ∀ {P : A → Type} {P? : Decidable¹ P} {px : P x}
  → P? x ≡ yes px
  → filter P? [ x ] ≡ [ x ]
filter-singleton {P? = P?} p rewrite p = refl

case-singleton : ∀ {x xs} {f : A → B} {g : B}
  → xs ≡ [ x ]
  → (case xs of λ{ (x′ ∷ []) → f x′
                 ; _         → g }) ≡ f x
case-singleton refl = refl

-- ** Singleton types
data Is {A : Type ℓ} : A → Type ℓ where
  ⟫_ : (x : A) → Is x
infix -100 ⟫_

-- NB: can be used to pattern match on module parameters
private module _ (n : ℕ) where
  f : (n ≡ 0) ⊎ (∃ λ n′ → n ≡ suc n′)
  f with ⟫ n
  ... | ⟫ 0     = inj₁ refl
  ... | ⟫ suc _ = inj₂ $ -, refl


-- ** ω-level

itω : ∀ {A : Typeω} → ⦃ A ⦄ → A
itω ⦃ x ⦄ = x

_∋ω_ : (A : Typeω) → A → A
_ ∋ω x = x

-- ** Testing

-- single case
_ = ∃ (_≤ 3)
  ∋ 3 , ≤-refl

-- syntactic sugar for giving multiple terms of the same type
module MultiTest where
  -- only the first is actually returned, but all are type-checked
  _∋⋮_ : (A : Type ℓ) → List⁺ A → A
  _∋⋮_ _ (x ∷ _) = x
  pattern _⋮_ x xs = x L.NE.∷ xs
  pattern _⋮_ x xs = x ∷ xs
  pattern _⋮∅ x = x ∷ []
  infixl -10 _∋⋮_
  infixr -9  _⋮_
  infix  -8  _⋮∅

  _ = ∃ (_≤ 3)
   ∋⋮ 3 , ≤-refl
    ⋮ 2 , ≤-step ≤-refl
    ⋮ 1 , ≤-step (≤-step ≤-refl)
    ⋮ 0 , ≤-step (≤-step (≤-step ≤-refl))
    ⋮∅

-- ** Strings

String∗ = List Char

apply∗ : (String∗ → String∗) → (String → String)
apply∗ f = Str.fromList ∘ f ∘ Str.toList

{-# TERMINATING #-}
words∗ : String∗ → List (String∗ × String∗)
words∗ [] = []
words∗ s  =
  let
    ws , s′ = L.span (T? ∘ Ch.isSpace) s
    w , s″ = L.span (T? ∘ not ∘ Ch.isSpace) s′
  in
    (ws , w) ∷ words∗ s″
words = map (map₁₂ Str.fromList) ∘ words∗ ∘ Str.toList

unwords∗ : List (String∗ × String∗) → String∗
unwords∗ = concatMap (uncurry _++_)

_ : words "a horse  and a    sheep" ≡
  ( ("" , "a")
  ∷ (" " , "horse")
  ∷ ("  " , "and")
  ∷ (" " , "a")
  ∷ ("    " , "sheep")
  ∷ [])
_ = refl

mapWords∗ : (String∗ → String∗) → String∗ → String∗
mapWords∗ f = unwords∗ ∘ map (map₂ f) ∘ words∗

mapWords : (String∗ → String∗) → String → String
mapWords = apply∗ ∘ mapWords∗

removeQualifiers∗ : String∗ → String∗
removeQualifiers∗ = L.reverse ∘ go ∘ L.reverse
  where
    go : String∗ → String∗
    go s = case takeWhile (¬? ∘ ('.' Ch.≟_)) s of λ where
      []         → s
      s′@(_ ∷ _) → s′

removeQualifiers : String → String
removeQualifiers = mapWords removeQualifiers∗

_ : removeQualifiers "open import Agda.Builtin.Char public -- hmm..."
  ≡ "open import Char public -- hmm..."
_ = refl
