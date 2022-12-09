{-# OPTIONS -v ord:100 #-}
module Prelude.Ord.Derive where

open import Prelude.Init
open import Prelude.Decidable
open import Prelude.DecEq
open import Prelude.Monad
open import Prelude.Semigroup
open import Prelude.Show
open import Prelude.ToN
open import Prelude.Lists
open import Prelude.Functor
open import Prelude.Bifunctor
open import Prelude.Applicative
open import Prelude.Nary
open import Prelude.Lift

open Meta
open import Prelude.Generics
open Debug ("ord" , 100)

open import Prelude.Ord.Core
open import Prelude.Ord.Dec
open import Prelude.Ord.Instances
open import Prelude.Ord.List

private
  variable A : Set ℓ

  pattern `⊤ = quote ⊤ ∙
  pattern `yes x = quote _because_ ◆⟦ quote true ◆  ∣ quote ofʸ ◆⟦ x ⟧ ⟧
  pattern `yes-tt = `yes (quote tt ◆)
  pattern `⊥ = quote ⊥ ∙
  pattern `no x = quote _because_ ◆⟦ quote false ◆ ∣ quote ofⁿ ◆⟦ x ⟧ ⟧
  pattern `no-⊥ = `no `λ⦅ (("_" , vArg unknown) ∷ []) ⦆∅
  pattern _`≡_ x y = quote _≡_ ∙⟦ x ∣ y ⟧
  pattern _`≟_ x y = quote _≟_ ∙⟦ x ∣ y ⟧
  pattern _`⊎_ x y = quote _⊎_ ∙⟦ x ∣ y ⟧
  pattern _`⊎-dec_ x y = quote _⊎-dec_ ∙⟦ x ∣ y ⟧
  pattern _`×_ x y = quote _×_ ∙⟦ x ∣ y ⟧
  pattern _`×-dec_ x y = quote _×-dec_ ∙⟦ x ∣ y ⟧
  pattern _`<_ x y = quote _<_ ∙⟦ x ∣ y ⟧
  pattern _`<?_ x y = quote _<?_ ∙⟦ x ∣ y ⟧

  removeExtra⊥ `toDec : Op₁ Term
  removeExtra⊥ = λ where
    (x `⊎ `⊥) → x
    (`⊥ `⊎ x) → x
    (x `× `⊥) → `⊥
    (`⊥ `× _) → `⊥
    t → t
  {-# TERMINATING #-}
  `toDec = λ where
    (lam v (abs s t)) → lam v (abs s (`toDec t))
    (pat-lam cs []) → pat-lam (map go cs) []
    (x `⊎ y) → `toDec x `⊎-dec `toDec y
    (x `× y) → `toDec x `×-dec `toDec y
    (x `≡ y) → `toDec x `≟ `toDec y
    (x `< y) → `toDec x `<? `toDec y
    `⊥       → `no-⊥
    `⊤       → `yes-tt
    t        → t
   where go = λ where
    (clause tel as e) → clause tel as (`toDec e)
    c → c

  deriveOrd : Name → Definition → TC Term
  deriveOrd tyn d with d
  ... | data-type ps cs = do
    print $ "DATATYPE {pars = " ◇ show ps ◇ "; cs = " ◇ show cs ◇ "}"
    cs′ ← concatMapM mkClause (map₁ toℕ <$> enumerate cs)
    return $ pat-lam cs′ []
    where
      module _ (N : ℕ) where
        constructLex< : ℕ → Term
        constructLex< = λ where
          0 → `⊥
          (suc n) →
            let i = N ∸ n ∸ 1
                x = ♯ i; y  = ♯ (i + N)
                x< = x `< y
                x≡ = x `≡ y
            in removeExtra⊥ (x< `⊎ removeExtra⊥ (x≡ `× constructLex< n))

      mkClause : ℕ × Name → TC (List Clause)
      mkClause (i , cn) = do
        print $ "Making pattern clauses for constructor: " ◇ show cn
        tys , N , _ , pc ← mkPattern 0 cn
        let mkTel = flip L.replicate ("_" , vArg unknown)
        cls< ← forM (take i cs) λ cn′ → do
          tys′ , N′ , _ , pc′ ← mkPattern 0 cn′
          return $ clause (mkTel $ N + N′) (vArg <$> (pc ∷ mapVariables (_+ N) pc′ ∷ [])) `⊥
        let cl≡ = clause (mkTel $ N + N)
                        (vArg <$> (pc ∷ mapVariables (_+ N) pc ∷ []))
                        (constructLex< N N)
        cls> ← forM (drop (suc i) cs) λ cn′ → do
          tys′ , N′ , _ , pc′ ← mkPattern 0 cn′
          return $ clause (mkTel $ N + N′) (vArg <$> (pc ∷ mapVariables (_+ N) pc′ ∷ [])) `⊤
        return $ cls< ++ cl≡ ∷ cls>
  ... | record-type rn fs = do
    print $ "RECORD {name = " ◇ show rn ◇ "; fs = " ◇ show fs ◇ "}"
    return `λ⟦ "r" ∣ "r′" ⇒ constructLex< (vArgs fs) ⟧
    where
      N = length fs
      ♯r = ♯ 1; ♯r′ = ♯ 0

      constructLex< : List Name → Term
      constructLex< = λ where
        [] → `⊥
        (fn ∷ fs) →
          let x = fn ∙⟦ ♯r ⟧; y = fn ∙⟦ ♯r′ ⟧
              x< = x `< y
              x≡ = x `≡ y
          in
            removeExtra⊥ $ x< `⊎ (x≡ `× removeExtra⊥ (constructLex< fs))
  ... | function cs = do
    print $ "FUNCTION {cs = " ◇ show cs ◇ "}"
    error  "[not supported] functions"
  ... | data-cons _ = error "[not supported] data constructors"
  ... | axiom       = error "[not supported] axioms or mutual definitions"
  ... | prim-fun    = error "[not supported] primitive functions"

instance
  Derivable-Ord : Derivable↑ Ord
  Derivable-Ord .DERIVE↑' args = do
    (n , f) ∷ [] ← return args
      where _ → error "[not supported] mutual types"
    print "********************************************************"
    print $ "Deriving " ◇ parens (show f ◇ " : Ord " ◇ show n)
    ord ← deriveOrd n =<< getDefinition n
    genSimpleInstance f
      (quote Ord ∙⟦ n ∙ ⟧)
      (quote mkOrd< ∙⟦ ord ⟧)
    print "********************************************************"

DERIVE-DecOrd : Derivation
DERIVE-DecOrd args = do
  (n , dec-f) ∷ [] ← return args
    where _ → error "[not supported] mutual types"
  print "********************************************************"
  print $ "Deriving " ◇ parens (show dec-f ◇ " : DecOrd " ◇ show n)
  ord ← deriveOrd n =<< getDefinition n
  let decOrd = `toDec ord
  genSimpleInstance dec-f
    (quote DecOrd ∙⟦ n ∙ ⟧)
    (quote mkDecOrd< ∙⟦ decOrd ⟧)
  print "********************************************************"

-- derive everything (+ postulate Ord laws)
DERIVE-Ord : List (Name × Name × Name × Name) → TC ⊤
DERIVE-Ord args = do
  (n , f , dec-f , laws-f) ∷ [] ← return args
    where _ → error "[not supported] mutual types"
  print "********************************************************"
  print $ "Deriving " ◇ parens (show f ◇ " : Ord " ◇ show n)
  print $ "Deriving " ◇ parens (show dec-f ◇ " : DecOrd " ◇ show n)
  ord ← deriveOrd n =<< getDefinition n
  genSimpleInstance f
    (quote Ord ∙⟦ n ∙ ⟧)
    (quote mkOrd< ∙⟦ ord ⟧)
  let decOrd = `toDec ord
  genSimpleInstance dec-f
    (quote DecOrd ∙⟦ n ∙ ⟧)
    (quote mkDecOrd< ∙⟦ decOrd ⟧)
  declarePostulate (iArg laws-f)
    (quote OrdLaws ∙⟦ n ∙ ⟧)
  print "********************************************************"

private
  data X : Set where
    ∅ : X
    c₁ : ℕ → X
    c₂ : ℕ → ℤ → X
    _⊚_ : X → X → X
    ∗_ : List X → X
  {-# TERMINATING #-}
  unquoteDecl DecEq-X = DERIVE DecEq [ quote X , DecEq-X ]
  {-# TERMINATING #-}
  unquoteDecl Ord-X DecOrd-X OrdLaws-X = DERIVE-Ord [ quote X , Ord-X , DecOrd-X , OrdLaws-X ]

  pattern ≪_ x = inj₁ x
  pattern ≫_ x = inj₂ (refl , x)
  pattern ≪⊥ = ≪ ()
  pattern ≫⊥ = ≫ ()
  open Integer using (0ℤ; 1ℤ; +<+)
  pattern 0<1 = s≤s z≤n

  _ = ∅ ≮ ∅
    ∋ λ ()
  _ = ∅ ≤ ∅
    ∋ ≪ refl
  _ = ∅ < c₁ 0
    ∋ tt
  _ = ∅ < c₁ 0
    ∋ tt
  _ = ∅ < c₂ 0 0ℤ
    ∋ tt
  _ = ∅ < (∅ ⊚ ∅)
    ∋ tt
  _ = ∅ < ∗ (∅ ∷ ∅ ∷ [])
    ∋ tt
  _ = c₁ 0 ≮ ∅
    ∋ λ ()
  _ = c₁ 0 ≰ ∅
    ∋ λ where (inj₂ ())
  _ = c₁ 0 ≮ c₁ 0
    ∋ λ ()
  _ = c₁ 0 ≤ c₁ 0
    ∋ ≪ refl
  _ = c₁ 0 < c₁ 1
    ∋ 0<1
  _ = c₁ 1 < c₂ 0 0ℤ
    ∋ tt
  _ = c₁ 0 < (∅ ⊚ ∅)
    ∋ tt
  _ = c₁ 0 < ∗ (∅ ∷ ∅ ∷ [])
    ∋ tt
  _ = c₂ 0 0ℤ ≮ c₂ 0 0ℤ
    ∋ λ where (≫ +<+ ())
  _ = c₂ 0 0ℤ ≤ c₂ 0 0ℤ
    ∋ ≪ refl
  _ = c₂ 0 1ℤ < c₂ 1 0ℤ
    ∋ ≪ 0<1
  _ = c₂ 0 0ℤ < c₂ 0 1ℤ
    ∋ ≫ +<+ 0<1
  _ = c₂ 1 0ℤ < c₂ 1 1ℤ
    ∋ ≫ +<+ 0<1
  _ = c₂ 0 0ℤ < (∅ ⊚ ∅)
    ∋ tt
  _ = c₂ 0 0ℤ < ∗ (∅ ∷ ∅ ∷ [])
    ∋ tt
  _ = (∅ ⊚ ∅) ≤ (∅ ⊚ ∅)
    ∋ ≪ refl
  _ = (∅ ⊚ ∅) < (∅ ⊚ c₁ 0)
    ∋ ≫ tt
  _ = (c₁ 0 ⊚ c₂ 0 0ℤ) < (c₁ 0 ⊚ c₂ 1 0ℤ)
    ∋ ≫ ≪ 0<1
  _ = (c₁ 0 ⊚ c₂ 1 0ℤ) ≮ (c₁ 0 ⊚ c₂ 0 1ℤ)
    ∋ λ where (≫ ≪⊥)
  _ = (c₁ 0 ⊚ c₂ 1 0ℤ) < ∗ (∅ ∷ ∅ ∷ [])
    ∋ tt
  _ = ∗ (∅ ∷ ∅ ∷ []) ≮ ∗ (∅ ∷ ∅ ∷ [])
    ∋ λ where (≫ ≪⊥); (≫ ≫⊥)
  _ = ∗ (∅ ∷ ∅ ∷ []) < ∗ (∅ ∷ c₁ 0 ∷ [])
    ∋ ≫ ≪ tt

  _ : DecOrd X
  _ = it

  _ = ¿ (c₁ 0 ⊚ c₂ 0 0ℤ) < (c₁ 0 ⊚ c₂ 1 0ℤ) ¿ ≡ yes (≫ ≪ 0<1)
    ∋ refl

  instance
    Dec-<X : _<_ {A = X} ⁇²
    Dec-<X {x} .dec = x <? _

    Dec-≤X : _≤_ {A = X} ⁇²
    Dec-≤X .dec = _ ≤? _

  record R : Set where
    constructor _⊕_⊕_
    field
      n : ℕ
      z : ℤ
      ns : List ℕ
  open R
  unquoteDecl DecEq-R = DERIVE DecEq [ quote R , DecEq-R ]
  unquoteDecl Ord-R DecOrd-R OrdLaws-R = DERIVE-Ord [ quote R , Ord-R , DecOrd-R , OrdLaws-R ]

  _ = (0 ⊕ 0ℤ ⊕ [])
    < (1 ⊕ 0ℤ ⊕ [])
    ∋ ≪ 0<1
  _ = (0 ⊕ 0ℤ ⊕ [])
    < (0 ⊕ 1ℤ ⊕ [])
    ∋ ≫ ≪ +<+ 0<1
  _ = (0 ⊕ 0ℤ ⊕ [])
    < (0 ⊕ 0ℤ ⊕ [ 0 ])
    ∋ ≫ ≫ ≪ it

  _ : DecOrd R
  _ = it

  _ = ((0 ⊕ 0ℤ ⊕ []) <? (0 ⊕ 1ℤ ⊕ [])) ≡ yes (≫ ≪ +<+ 0<1)
    ∋ refl

  instance
    Dec-<R : _<_ {A = R} ⁇²
    Dec-<R {x} .dec = x <? _

    Dec-≤R : _≤_ {A = R} ⁇²
    Dec-≤R .dec = _ ≤? _
