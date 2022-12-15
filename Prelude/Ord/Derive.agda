{-# OPTIONS -v ord:100 #-}
{-# OPTIONS --with-K #-}
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
open import Prelude.Generics using (DERIVE) public
open Debug ("ord" , 100)

open import Prelude.Ord.Core
open import Prelude.Ord.Dec
open import Prelude.Ord.Instances
open import Prelude.Ord.List

private
  variable A : Set ℓ

  pattern `⊤ = quote ⊤ ∙
  pattern `↑⊤ = quote ↑ℓ ∙⟦ `⊤ ⟧
  pattern `yes x = quote _because_ ◆⟦ quote true ◆  ∣ quote ofʸ ◆⟦ x ⟧ ⟧
  pattern `yes-tt = `yes (quote it ∙)
  pattern `⊥ = quote ⊥ ∙
  pattern `↑⊥ = quote ↑ℓ ∙⟦ `⊥ ⟧
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
    (x `⊎ `↑⊥) → x
    (`↑⊥ `⊎ x) → x
    (x `× `↑⊥) → `↑⊥
    (`↑⊥ `× _) → `↑⊥
    t → t
  {-# TERMINATING #-}
  `toDec = λ where
    (lam v (abs s t)) → lam v (abs s (`toDec t))
    (pat-lam cs []) → pat-lam (map go cs) []
    (x `⊎ y) → `toDec x `⊎-dec `toDec y
    (x `× y) → `toDec x `×-dec `toDec y
    (x `≡ y) → `toDec x `≟ `toDec y
    (x `< y) → `toDec x `<? `toDec y
    `↑⊥      → `no-⊥
    `↑⊤      → `yes-tt
    t        → t
   where go = λ where
    (clause tel as e) → clause tel as (`toDec e)
    c → c

  module _ (toDrop : ℕ) {- module context -} where
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
            0 → `↑⊥
            (suc n) →
              let i = N ∸ n ∸ 1
                  x = ♯ i; y  = ♯ (i + N)
                  x< = x `< y
                  x≡ = x `≡ y
              in removeExtra⊥ (x< `⊎ removeExtra⊥ (x≡ `× constructLex< n))

        mkClause : ℕ × Name → TC (List Clause)
        mkClause (i , cn) = do
          print $ "  Making pattern clauses for constructor: " ◇ show cn
          tys , N , _ , pc ← mkPattern toDrop cn
          let mkTel = flip L.replicate ("_" , vArg unknown)
          cls< ← forM (take i cs) λ cn′ → do
            tys′ , N′ , _ , pc′ ← mkPattern toDrop cn′
            return $ clause (mkTel $ N + N′)
                            (vArg <$> (pc ∷ mapVariables (_+ N) pc′ ∷ [])) `↑⊥
          let cl≡ = clause (mkTel $ N + N)
                           (vArg <$> (pc ∷ mapVariables (_+ N) pc ∷ []))
                           (constructLex< N N)
          cls> ← forM (drop (suc i) cs) λ cn′ → do
            tys′ , N′ , _ , pc′ ← mkPattern toDrop cn′
            return $ clause (mkTel $ N + N′)
                            (vArg <$> (pc ∷ mapVariables (_+ N) pc′ ∷ [])) `↑⊤
          return $ cls< ++ cl≡ ∷ cls>
    ... | record-type rn fs = do
      print $ "RECORD {name = " ◇ show rn ◇ "; fs = " ◇ show fs ◇ "}"
      return `λ⟦ "r" ∣ "r′" ⇒ constructLex< (vArgs fs) ⟧
      where
        N = length fs
        ♯r = ♯ 1; ♯r′ = ♯ 0

        constructLex< : List Name → Term
        constructLex< = λ where
          [] → `↑⊥
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

module _ (ss : List $ String × Name) where
  addHypotheses : Type → Type
  addHypotheses (Π[ s ∶ a ] ty) =
    Π[ s ∶ a ]
      (case unArg a of λ where
        (agda-sort (lit _)) → ty″
        (agda-sort (set _)) → ty″
        _ → ty′)
    where
      ty′ = addHypotheses ty
      ty″ = go (zip (indices ss) ss) ty′
        where
        go : List (ℕ × String × Name) → (Type → Type)
        go = λ where
          [] → mapVars (_+ length ss)
          ((i , s′ , n) ∷ xs) → iΠ[ s ◇ s′ ∶ n ∙⟦ ♯ i ⟧ ]_ ∘ go xs

  addHypotheses ty = ty

instance
  Derivable-Ord∗ : DERIVABLE Ord 3
  Derivable-Ord∗ .derive args = do
    (n , f , dec-f , laws-f) ∷ [] ← return args
      where _ → error "[not supported] mutual types"
    print "********************************************************"
    d ← getDefinition n; ty ← getType n; ctx ← getContext

    print $ "Deriving " ◇ parens (show f ◇ " : Ord " ◇ show n)
    let tel = tyTele ty
        n′ = apply⋯ tel n
        iTy = addHypotheses [ "Ord-" , quote Ord ]
            $ ∀indices⋯ tel
            $ quote Ord ∙⟦ n′ ⟧
    declareDef (iArg f) iTy
    inContext (L.reverse $ tyTele iTy) $ do
      ctx ← getContext; print ("  Context′: " ◇ show ctx)
      iTerm ← deriveOrd (length tel) n d
      print $ "instance\n  " ◇ show f ◇ " : " ◇ show iTy ◇ " = "
      print $ showTermClauses iTerm
      defineFun f [ clause [] [] (quote mkOrd< ∙⟦ iTerm ⟧) ]

    print $ "Postulating " ◇ parens (show laws-f ◇ " : OrdLaws " ◇ show n)
    let iTy = addHypotheses ( ("Ord-"     , quote Ord)
                            ∷ ("OrdLaws-" , quote OrdLaws)
                            ∷ []
                            )
            $ ∀indices⋯ tel
            $ quote OrdLaws ∙⟦ n′ ⟧
    declarePostulate (iArg laws-f) iTy

    print $ "Deriving " ◇ parens (show dec-f ◇ " : DecOrd " ◇ show n)
    let iTy = addHypotheses ( ("Ord-"    , quote Ord)
                            ∷ ("DecOrd-" , quote DecOrd)
                            ∷ ("DecEq-"  , quote DecEq)
                            ∷ []
                            )
            $ ∀indices⋯ tel
            $ quote DecOrd ∙⟦ n′ ⟧
    declareDef (iArg dec-f) iTy
    inContext (L.reverse $ tyTele iTy) $ do
      ctx ← getContext; print ("  Context′: " ◇ show ctx)
      iTerm ← `toDec <$> deriveOrd (length tel) n d
      print $ "instance\n  " ◇ show f ◇ " : " ◇ show iTy ◇ " = "
      print $ showTermClauses iTerm
      defineFun dec-f [ clause [] [] (quote mkDecOrd< ∙⟦ iTerm ⟧) ]
    print "********************************************************"

private
  pattern ≪_ x = inj₁ x
  pattern ≫_ x = inj₂ (refl , x)
  pattern ≪⊥ = ≪ ()
  pattern ≫⊥ = ≫ ()
  open Integer using (0ℤ; 1ℤ; +<+)
  pattern 0<1 = s≤s z≤n

  data X : Set where
    ∅ : X
    c₁ : ℕ → X
    c₂ : ℕ → ℤ → X
    _⊚_ : X → X → X
    ∗_ : List X → X
  {-# TERMINATING #-}
  unquoteDecl DecEq-X = DERIVE DecEq [ quote X , DecEq-X ]
  {-# TERMINATING #-}
  unquoteDecl Ord-X DecOrd-X OrdLaws-X =
    DERIVE Ord [ quote X , Ord-X , DecOrd-X , OrdLaws-X ]

  _ = ∅ ≮ ∅ ∋ λ ()
  _ = ∅ ≤ ∅ ∋ ≪ refl
  _ = ∅ < c₁ 0 ∋ it
  _ = ∅ < c₁ 0 ∋ it
  _ = ∅ < c₂ 0 0ℤ ∋ it
  _ = ∅ < (∅ ⊚ ∅) ∋ it
  _ = ∅ < ∗ (∅ ∷ ∅ ∷ []) ∋ it
  _ = c₁ 0 ≮ ∅ ∋ λ ()
  _ = c₁ 0 ≰ ∅ ∋ λ where (inj₂ ())
  _ = c₁ 0 ≮ c₁ 0 ∋ λ ()
  _ = c₁ 0 ≤ c₁ 0 ∋ ≪ refl
  _ = c₁ 0 < c₁ 1 ∋ 0<1
  _ = c₁ 1 < c₂ 0 0ℤ ∋ it
  _ = c₁ 0 < (∅ ⊚ ∅) ∋ it
  _ = c₁ 0 < ∗ (∅ ∷ ∅ ∷ []) ∋ it
  _ = c₂ 0 0ℤ ≮ c₂ 0 0ℤ ∋ λ where (≫ +<+ ())
  _ = c₂ 0 0ℤ ≤ c₂ 0 0ℤ ∋ ≪ refl
  _ = c₂ 0 1ℤ < c₂ 1 0ℤ ∋ ≪ 0<1
  _ = c₂ 0 0ℤ < c₂ 0 1ℤ ∋ ≫ +<+ 0<1
  _ = c₂ 1 0ℤ < c₂ 1 1ℤ ∋ ≫ +<+ 0<1
  _ = c₂ 0 0ℤ < (∅ ⊚ ∅) ∋ it
  _ = c₂ 0 0ℤ < ∗ (∅ ∷ ∅ ∷ []) ∋ it
  _ = (∅ ⊚ ∅) ≤ (∅ ⊚ ∅) ∋ ≪ refl
  _ = (∅ ⊚ ∅) < (∅ ⊚ c₁ 0) ∋ ≫ it
  _ = (c₁ 0 ⊚ c₂ 0 0ℤ) < (c₁ 0 ⊚ c₂ 1 0ℤ) ∋ ≫ ≪ 0<1
  _ = (c₁ 0 ⊚ c₂ 1 0ℤ) ≮ (c₁ 0 ⊚ c₂ 0 1ℤ) ∋ λ where (≫ ≪⊥)
  _ = (c₁ 0 ⊚ c₂ 1 0ℤ) < ∗ (∅ ∷ ∅ ∷ []) ∋ it
  _ = ∗ (∅ ∷ ∅ ∷ []) ≮ ∗ (∅ ∷ ∅ ∷ []) ∋ λ where (≫ ≪⊥); (≫ ≫⊥)
  _ = ∗ (∅ ∷ ∅ ∷ []) < ∗ (∅ ∷ c₁ 0 ∷ []) ∋ ≫ ≪ it

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
  unquoteDecl Ord-R DecOrd-R OrdLaws-R =
    DERIVE Ord [ quote R , Ord-R , DecOrd-R , OrdLaws-R ]

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

  data _list (A : Set) : Set where
    [] : A list
    _∷_ : A → A list → A list
  -- unquoteDecl DecEq-L = DERIVE DecEq [ quote _list , DecEq-L ]
  postulate instance DecEq-L : ∀ {A} → DecEq (A list)
  {-# TERMINATING #-}
  unquoteDecl Ord-L DecOrd-L OrdLaws-L =
    DERIVE Ord [ quote _list , Ord-L , DecOrd-L , OrdLaws-L ]

  _ = (ℤ list ∋ 1ℤ ∷ 0ℤ ∷ []) < (1ℤ ∷ 1ℤ ∷ [])
    ∋ ≫ ≪ +<+ 0<1

  module _ {A : Set} ⦃ _ : Ord A ⦄ ⦃ _ : DecEq A ⦄ where
    _ : ⦃ DecOrd A ⦄ → DecOrd (A list)
    _ = it

  _ = ((ℤ list ∋ 1ℤ ∷ 0ℤ ∷ []) <? (1ℤ ∷ 1ℤ ∷ [])) ≡ yes (≫ ≪ +<+ 0<1)
    ∋ refl

  data BiList (A B : Set) : Set where
    [] : BiList A B
    _∷_ : A × B → BiList A B → BiList A B
  -- unquoteDecl DecEq-L = DERIVE DecEq [ quote _list , DecEq-L ]
  postulate instance DecEq-BiL : ∀ {A B} → DecEq (BiList A B)
  open import Prelude.Ord.Product
  {-# TERMINATING #-}
  unquoteDecl Ord-BiL DecOrd-BiL OrdLaws-BiL =
    DERIVE Ord [ quote BiList , Ord-BiL , DecOrd-BiL , OrdLaws-BiL ]

  _ = (BiList ℕ ℤ ∋ (1 , 1ℤ) ∷ (0 , 0ℤ) ∷ []) < ((1 , 1ℤ) ∷ (1 , 1ℤ) ∷ [])
    ∋ ≫ ≪ ≪ 0<1

  module _ {A B : Set} ⦃ _ : Ord A ⦄ ⦃ _ : Ord B ⦄ ⦃ _ : DecEq A ⦄ ⦃ _ : DecEq B ⦄ where
    _ : ⦃ DecOrd A ⦄ → ⦃ DecOrd B ⦄ → DecOrd (BiList A B)
    _ = it

  _ = ((BiList ℕ ℤ ∋ (1 , 1ℤ) ∷ (0 , 0ℤ) ∷ []) <? ((1 , 1ℤ) ∷ (1 , 1ℤ) ∷ []))
      ≡ yes (≫ ≪ ≪ 0<1)
    ∋ refl

  data _list′ (A : Set ℓ) : Set ℓ where
    [] : A list′
    _∷_ : A → A list′ → A list′
  -- unquoteDecl DecEq-L = DERIVE DecEq [ quote _list , DecEq-L ]
  postulate instance DecEq-L′ : ∀ {A : Set ℓ} → DecEq (A list′)
  {-# TERMINATING #-}
  unquoteDecl Ord-L′ DecOrd-L′ OrdLaws-L′ =
    DERIVE Ord [ quote _list′ , Ord-L′ , DecOrd-L′ , OrdLaws-L′ ]

  _ = (ℤ list′ ∋ 1ℤ ∷ 0ℤ ∷ []) < (1ℤ ∷ 1ℤ ∷ [])
    ∋ ≫ ≪ +<+ 0<1

  module _ {A : Set} ⦃ _ : Ord A ⦄ ⦃ _ : DecEq A ⦄ where
    _ : ⦃ DecOrd A ⦄ → DecOrd (A list′)
    _ = it

  _ = ((ℤ list′ ∋ 1ℤ ∷ 0ℤ ∷ []) <? (1ℤ ∷ 1ℤ ∷ [])) ≡ yes (≫ ≪ +<+ 0<1)
    ∋ refl


  -- unquoteDecl DecEq-List = DERIVE DecEq [ quote List , DecEq-List ]
  -- unquoteDecl Ord-List DecOrd-List OrdLaws-List =
  --   DERIVE Ord [ quote List , Ord-List , DecOrd-List , OrdLaws-List ]

{-
  unquoteDecl `Ord-List = DERIVE↑ Ord [ quote List , `Ord-List ]

  _ : DecOrd (List A)
  _ = it

  _ = ((List ℤ ∋ 2ℤ ∷ 0ℤ ∷ []) <? (2ℤ ∷ 1ℤ ∷ [])) ≡ yes (≫ ≪ +<+ 0<1)
    ∋ refl

-}
