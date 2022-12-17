{-# OPTIONS -v bnfc:100 #-}
module Prelude.Tactics.BNF where

open import Agda.Builtin.Reflection using (declareData; defineData)

open import Prelude.Init hiding (+_; _+_; _*_)
open Meta
open import Prelude.Generics hiding (Derivation)
open Debug ("bnfc" , 100)
open import Prelude.Monad
open import Prelude.Nary renaming (⟦_⟧ to `⟦_⟧)
open import Prelude.General

private variable n : ℕ; A : Set ℓ

toList : A ^ n → List A
toList {n = 0} A = [ A ]
toList {n = suc n} (A , As) = A ∷ toList As

pattern _&_ x y = _,_ x y
pattern _∣_ x y = _,_ x y

infixr -1 _&_
infix  0  _∷=_
infixr 1  _∣_
infix  2  _∶_
-- infixr 4 _,_

private
  data Rule : Set where
    _∶_ : Name → Name ^ n → Rule

  data Derivation : Set where
    _∷=_ : Name → Rule ^ n → Derivation

  pattern `Set = agda-sort (lit 0)

  rules→constructors : Name → Rule ^ n → List (Name × Type)
  rules→constructors n = map go ∘ toList
    where
      go : Rule → Name × Type
      go (c ∶ tys)
       = (c , tyView (map (λ n → abs "_" $ vArg (n ∙)) (toList tys) , n ∙))

infix -100 BNF∶_
BNF∶_ : Derivation ^ n → TC ⊤
BNF∶ ds = do
  forEach λ where (n ∷= _) → declareData n 0 `Set
  forEach λ where (n ∷= rs) → defineData n (rules→constructors n rs)
  where
    forEach : (Derivation → TC ⊤) → TC ⊤
    forEach = void ∘ forM (toList ds)

unquoteDecl Expr k _+_ _*_ _⨾_ Expr⁺ ↓_ _＝_ =
  BNF∶
    Expr  ∷= k   ∶ quote ℕ
           ∣ _+_ ∶ Expr , Expr
           ∣ _*_ ∶ Expr , Expr
           ∣ _⨾_ ∶ Expr⁺ , Expr
  & Expr⁺ ∷= ↓_  ∶ Expr
           ∣ _＝_ ∶ Expr , Expr
infixr 5 _*_
infixr 4 _+_
infix  3 _＝_
infix  2 _⨾_
infix  0 ↓_

x : Expr
x = k 5
y : Expr
y = k 5 + k 5
z : Expr
z = k 5 * k 5 + k 5

_ : Expr⁺
_ = k 5 * k 5 + k 5 ＝ (k 0 ＝ k 1 ⨾ k 30)
