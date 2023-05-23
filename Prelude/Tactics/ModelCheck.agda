{-# OPTIONS --allow-exec --with-K #-}
{-# OPTIONS -v modelcheck:100 #-}
open import Agda.Builtin.Reflection.External using (execTC)

open import Prelude.Init
open Integer hiding (show; _>_; _≥_; _<_; _≤_)
open Meta
open import Prelude.Generics
open Debug ("modelcheck" , 100)
open import Prelude.Ord
open import Prelude.Semigroup
open import Prelude.Show
open import Prelude.Monad
open import Prelude.DecEq
open import Prelude.FromList; open import Prelude.ToList
open import Prelude.Tactics.PostulateIt
open import Prelude.Nary

private variable A B S : Set

-- ** state machine definition
record StateMachine (S : Set) : Set where
  field init : S
        step : S → S
open StateMachine

Invariant : StateMachine S → Pred₀ S → Set
Invariant sm P = P (sm .init) × (∀ s → P s → P (sm .step s))

-- ** translation to Kind2 syntax
record ToCode (A : Set) : Set where
  field toCode : A → String
open ToCode ⦃...⦄ public

pattern `pos l = con (quote ℤ.pos) (vArg l ∷ [])
pattern `if_then_else_ b x y =
  def (quote if_then_else_) (hArg _ ∷ hArg _ ∷ vArg b ∷ vArg x ∷ vArg y ∷ [])

toCode-deBruijn : ℕ → String
toCode-deBruijn = λ where
  0 → "𝟘"; 1 → "𝟙"; 2 → "𝟚"; 3 → "𝟛"; 4 → "𝟜"
  5 → "𝟝"; 6 → "𝟞"; 7 → "𝟟"; 8 → "𝟠"; 9 → "𝟡"
  _ → "$"

toCode-binOp toCode-unOp toCode-nullOp : Name → String
toCode-nullOp n = case show n of λ where
  "Int" → "int"; "ℤ" → "int"
  "0ℤ"  → "0"; "1ℤ"  → "1"
  s → s
toCode-unOp n = case show n of λ where
  "¬_" → "not"
  s → s
toCode-binOp n = case show n of λ where
  "_>ᵇ_" → ">"; "_≥ᵇ_" → ">="; "_<ᵇ_" → "<"; "_≤ᵇ_" → "<="
  "_>_" → ">"; "_≥_" → ">="; "_<_" → "<"; "_≤_" → "<="
  "_-_" → "-"
  s → s

instance
  ToCode-ℕ : ToCode ℕ
  ToCode-ℕ .toCode = show

  ToCode-ℤ : ToCode ℤ
  ToCode-ℤ .toCode = λ where
    (Integer.+_ n)     → toCode n
    (Integer.-[1+_] n) → "-" ◇ toCode n

  ToCode-Float : ToCode Float
  ToCode-Float .toCode = show

  ToCode-Char : ToCode Char
  ToCode-Char .toCode = show

  ToCode-String : ToCode String
  ToCode-String .toCode s = "\"" ◇ show s ◇ "\""

  ToCode-Literal : ToCode Literal
  ToCode-Literal .toCode = λ where
    (nat    n) → toCode n
    (float  f) → toCode f
    (char   c) → toCode c
    (string s) → toCode s
    l → show l

  {-# TERMINATING #-}
  ToCode-Term : ToCode Term
  ToCode-Term .toCode = λ where
    (lit l) → toCode l
    (var n []) → toCode-deBruijn n
    (`pos l) → toCode l
    (`if b then x else y) →
      "if " ◇ toCode b ◇ " then " ◇ toCode x ◇ " else " ◇ toCode y
    t@(def op as) →
      case vArgs as of λ where
        [] → toCode-nullOp op
        (x ∷ []) → toCode-unOp op ◇ " (" ◇ toCode x ◇ ")"
        (x ∷ y ∷ []) → toCode x ◇ " " ◇ toCode-binOp op ◇ " " ◇ toCode y
        (_ ∷ x ∷ y ∷ []) → toCode x ◇ " " ◇ toCode-binOp op ◇ " " ◇ toCode y
        _ → show t
    t → show t

-- ** counter state machine
State = ℤ

Counter : StateMachine State
Counter = λ where
  .init → + 42
  .step i → if i >ᵇ 0ℤ then i - 1ℤ else 0ℤ
-- Counter = record
--   { init = + 42
--   ; step = λ i → if i >ᵇ 0ℤ then i - 1ℤ else 0ℤ
--   }

NoNegatives : Pred₀ State
NoNegatives = λ i → ¬ (i < + 0)

-- ** reflection
private postulate
  solvedByKind2 : ∀ {A : Set ℓ} → A
macro
  solveWithKind2 : Hole → TC ⊤
  solveWithKind2 hole = do
    (def (quote Invariant) as) ← inferType hole
      where _ → error "goal type is not an `Invariant`"
    (n ∙ ∷ p@(def pn _) ∷ []) ← return $ vArgs as
      where _ → error "hole should be of type `Invariant _ _`"
    (lam visible (abs _ p)) ← reduce p
      where _ → error "invariant property should be of the form `λ x → P x`"
    (def (quote StateMachine) (vArg ty ∷ [])) ← getType n
      where _ → error "not of type `StateMachine _`"
    ty ← reduce ty
    function (clause _ _ body ∷ []) ← getDefinition n
      where _ → error $ show n ◇ " is not defining a record value"
    (i , x , t) ← getRecordValue body
    let s = "node " ◇ show n ◇ "() returns (" ◇ x ◇ " : " ◇ toCode ty ◇ ");\n"
          ◇ "let\n"
          ◇ "  " ◇ x ◇ " = " ◇ toCode i ◇ " -> \n"
          ◇ "    " ◇ replace ('𝟘' , "(pre " ◇ x ◇ ")") (toCode t) ◇ ";\n"
          ◇ "  check \"" ◇ show pn ◇ "\" " ◇ replace ('𝟘' , x) (toCode p) ◇ ";\n"
          ◇ "tel\n"
    print s
    (errCode , stdout , _) ← execTC "kind2" ⟦ "--color" , "false" ⟧ s
    print $ "errCode: " ◇ show errCode
    case errCode of λ where
      20 → print stdout >> unify hole (quote solvedByKind2 ∙)
      _  → error stdout
    where
      replace : Char × String → String → String
      replace (c₀ , x) = fromList
                       ∘ concatMap (λ c → if c == c₀ then toList x else [ c ])
                       ∘ toList

      getRecordValue : Term → TC (Term × String × Term)
      getRecordValue t with t
      ... | con _ (_ ∷ vArg i ∷ vArg (lam visible (abs x t)) ∷ [])
          = return (i , x , t)
      ... | pat-lam (clause _ _ i ∷ clause ((x , _) ∷ []) _ t ∷ []) _
          = return (i , x , t)
      ... | _ = error $ "not a record value: " ◇ show t

_ : Invariant Counter NoNegatives
_ = solveWithKind2
