------------------------------------------------------------------------
-- Singleton predicate for various kinds of lists.

{-# OPTIONS --safe #-}
module Prelude.Lists.Singletons where

open import Prelude.Init; open SetAsType
open Nat using (_≤_)
open L.Mem using (_∈_; mapWith∈)
open L.NE using (toList)
open import Prelude.Null
open import Prelude.Lists.Count
open import Prelude.Lists.Combinatorics
open import Prelude.Lists.Empty
open import Prelude.Lists.NonEmpty

private variable
  A : Type ℓ
  B : Type ℓ′
  x : A
  xs : List A
  xss : List (List A)

Singleton : List A → Type
Singleton []       = ⊥
Singleton (_ ∷ []) = ⊤
Singleton (_ ∷ _)  = ⊥

construct-Singleton : ∃[ x ] (xs ≡ x ∷ []) → Singleton xs
construct-Singleton (_ , refl) = tt

destruct-Singleton : Singleton xs → ∃ λ x → xs ≡ [ x ]
destruct-Singleton {xs = []}          ()
destruct-Singleton {xs = _ ∷ []}      tt = _ , refl
destruct-Singleton {xs = _ ∷ (_ ∷ _)} ()

Singleton⇒len≡ : Singleton xs → length xs ≡ 1
Singleton⇒len≡ s-xs rewrite proj₂ $ destruct-Singleton s-xs = refl

len≡⇒Singleton : length xs ≡ 1 → Singleton xs
len≡⇒Singleton {xs = []}        ()
len≡⇒Singleton {xs = _ ∷ []}    refl = tt
len≡⇒Singleton {xs = _ ∷ _ ∷ _} ()

singleton-map : ∀ {f : A → B}
  → Singleton xs
  → Singleton (map f xs)
singleton-map {xs = []}        ()
singleton-map {xs = _ ∷ []}    tt = tt
singleton-map {xs = _ ∷ _ ∷ _} ()

singleton-subseqs : Singleton xs → subsequences xs ≡ [] ∷ xs ∷ []
singleton-subseqs {xs = []}        ()
singleton-subseqs {xs = _ ∷ []}    tt = refl
singleton-subseqs {xs = _ ∷ _ ∷ _} ()

singleton-mapWith∈  : ∀ {x : A} {xs : List A} {x′ : B} {f : ∀ {x} → x ∈ xs → B}
  → (∀ x∈ → f {x} x∈ ≡ x′)
  → xs ≡ [ x ]
  → mapWith∈ xs f ≡ [ x′ ]
singleton-mapWith∈ f≡ refl rewrite f≡ (here refl) = refl

singleton∈ : ∀ {xs : List A}
  → (s-xs : Singleton xs)
  → proj₁ (destruct-Singleton s-xs) ∈ xs
singleton∈ s-xs with _ , refl ← destruct-Singleton s-xs = here refl

singleton-concat : ∀ {x : A} {xss : List (List A)}
  → xss ≡ [ [ x ] ]
  → Singleton (concat xss)
singleton-concat refl = tt

All-singleton : {x : A} {xs : List A} {P : A → Type}
 → xs ≡ [ x ]
 → All P xs
 → P x
All-singleton refl (Px ∷ []) = Px

---

AtMostSingleton : Pred₀ (List A)
AtMostSingleton []          = ⊤
AtMostSingleton (_ ∷ [])    = ⊤
AtMostSingleton (_ ∷ _ ∷ _) = ⊥

ams-single : ∀ {x : A} {xs : List A}
  → AtMostSingleton (x ∷ xs)
  → xs ≡ []
ams-single {xs = []}    _ = refl
ams-single {xs = _ ∷ _} ()

ams-∈ : ∀ {x : A} {xs : List A}
  → AtMostSingleton xs
  → x ∈ xs
  → xs ≡ [ x ]
ams-∈ {xs = []}        _  ()
ams-∈ {xs = x ∷ []}    _  (here refl) = refl
ams-∈ {xs = _ ∷ _ ∷ _} () _

ams-filter⁺ : ∀ {xs : List A} {P : A → Type} {P? : Decidable¹ P}
  → AtMostSingleton xs
  → AtMostSingleton (filter P? xs)
ams-filter⁺ {xs = []}                  tt = tt
ams-filter⁺ {xs = x ∷ []}    {P? = P?} tt with P? x
... | yes _ = tt
... | no  _ = tt
ams-filter⁺ {xs = _ ∷ _ ∷ _}           ()

am-¬null⇒singleton : ∀ {xs : List A}
  → AtMostSingleton xs
  → ¬Null xs
  → Singleton xs
am-¬null⇒singleton {xs = []         } tt ¬p = ⊥-elim (¬p refl)
am-¬null⇒singleton {xs = (_ ∷ [])   } _  _  = tt
am-¬null⇒singleton {xs = (_ ∷ _ ∷ _)} ()

---

Singleton⁺ : List⁺ A → Type
Singleton⁺ (_ ∷ []) = ⊤
Singleton⁺ (_ ∷ _)  = ⊥

destruct-Singleton⁺ : ∀ {xs : List⁺ A}
  → Singleton⁺ xs
  → ∃ λ x → xs ≡ [ x ]⁺
destruct-Singleton⁺ {xs = _ ∷ []}      tt = _ , refl
destruct-Singleton⁺ {xs = _ ∷ (_ ∷ _)} ()

singleton⁺ : ∀ {A : Type ℓ} {xs : List A}
  → AtMostSingleton xs
  → (xs≢[] : ¬Null xs)
  → Singleton⁺ (toList⁺ xs xs≢[])
singleton⁺ {xs = []}        tt xs≢[] = ⊥-elim $ xs≢[] refl
singleton⁺ {xs = _ ∷ []}    tt xs≢[] = tt
singleton⁺ {xs = _ ∷ _ ∷ _} ()

singleton-concatMap  : ∀ {h : List⁺ A} {f : A → List B}
  → Singleton⁺ h
  → (∀ x → Singleton (f x))
  → Singleton $ concatMap f (toList h)
singleton-concatMap {f = f} h⁺ s-f
  with h , refl ← destruct-Singleton⁺ h⁺
  rewrite L.++-identityʳ (f h)
    = s-f h

singleton⇒singleton⁺ : ∀ {A : Type ℓ} {xs : List A} {xs≢[] : ¬ Null xs}
  → Singleton xs
  → Singleton⁺ (toList⁺ xs xs≢[])
singleton⇒singleton⁺ p rewrite destruct-Singleton p .proj₂ = tt

---

Singleton² : Pred (List (List A)) _
Singleton² xss = Singleton xss × All Singleton xss

construct-Singleton² :
    xss ≡ [ [ x ] ]
  → Singleton² xss
construct-Singleton² refl = tt , tt ∷ []

destruct-Singleton² : Singleton² xss → ∃ λ x → xss ≡ [ [ x ] ]
destruct-Singleton² (tt , s-xs ∷ [])
  with x , refl ← destruct-Singleton s-xs
     = x , refl

singleton-concat⁺ : Singleton² xss → Singleton (concat xss)
singleton-concat⁺ {xss = []}                  (()   , _)
singleton-concat⁺ {xss = []          ∷ []}    (_    , () ∷ _)
singleton-concat⁺ {xss = (_ ∷ [])    ∷ []}    (_    , _)      = tt
singleton-concat⁺ {xss = (_ ∷ _ ∷ _) ∷ []}    (_    , () ∷ _)
singleton-concat⁺ {xss = _           ∷ _ ∷ _} (()   , _)
