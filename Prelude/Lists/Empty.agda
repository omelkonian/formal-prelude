------------------------------------------------------------------------
-- Empty lists.

module Prelude.Lists.Empty where

open import Prelude.Init
open L.Mem using (_∈_; mapWith∈)
open import Prelude.Null

private variable
  A : Set ℓ
  B : Set ℓ′
  x : A
  xs ys : List A
  xss : List (List A)

toList≢[] : ∀ {xs : List⁺ A} → ¬Null (L.NE.toList xs)
toList≢[] {xs = x ∷ xs} ()

map≢[] : ∀ {xs : List A} {f : A → B}
  → ¬Null xs
  → ¬Null (map f xs)
map≢[] {xs = []}     xs≢[] _      = ⊥-elim $ xs≢[] refl
map≢[] {xs = x ∷ xs} _    ()

mapWith∈≢[] : ∀ {f : ∀ {x} → x ∈ xs → B}
  → ¬Null xs
  → ¬Null (mapWith∈ xs f)
mapWith∈≢[] {xs = []}     xs≢[] _ = ⊥-elim $ xs≢[] refl
mapWith∈≢[] {xs = x ∷ xs} _    ()

concat≡[]ˡ : Null $ concat (xs ∷ xss) → Null xs
concat≡[]ˡ {xs = []} _ = refl

concat≡[]ʳ : Null $ concat (xs ∷ xss) → Null $ concat xss
concat≡[]ʳ {xs = []} {xss = xss} concat≡[]
  rewrite L.++-identityˡ xss = concat≡[]

concat≢[] :
    ∃[ xs ] ( (xs ∈ xss)
            × ¬Null xs )
  → ¬Null (concat xss)
concat≢[] {xss = _ ∷ xss} (_  , here refl , xs≢[]) concat≡[] = xs≢[] $ concat≡[]ˡ {xss = xss} concat≡[]
concat≢[] {xss = _ ∷ xss} (xs , there xs∈ , xs≢[]) concat≡[] = concat≢[] (xs , xs∈ , xs≢[])
                                                                       (concat≡[]ʳ {xss = xss} concat≡[])

concat≡[] : Null $ concat xss → All Null xss
concat≡[] {xss = []}       _  = []
concat≡[] {xss = [] ∷ xss} eq
  rewrite L.++-identityˡ xss = refl ∷ concat≡[] eq

mapWith∈≡[] : ∀ {f : ∀ {x} → x ∈ xs → B}
  → Null $ mapWith∈ xs f
  → Null xs
mapWith∈≡[] {xs = []} _ = refl

∀mapWith∈≡[] : ∀ {f : ∀ {x} → x ∈ xs → List B}
  → (∀ {x} x∈ → ¬Null $ f {x} x∈)
  → ¬ (Null xs)
  → ¬ (All Null $ mapWith∈ xs f)
∀mapWith∈≡[] {xs = []}     {f} _  xs≢[]  _    = xs≢[] refl
∀mapWith∈≡[] {xs = x ∷ xs} {f} ∀f _      ∀≡[] = ∀f {x} (here refl) (L.All.lookup ∀≡[] (here refl))

filter≡[] : {P : A → Set} {P? : Decidable¹ P} {xs : List A}
  → filter P? xs ≡ []
  → All (¬_ ∘ P) xs
filter≡[] {P = P} {P?} {[]}     _  = []
filter≡[] {P = P} {P?} {x ∷ xs} eq
  with P? x | eq
... | yes px  | ()
... | no  ¬px | eq′ = ¬px ∷ filter≡[] eq′

¬Null⇒∃x : ¬Null xs → ∃ (_∈ xs)
¬Null⇒∃x {xs = []}     ¬p = ⊥-elim $ ¬p refl
¬Null⇒∃x {xs = x ∷ xs} _  = x , here refl

postulate Null-++⁻ : Null (xs ++ ys) → Null xs × Null ys

module _ (f : A → Maybe B) where
  Null-mapMaybe⁺ : Null xs → Null (mapMaybe f xs)
  Null-mapMaybe⁺ refl = refl

  -- Null-mapMaybe⁻ : Null (mapMaybe f xs) → M.All () (head xs) → Null xs
  -- Null-mapMaybe⁻ {xs = []}    refl _ = refl
  -- Null-mapMaybe⁻ {xs = x ∷ _} eq jx with f x | jx
  -- ... | just _  | _ = case eq of λ ()
  -- ... | nothing | fx = {!!}
