module Prelude.Maps.Interface where

open import Prelude.Init
open import Prelude.General
open import Prelude.DecEq
open import Prelude.Decidable

import Relation.Binary.Reasoning.Setoid as BinSetoid

record Mapᴵ (K V : Set) (σ : Level) : Set (lsuc σ) where
  constructor mkMapᴵ
  field
    Map : Set σ

    ∅ : Map
    _∪_ : Op₂ Map -- left-biased

    _⁉_ : Map → K → Maybe V
    _∈ᵈ_ : K → Map → Set

    _♯_ : Rel₀ Map

  -- syntactic sugar
  syntax Map {K = K} {V = V} = Map⟨ K ↦ V ⟩

  -- operator precedence
  infix  5 _⁉_
  infixr 4 _∪_
  infix  3 _≈_ _∈ᵈ_ _∉ᵈ_
  _∉ᵈ_ : K → Map → Set
  k ∉ᵈ m = ¬ (k ∈ᵈ m)

  -- equivalence
  _≈_ : Rel₀ Map
  m ≈ m′ = ∀ k → m ⁉ k ≡ m′ ⁉ k

  ≈-refl : Reflexive _≈_
  ≈-refl _ = refl

  ≈-sym : Symmetric _≈_
  ≈-sym p k = sym (p k)

  ≈-trans : Transitive _≈_
  ≈-trans p q k = trans (p k) (q k)

  ≈-equiv : IsEquivalence _≈_
  ≈-equiv = record {refl = ≈-refl; sym = ≈-sym; trans = ≈-trans}

  ≈-setoid : Setoid σ 0ℓ
  ≈-setoid = record {Carrier = Map; _≈_ = _≈_; isEquivalence = ≈-equiv}

  module ≈-Reasoning = BinSetoid ≈-setoid

  -- derived relations
  ⟨_⊎_⟩≡_ : Map → Map → Map → Set
  ⟨ m ⊎ m′ ⟩≡ m″ = (m ♯ m′) × ((m ∪ m′) ≈ m″)

  _[_↦_] : Map → K → V → Set
  m [ k ↦ v ] = m ⁉ k ≡ just v

  _[_↦_]∅ : Map → K → V → Set
  m [ k ↦ v ]∅ = m [ k ↦ v ] × ∀ k′ → k′ ≢ k → k′ ∉ᵈ m

  field
    ⁉⇒∈ᵈ : ∀ {s k} → Is-just (s ⁉ k) → k ∈ᵈ s
    ∈ᵈ⇒⁉ : ∀ {s k} → k ∈ᵈ s → Is-just (s ⁉ k)

    -- _∪_ is left-biased
    ↦-∪⁺ˡ : ∀ {s₁ s₂ k v} → s₁ [ k ↦ v ] → (s₁ ∪ s₂) [ k ↦ v ]
    ↦-∪⁺ʳ : ∀ {s₁ s₂ k} → k ∉ᵈ s₁ → s₂ ⁉ k ≡ (s₁ ∪ s₂) ⁉ k

    -- commutativity
    ♯-comm : Symmetric _♯_
    ∪-comm : ∀ {s₁}{s₂} → s₁ ♯ s₂ → (s₁ ∪ s₂) ≈ (s₂ ∪ s₁)

    -- congruences
    ♯-cong : ∀ {s₁ s₂ s₃} → s₁ ≈ s₂ → s₁ ♯ s₃ → s₂ ♯ s₃
    ∪-cong : ∀ {s₁ s₂ s₃} → s₁ ≈ s₂ → (s₁ ∪ s₃) ≈ (s₂ ∪ s₃)
    ∈ᵈ-cong : ∀ {k s₁ s₂} → s₁ ≈ s₂ → k ∈ᵈ s₁ → k ∈ᵈ s₂

    -- introduction/elimination of union
    ∈ᵈ-∪⁻ : ∀ k s₁ s₂ → k ∈ᵈ (s₁ ∪ s₂) → (k ∈ᵈ s₁) ⊎ (k ∈ᵈ s₂)
    ∈ᵈ-∪⁺ : ∀ k s₁ s₂ → (k ∈ᵈ s₁) ⊎ (k ∈ᵈ s₂) → k ∈ᵈ (s₁ ∪ s₂)
    ∪-chooseₗ : ∀ {s₁ s₂} → s₁ ♯ s₂ → (∀ {k} → k ∉ᵈ s₂ → (s₁ ∪ s₂) ⁉ k ≡ s₁ ⁉ k)
    ∪-chooseᵣ : ∀ {s₁ s₂} → s₁ ♯ s₂ → (∀ {k} → k ∈ᵈ s₂ → (s₁ ∪ s₂) ⁉ k ≡ s₂ ⁉ k)

    ♯-∪⁻ʳ : ∀ {s₁}{s₂}{s₃} → s₁ ♯ (s₂ ∪ s₃) → (s₁ ♯ s₂) × (s₁ ♯ s₃)
    ♯-∪⁻ˡ : ∀ {s₁}{s₂}{s₃} → (s₁ ∪ s₂) ♯ s₃ → (s₁ ♯ s₃) × (s₂ ♯ s₃)
    ♯-∪⁺ˡ : ∀ {s₁}{s₂}{s₃} → (s₁ ♯ s₃) × (s₂ ♯ s₃) → (s₁ ∪ s₂) ♯ s₃
    ♯-∪⁺ʳ : ∀ {s₁}{s₂}{s₃} → (s₁ ♯ s₂) × (s₁ ♯ s₃) → s₁ ♯ (s₂ ∪ s₃)

    -- associativity
    ∪-assocʳ : ∀ {s₁ s₂ s₃} → s₁ ∪ (s₂ ∪ s₃) ≈ (s₁ ∪ s₂) ∪ s₃
    ∪≡-assocʳ : ∀ {s₁}{s₂}{s₃}{s} → s₂ ♯ s₃ → ⟨ s₁ ⊎ (s₂ ∪ s₃) ⟩≡ s → ⟨ (s₁ ∪ s₂) ⊎ s₃ ⟩≡ s

    -- ⊎≈-assocʳ : ∀ {s₁}{s₂₃}{s}{s₂}{s₃} → ⟨ s₁ ⊎ s₂₃ ⟩≡ s → ⟨ s₂ ⊎ s₃  ⟩≡ s₂₃ → ⟨ (s₁ ∪ s₂) ⊎ s₃ ⟩≡ s × (s₁ ♯ s₂)
    -- ⊎≈-assocˡ : ∀ {s₁₂}{s₃}{s}{s₁}{s₂} → ⟨ s₁₂ ⊎ s₃ ⟩≡ s → ⟨ s₁ ⊎ s₂  ⟩≡ s₁₂ → ⟨ s₁ ⊎ (s₂ ∪ s₃) ⟩≡ s × (s₂ ♯ s₃)
  ⁉⇒∉ᵈ : ∀ {s k} → Is-nothing (s ⁉ k) → k ∉ᵈ s
  ⁉⇒∉ᵈ {s}{k} p k∈ with s ⁉ k | p | ∈ᵈ⇒⁉ k∈
  ... | just _ | M.All.just () | _

  ∉ᵈ⇒⁉ : ∀ {s k} → k ∉ᵈ s → Is-nothing (s ⁉ k)
  ∉ᵈ⇒⁉ {s}{k} k∉ with s ⁉ k | ⁉⇒∈ᵈ {s}{k}
  ... | just _  | p = ⊥-elim $ k∉ (p auto)
  ... | nothing | _ = auto

  ↦-∪⁺ʳ′ : ∀ {s₁ s₂ k v} → k ∉ᵈ s₁ → s₂ [ k ↦ v ] → (s₁ ∪ s₂) [ k ↦ v ]
  ↦-∪⁺ʳ′ {s₁}{s₂}{k}{v} k∉ sk≡ = trans (sym (↦-∪⁺ʳ k∉)) sk≡

  ∪-congʳ : ∀ {s₁}{s₂}{s₃} → s₁ ♯ s₂ → s₂ ≈ s₃ → (s₁ ∪ s₂) ≈ (s₁ ∪ s₃)
  ∪-congʳ {s₁}{s₂}{s₃} s₁♯s₂ s₂≈s₃ =
    begin s₁ ∪ s₂ ≈⟨ ∪-comm s₁♯s₂ ⟩
          s₂ ∪ s₁ ≈⟨ ∪-cong s₂≈s₃ ⟩
          s₃ ∪ s₁ ≈⟨ ∪-comm (♯-cong s₂≈s₃ $ ♯-comm s₁♯s₂) ⟩
          s₁ ∪ s₃ ∎
    where open ≈-Reasoning

  ∈ᵈ-∪⁺ˡ : ∀ k s₁ s₂ → k ∈ᵈ s₁ → k ∈ᵈ (s₁ ∪ s₂)
  ∈ᵈ-∪⁺ˡ _ _ _ = ∈ᵈ-∪⁺ _ _ _ ∘ inj₁
  ∈ᵈ-∪⁺ʳ : ∀ k s₁ s₂ → k ∈ᵈ s₂ → k ∈ᵈ (s₁ ∪ s₂)
  ∈ᵈ-∪⁺ʳ _ _ _ = ∈ᵈ-∪⁺ _ _ _ ∘ inj₂

  infix 3 _⊆ᵈ_ _⊈ᵈ_
  _⊆ᵈ_ _⊈ᵈ_ : Rel₀ Map
  m ⊆ᵈ m′ = ∀ k → k ∈ᵈ m → k ∈ᵈ m′
  k ⊈ᵈ m = ¬ (k ⊆ᵈ m)

  private
    variable
      s s₁ s₂ s₃ s₁₂ s₂₃ : Map
      k : K
      v : V

  ≈-cong : ∀ {P : K → Maybe V → Set}
    → s₁ ≈ s₂
    → (∀ k → P k (s₁ ⁉ k))
    → (∀ k → P k (s₂ ⁉ k))
  ≈-cong {P = P} eq p k = subst (P k) (eq k) (p k)

  ∉ᵈ-∪⁻ : k ∉ᵈ (s₁ ∪ s₂) → (k ∉ᵈ s₁) × (k ∉ᵈ s₂)
  ∉ᵈ-∪⁻ {k}{s₁}{s₂} k∉ = (k∉ ∘ ∈ᵈ-∪⁺ k s₁ s₂ ∘ inj₁) , (k∉ ∘ ∈ᵈ-∪⁺ k s₁ s₂ ∘ inj₂)

  ∉ᵈ-∪⁺ : (k ∉ᵈ s₁) × (k ∉ᵈ s₂) → k ∉ᵈ (s₁ ∪ s₂)
  ∉ᵈ-∪⁺ {k}{s₁}{s₂} (k∉₁ , k∉₂) k∈ = case ∈ᵈ-∪⁻ k s₁ s₂ k∈ of λ where
    (inj₁ k∈₁) → k∉₁ k∈₁
    (inj₂ k∈₂) → k∉₂ k∈₂

  ∪≡-comm : Symmetric (⟨_⊎_⟩≡ s)
  ∪≡-comm (s₁♯s₂ , ≡s) = ♯-comm s₁♯s₂ , ≈-trans (≈-sym $ ∪-comm s₁♯s₂) ≡s

  ∪≡-cong : s₁ ≈ s₂ → ⟨ s₁ ⊎ s₃ ⟩≡ s → ⟨ s₂ ⊎ s₃ ⟩≡ s
  ∪≡-cong eq (s₁♯s₃ , ≡s) = ♯-cong eq s₁♯s₃ , ≈-trans (≈-sym (∪-cong eq)) ≡s

  ∪-assocˡ : (s₁ ∪ s₂) ∪ s₃ ≈ s₁ ∪ (s₂ ∪ s₃)
  ∪-assocˡ = ≈-sym ∪-assocʳ

  ⊎≈-assocʳ :
      ⟨ s₁ ⊎ s₂₃ ⟩≡ s
    → ⟨ s₂ ⊎ s₃  ⟩≡ s₂₃
      ---------------------
    → ⟨ (s₁ ∪ s₂) ⊎ s₃ ⟩≡ s
    × (s₁ ♯ s₂)
  ⊎≈-assocʳ {s₁}{s₂₃}{s}{s₂}{s₃} (s₁♯s₂₃ , ≡s) (s₂♯s₃ , ≡s₂₃) =
    ∪≡-assocʳ s₂♯s₃ ≡ss , proj₁ (♯-∪⁻ʳ s₁♯s₂₃′)
    where
      s₁♯s₂₃′ : s₁ ♯ (s₂ ∪ s₃)
      s₁♯s₂₃′ = ♯-comm $ ♯-cong (≈-sym ≡s₂₃) $ ♯-comm s₁♯s₂₃

      ≡ss : ⟨ s₁ ⊎ (s₂ ∪ s₃) ⟩≡ s
      ≡ss = s₁♯s₂₃′ , ≈-trans (≈-trans (∪-comm s₁♯s₂₃′) (≈-trans (∪-cong ≡s₂₃) (≈-sym $ ∪-comm s₁♯s₂₃))) ≡s

  ∪≡-assocˡ : ∀ {s₁ s₂ s₃ s} → s₁ ♯ s₂ → ⟨ (s₁ ∪ s₂) ⊎ s₃ ⟩≡ s → ⟨ s₁ ⊎ (s₂ ∪ s₃)  ⟩≡ s
  ∪≡-assocˡ {s₁}{s₂}{s₃}{s} s₁♯s₂ p@(s₁₂♯s₃ , _) =
      ∪≡-comm ∘ ∪≡-assocʳ (♯-comm $ proj₁ $ ♯-∪⁻ˡ s₁₂♯s₃)
    $ ∪≡-comm ∘ ∪≡-assocʳ s₁♯s₂
    $ ∪≡-comm p

  ⊎≈-assocˡ :
      ⟨ s₁₂ ⊎ s₃ ⟩≡ s
    → ⟨ s₁ ⊎ s₂  ⟩≡ s₁₂
      ---------------------
    → ⟨ s₁ ⊎ (s₂ ∪ s₃) ⟩≡ s
    × (s₂ ♯ s₃)
  ⊎≈-assocˡ {s₁₂}{s₃}{s}{s₁}{s₂} (s₁₂♯s₃ , ≡s) (s₁♯s₂ , ≡s₁₂) =
    ∪≡-assocˡ s₁♯s₂ ≡ss , proj₂ (♯-∪⁻ˡ {s₁ = s₁} s₁₂♯s₃′)
    where
      s₁₂♯s₃′ : (s₁ ∪ s₂) ♯ s₃
      s₁₂♯s₃′ = ♯-cong (≈-sym ≡s₁₂) s₁₂♯s₃

      ≡ss : ⟨ (s₁ ∪ s₂) ⊎ s₃ ⟩≡ s
      ≡ss = s₁₂♯s₃′ , ≈-trans (∪-cong ≡s₁₂) ≡s

record DecMapᴵ (K V : Set) (σ : Level) ⦃ _ : DecEq K ⦄ : Set (lsuc σ) where
  constructor mkDecMapᴵ
  open Mapᴵ ⦃...⦄
  field
    ⦃ mapᴵ ⦄ : Mapᴵ K V σ
    _∈ᵈ?_ : Decidable² _∈ᵈ_

    singleton : K × V → Map
    singleton-law : ∀ {k v} → singleton (k , v) [ k ↦ v ]∅
    singleton∈ : ∀ {A v k} → k ∈ᵈ singleton (A , v) → k ≡ A
    singleton♯ : ∀ {k v k′ v′} → k ≢ k′ → singleton (k , v) ♯ singleton (k′ , v′)
    singleton-collapse : ∀ {k v v′} → singleton (k , v) ∪ singleton (k , v′) ≈ singleton (k , v)

  update : K × V → Map → Map
  update entry = singleton entry ∪_

  KeyMonotonic : (Map → Map) → Set σ
  KeyMonotonic f = ∀ s → s ⊆ᵈ f s

  KeyPreserving : (Map → Map) → Set σ
  KeyPreserving f = ∀ s → f s ⊆ᵈ s

  update-mon : ∀ {k v} → KeyMonotonic (update (k , v))
  update-mon s _ = ∈ᵈ-∪⁺ʳ _ _ _

  singleton-law′ : ∀ {k v} → singleton (k , v) [ k ↦ v ]
  singleton-law′ {k}{v} = proj₁ $ singleton-law {k}{v}

  field
    ≡-cong-update : ∀ {k′ k : K} {v} {s₁ s₂ : Map}
      → s₁ ⁉ k′ ≡ s₂ ⁉ k′ → update (k , v) s₁ ⁉ k′ ≡ update (k , v) s₂ ⁉ k′
    ♯-cong-pre : ∀ {s₁ s₂ : Map} {f : Map → Map} → KeyPreserving f → s₁ ♯ s₂ → f s₁ ♯ s₂

  ≈-cong-update : ∀ {k v s₁ s₂} → s₁ ≈ s₂ → update (k , v) s₁ ≈ update (k , v) s₂
  ≈-cong-update {k = k} s₁≈s₂ = ≡-cong-update ∘ s₁≈s₂

  infix 3 _∈ᵈ?_ _∉ᵈ?_
  _∉ᵈ?_ : Decidable² _∉ᵈ_
  k ∉ᵈ? m = ¬? (k ∈ᵈ? m)

  instance
    Dec-∈ᵈ : ∀ {k : K} {m : Map} → (k ∈ᵈ m) ⁇
    Dec-∈ᵈ .dec = _∈ᵈ?_ _ _

  singleton≈ : ∀ {m : Map} {k v} → m [ k ↦ v ]∅ → m ≈ singleton (k , v)
  singleton≈ {m}{k}{v} (eq , p) k′
    with k′ ≟ k
  ... | yes refl = trans eq (sym singleton-law′)
  ... | no  ≢k
    with m ⁉ k′ | ⁉⇒∈ᵈ {s = m} {k = k′}
  ... | just _  | q = ⊥-elim $ p k′ ≢k (q auto)
  ... | nothing | _
    with singleton (k , v) ⁉ k′ | ⁉⇒∈ᵈ {s = singleton (k , v)} {k = k′}
  ... | just _  | q = ⊥-elim $ ≢k (singleton∈ (q auto))
  ... | nothing | _ = refl

  update-update : ∀ {k v v′} {s : Map} → update (k , v′) (update (k , v) s) ≈ update (k , v′) s
  update-update {k}{v}{v′}{s} =
    begin
      update (k , v′) (update (k , v) s)
    ≡⟨⟩
      singleton (k , v′) ∪ (singleton (k , v) ∪ s)
    ≈⟨ ∪-assocʳ ⟩
      (singleton (k , v′) ∪ singleton (k , v)) ∪ s
    ≈⟨ ∪-cong singleton-collapse ⟩
      singleton (k , v′) ∪ s
    ≡⟨⟩
      update (k , v′) s
    ∎ where open ≈-Reasoning

  singleton-accept : ∀ {k v} {s : Map} → (singleton (k , v) ∪ s) ⁉ k ≡ just v
  singleton-accept {k}{v}{s} rewrite ↦-∪⁺ˡ {s₂ = s}{k}{v} singleton-law′ = refl

  singleton-reject : ∀ {k k′ v} {s : Map} → k′ ≢ k → (singleton (k , v) ∪ s) ⁉ k′ ≡ s ⁉ k′
  singleton-reject {k}{k′}{v}{s} k≢
    with ¿ k′ ∈ᵈ singleton (k , v) ¿
  ... | yes k∈ = ⊥-elim $ k≢ (singleton∈ k∈)
  ... | no k∉ rewrite ↦-∪⁺ʳ {s₂ = s} k∉ = refl

  data Cmd : Set₁ where
    _∶_ : Cmd → Cmd → Cmd
    _≔_ : K → V → Cmd
    iff : ∀ {P : Set} → Dec P → Cmd → Cmd
    just? : K → (V → Cmd) → Cmd

  infix 4 _≔_

  run : Cmd → (Map → Map)
  run (k ≔ v) = update (k , v)
  run (cmd₁ ∶ cmd₂) = run cmd₂ ∘ run cmd₁
  run (iff b cmd) with b
  ... | yes _ = run cmd
  ... | no  _ = id
  run (just? k go) s with s ⁉ k
  ... | just v  = run (go v) s
  ... | nothing = s

  ≈-cong-cmd : ∀ {s₁ s₂} cmd → s₁ ≈ s₂ → run cmd s₁ ≈ run cmd s₂
  ≈-cong-cmd {s₁} {s₂} (cmd₁ ∶ cmd₂) s₁≈s₂ k = ≈-cong-cmd cmd₂ (≈-cong-cmd cmd₁ s₁≈s₂) k
  ≈-cong-cmd {s₁} {s₂} (_ ≔ _) s₁≈s₂ k = ≈-cong-update s₁≈s₂ k
  ≈-cong-cmd {s₁} {s₂} (iff b cmd) s₁≈s₂ k
    with b
  ... | yes _ = ≈-cong-cmd cmd s₁≈s₂ k
  ... | no  _ = s₁≈s₂ k
  ≈-cong-cmd {s₁} {s₂} (just? k′ go) s₁≈s₂ k
    with s₁ ⁉ k′ | s₂ ⁉ k′ | s₁≈s₂ k′
  ... | nothing | .nothing  | refl = s₁≈s₂ k
  ... | just v  | .(just v) | refl = ≈-cong-cmd (go v) s₁≈s₂ k

  cmd-mon : ∀ cmd → KeyMonotonic (run cmd)
  cmd-mon (cmd₁ ∶ cmd₂) s k = cmd-mon cmd₂ (run cmd₁ s) k ∘ cmd-mon cmd₁ s k
  cmd-mon (k′ ≔ v) = update-mon
  cmd-mon (iff b cmd) with b
  ... | yes _ = cmd-mon cmd
  ... | no  _ = λ _ _ → id
  cmd-mon (just? k′ go) s with s ⁉ k′
  ... | just v  = cmd-mon (go v) s
  ... | nothing = λ _ → id

  just?-accept : ∀ {s k v go}
    → s [ k ↦ v ]
    → run (just? k go) s ≈ run (go v) s
  just?-accept {s}{k}{v} eq _ with s ⁉ k | eq
  ... | just v | refl = refl

  just?-reject : ∀ {s : Map} {k} {v : V} {go}
    → k ∉ᵈ s
    → run (just? k go) s ≈ s
  just?-reject {s}{k}{v} k∉ _ with s ⁉ k | ⁉⇒∈ᵈ {s = s} {k = k}
  ... | just _  | p = ⊥-elim $ k∉ (p auto)
  ... | nothing | _ = refl

  iff-accept : ∀ {s cmd} {P : Set} {b : Dec P}
    → True b
    → run (iff b cmd) s ≈ run cmd s
  iff-accept {b = b} ≡yes _ with b | ≡yes
  ... | yes _ | _ = refl


record DecEqMapᴵ (K V : Set) ⦃ _ : DecEq K ⦄ (σ : Level) : Set (lsuc σ) where
  constructor mkDecEqMapᴵ
  open Mapᴵ ⦃...⦄
  field
    ⦃ mapᴵ ⦄ : Mapᴵ K V σ
    deceq : DecEq Map
  instance
    DecEq-Map : DecEq Map
    DecEq-Map = deceq
