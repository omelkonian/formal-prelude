{-# OPTIONS --safe #-}
module Prelude.Membership.Patterns where

open import Prelude.Init
open L.Any
open V.Any

pattern 𝟘 = here refl
pattern 𝟙 = there 𝟘
pattern 𝟚 = there 𝟙
pattern 𝟛 = there 𝟚
pattern 𝟜 = there 𝟛
pattern 𝟝 = there 𝟜
pattern 𝟞 = there 𝟝
pattern 𝟟 = there 𝟞
pattern 𝟠 = there 𝟟
pattern 𝟡 = there 𝟠

_ = 1 L.Mem.∈ [ 1 ⨾ 2 ]
  ∋ 𝟘
_ = 2 L.Mem.∈ [ 1 ⨾ 2 ]
  ∋ 𝟙
_ = 1 V.Mem.∈ [ 1 ⨾ 2 ]
  ∋ 𝟘
_ = 2 V.Mem.∈ [ 1 ⨾ 2 ]
  ∋ 𝟙

pattern 𝟘⊥ = here ()
pattern 𝟙⊥ = there 𝟘⊥
pattern 𝟚⊥ = there 𝟙⊥
pattern 𝟛⊥ = there 𝟚⊥
pattern 𝟜⊥ = there 𝟛⊥
pattern 𝟝⊥ = there 𝟜⊥
pattern 𝟞⊥ = there 𝟝⊥
pattern 𝟟⊥ = there 𝟞⊥
pattern 𝟠⊥ = there 𝟟⊥
pattern 𝟡⊥ = there 𝟠⊥

_ = 4 L.Mem.∉ [ 1 ⨾ 2 ⨾ 3 ]
  ∋ λ where 𝟘⊥; 𝟙⊥; 𝟚⊥
_ = 4 V.Mem.∉ [ 1 ⨾ 2 ⨾ 3 ]
  ∋ λ where 𝟘⊥; 𝟙⊥; 𝟚⊥
