------------------------------------------------------------------------
-- Types of configurations.
------------------------------------------------------------------------
open import Prelude.Init; open SetAsType
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Coercions

open import BitML.BasicTypes

module BitML.Semantics.Configurations.Types (⋯ : ⋯) (let open ⋯ ⋯) where

open import BitML.Contracts.Types ⋯
open import BitML.Semantics.Action ⋯

data Cfg : Type where
  -- empty
  ∅ᶜ : Cfg

  -- contract advertisement
  `_ : (ad : Ad) → Cfg

  -- active contract
  ⟨_,_⟩at_ : (c : Contract) → (v : Value) → (x : Id) → Cfg

  -- deposit redeemable by a participant
  ⟨_has_⟩at_ : (A : Participant) → (v : Value) → (x : Id) → Cfg

  -- authorization to perform an action
  _auth[_] : (A : Participant) → (a : Action) → Cfg

  -- committed secret
  ⟨_∶_♯_⟩ : (A : Participant) → (s : Secret) → (mn : Maybe ℕ) → Cfg

  -- revealed secret
  _∶_♯_ : (A : Participant) → (s : Secret) → (n : ℕ) → Cfg

  -- parallel composition
  _∣_ : Cfg → Cfg → Cfg
  -- _∣_ : Op₂ Cfg -- breaks DERIVE-DecEq :(

unquoteDecl DecEqᶜᶠ = DERIVE DecEq [ quote Cfg , DecEqᶜᶠ ]

variable Γ Γ′ Γ″ Γ₀ Γ₀′ Γ₀″ Δ Δ′ Δ″ L L′ L″ M M′ M″ : Cfg

||_ : List Cfg → Cfg
-- ||_ = foldl _∣_ ∅ᶜ
|| [] = ∅ᶜ
|| (Γ ∷ []) = Γ
|| (Γ ∷ Γs) = Γ ∣ || Γs

record Cfgᵗ : Type where
  constructor _at_
  field cfg  : Cfg
        time : Time
open Cfgᵗ public

unquoteDecl DecEqᵗᶜᶠ = DERIVE DecEq [ quote Cfgᵗ , DecEqᵗᶜᶠ ]

variable Γₜ Γₜ′ Γₜ″ Γₜ₀ Γₜ₀′ Γₜ₀″ Δₜ Δₜ′ Δₜ″ : Cfgᵗ

infix  11 ⟨_,_⟩at_
infix  10 ⟨_has_⟩at_
infix  8 _auth[_]
infix  7 ||_
infixl 6 _∣_
infix  5 _at_

∅ᵗ : Cfgᵗ
∅ᵗ = ∅ᶜ at 0

ActiveContract = Contract × Value × Id

-- Alternative representation as list of atomic/base configurations.
data BaseCfg : Type where
  ``_         : (ad : Ad) → BaseCfg
  `⟨_,_⟩at_   : (c : Contract) → (v : Value) → (x : Id) → BaseCfg
  `⟨_has_⟩at_ : (A : Participant) → (v : Value) → (x : Id) → BaseCfg
  _`auth[_]   : (A : Participant) → (a : Action) → BaseCfg
  `⟨_∶_♯_⟩    : (A : Participant) → (s : Secret) → (mn : Maybe ℕ) → BaseCfg
  _`∶_♯_      : (A : Participant) → (s : Secret) → (n : ℕ) → BaseCfg
unquoteDecl DecEqᵇᶜᶠ = DERIVE DecEq [ quote BaseCfg , DecEqᵇᶜᶠ ]

variable Γ¹ Γ¹′ Γ¹″ Δ¹ Δ¹′ Δ¹″ : BaseCfg

Cfg′ = List BaseCfg
pattern `∅ᶜ = []

instance
  BaseCfg↝Cfg : BaseCfg ↝ Cfg
  BaseCfg↝Cfg .to = λ where
    (`` ad) → ` ad
    (`⟨ c , v ⟩at x) → ⟨ c , v ⟩at x
    (`⟨ A has v ⟩at x) → ⟨ A has v ⟩at x
    ( A `auth[ a ]) → A auth[ a ]
    `⟨ A ∶ s ♯ mn ⟩ → ⟨ A ∶ s ♯ mn ⟩
    (A `∶ s ♯ n) → A ∶ s ♯ n

  Cfg′↝Cfg : Cfg′ ↝ Cfg
  Cfg′↝Cfg .to = ||_ ∘ map to

  Cfg↝Cfg′ : Cfg ↝ Cfg′
  Cfg↝Cfg′ .to = λ where
    ∅ᶜ → []
    (` ad) → [ `` ad ]
    (⟨ c , v ⟩at x) → [ `⟨ c , v ⟩at x ]
    (⟨ A has v ⟩at x) → [ `⟨ A has v ⟩at x ]
    (A auth[ a ]) → [ A `auth[ a ] ]
    ⟨ A ∶ s ♯ mn ⟩ → [ `⟨ A ∶ s ♯ mn ⟩ ]
    (A ∶ s ♯ n) → [ A `∶ s ♯ n ]
    (l ∣ r) → to l ++ to r
