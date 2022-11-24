------------------------------------------------------------------------
-- Types of configurations.
------------------------------------------------------------------------
open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Coercions

open import BitML.BasicTypes

module BitML.Semantics.Configurations.Types
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import BitML.Contracts.Types Participant Honest
open import BitML.Semantics.Action Participant Honest

-------------------------------------------------------------------

ActiveContract = Contracts × Value × Id

data Configuration : Set where
  -- empty
  ∅ᶜ : Configuration

  -- contract advertisement
  `_ : (ad : Advertisement) → Configuration

  -- active contract
  ⟨_,_⟩at_ : (c : Contracts) → (v : Value) → (x : Id) → Configuration

  -- deposit redeemable by a participant
  ⟨_has_⟩at_ : (A : Participant) → (v : Value) → (x : Id) → Configuration

  -- authorization to perform an action
  _auth[_] : (A : Participant) → (a : Action) → Configuration

  -- committed secret
  ⟨_∶_♯_⟩ : (A : Participant) → (s : Secret) → (mn : Maybe ℕ) → Configuration

  -- revealed secret
  _∶_♯_ : (A : Participant) → (s : Secret) → (n : ℕ) → Configuration

  -- parallel composition
  _∣_ : Configuration → Configuration → Configuration
  -- _∣_ : Op₂ Configuration -- breaks DERIVE-DecEq :(

unquoteDecl DecEqᶜᶠ = DERIVE DecEq [ quote Configuration , DecEqᶜᶠ ]

variable Γ Γ′ Γ″ Γ₀ Γ₀′ Γ₀″ Δ Δ′ Δ″ L L′ L″ M M′ M″ : Configuration

||_ : List Configuration → Configuration
-- ||_ = foldl _∣_ ∅ᶜ
|| [] = ∅ᶜ
|| (Γ ∷ []) = Γ
|| (Γ ∷ Γs@(_ ∷ _)) = Γ ∣ || Γs

record TimedConfiguration : Set where
  constructor _at_
  field
    cfg  : Configuration
    time : Time
open TimedConfiguration public

unquoteDecl DecEqᵗᶜᶠ = DERIVE DecEq [ quote TimedConfiguration , DecEqᵗᶜᶠ ]

variable Γₜ Γₜ′ Γₜ″ Γₜ₀ Γₜ₀′ Γₜ₀″ Δₜ Δₜ′ Δₜ″ : TimedConfiguration

infix  11 ⟨_,_⟩at_
infix  10 ⟨_has_⟩at_
infix  8 _auth[_]
infix  7 ||_
infixl 6 _∣_
infix  5 _at_

Cfg = Configuration
Cfgᵗ = TimedConfiguration

∅ᵗ : Cfgᵗ
∅ᵗ = ∅ᶜ at 0

-- Alternative representation as list of atomic/base configurations.
data BaseCfg : Set where
  ``_ : (ad : Advertisement) → BaseCfg
  `⟨_,_⟩at_ : (c : Contracts) → (v : Value) → (x : Id) → BaseCfg
  `⟨_has_⟩at_ : (A : Participant) → (v : Value) → (x : Id) → BaseCfg
  _`auth[_] : (A : Participant) → (a : Action) → BaseCfg
  `⟨_∶_♯_⟩ : (A : Participant) → (s : Secret) → (mn : Maybe ℕ) → BaseCfg
  _`∶_♯_ : (A : Participant) → (s : Secret) → (n : ℕ) → BaseCfg
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
