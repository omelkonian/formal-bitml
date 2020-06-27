------------------------------------------------------------------------
-- Types of configurations.
------------------------------------------------------------------------
open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq

open import BitML.BasicTypes

module BitML.Semantics.Configurations.Types
  (Participant : Set)
  {{_ : DecEq Participant}}
  (Honest : List⁺ Participant)
  where

open import BitML.Contracts.Types Participant Honest
open import BitML.Semantics.Action Participant Honest

-------------------------------------------------------------------

data Configuration : Set where

  -- empty
  ∅ᶜ : Configuration

  -- contract advertisement
  `_ : Advertisement → Configuration

  -- active contract
  ⟨_,_⟩at_ : Contracts → Value → Id → Configuration

  -- deposit redeemable by a participant
  ⟨_has_⟩at_ : Participant → Value → Id → Configuration

  -- authorization to perform an action
  _auth[_] : Participant → Action → Configuration

  -- committed secret
  ⟨_∶_♯_⟩ : Participant → Secret → Maybe ℕ → Configuration

  -- revealed secret
  _∶_♯_ : Participant → Secret → ℕ → Configuration

  -- parallel composition
  _∣_ : Configuration → Configuration → Configuration

unquoteDecl DecEqᶜᶠ = DERIVE DecEq [ quote Configuration , DecEqᶜᶠ ]

variable
  Γ Γ′ Γ₀ Δ Δ′ L L′ M M′ : Configuration

||_ : List Configuration → Configuration
-- ||_ = foldl _∣_ ∅ᶜ
|| [] = ∅ᶜ
|| (Γ ∷ []) = Γ
|| (Γ ∷ Γs) = Γ ∣ || Γs

record TimedConfiguration : Set where
  constructor _at_
  field
    cfg  : Configuration
    time : Time
open TimedConfiguration public

unquoteDecl DecEqᵗᶜᶠ = DERIVE DecEq [ quote TimedConfiguration , DecEqᵗᶜᶠ ]

variable
  Γₜ Γₜ′ Γₜ″ : TimedConfiguration

infix  9 ⟨_,_⟩at_
infix  8 ⟨_has_⟩at_
infix  6 _auth[_]
infix  5 ||_
infixl 4 _∣_
infix  3 _at_
