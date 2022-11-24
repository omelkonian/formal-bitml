------------------------------------------------------------------------
-- Types of actions.
------------------------------------------------------------------------
open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Sets
open import Prelude.ToList

open import BitML.BasicTypes

module BitML.Semantics.Action
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import BitML.Contracts.Types Participant Honest hiding (A; B)
open import BitML.Contracts.Helpers Participant Honest

--------------------------------------------------------------------------------

data Action : Set where

  -- commit secrets to stipulate {G}C
  ♯▷_ : Advertisement → Action

  -- spend x to stipulate {G}C
  _▷ˢ_ : Id → Advertisement → Action

  -- take branch
  _▷_ : Id → Contract → Action

  -- join deposits
  _↔_▷⟨_,_⟩ : Id → Id → Participant → Value → Action

  -- divide a deposit
  _▷⟨_,_,_⟩ : Id → Participant → Value → Value → Action

  -- donate deposit to participant
  _▷ᵈ_ : Id → Participant → Action

  -- destroy i-th deposit in xs through y
  _,_▷ᵈˢ_ : (xs : Ids) → Index (toList xs) → Id → Action

unquoteDecl DecEq-Action = DERIVE DecEq [ quote Action , DecEq-Action ]

Actions = List Action

variable
  act act′ : Action
  acts acts′ : Actions
