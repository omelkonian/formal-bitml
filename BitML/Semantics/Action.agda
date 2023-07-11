------------------------------------------------------------------------
-- Types of actions.
------------------------------------------------------------------------
open import Prelude.Init; open SetAsType
open import Prelude.Lists
open import Prelude.DecEq

open import BitML.BasicTypes

module BitML.Semantics.Action (⋯ : ⋯) (let open ⋯ ⋯) where

open import BitML.Contracts.Types ⋯ hiding (A; B)
open import BitML.Contracts.Helpers ⋯

--------------------------------------------------------------------------------

data Action : Type where

  -- commit secrets to stipulate {G}C
  ♯▷_ : Ad → Action

  -- spend x to stipulate {G}C
  _▷ˢ_ : Id → Ad → Action

  -- take branch
  _▷_ : Id → Branch → Action

  -- join deposits
  _↔_▷⟨_,_⟩ : Id → Id → Participant → Value → Action

  -- divide a deposit
  _▷⟨_,_,_⟩ : Id → Participant → Value → Value → Action

  -- donate deposit to participant
  _▷ᵈ_ : Id → Participant → Action

  -- destroy i-th deposit in xs through y
  _,_▷ᵈˢ_ : (xs : Ids) → Index xs → Id → Action

unquoteDecl DecEq-Action = DERIVE DecEq [ quote Action , DecEq-Action ]

Actions = List Action

variable
  act act′ : Action
  acts acts′ : Actions
