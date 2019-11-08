------------------------------------------------------------------------
-- Types of actions.
------------------------------------------------------------------------

open import Data.Nat     using (_>_)
open import Data.Product using (Σ-syntax)
open import Data.List    using (List; length)

open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Prelude.Lists

open import BitML.BasicTypes

module BitML.Semantics.Actions.Types
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))
  where

open import BitML.Contracts.Types   Participant _≟ₚ_ Honest
open import BitML.Contracts.Helpers Participant _≟ₚ_ Honest

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
  _,_▷ᵈˢ_ : (xs : Ids) → Index xs → Id → Action
