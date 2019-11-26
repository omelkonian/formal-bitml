------------------------------------------------------------------------
-- Examples of actions.
------------------------------------------------------------------------

module BitML.Semantics.Actions.Examples where

open import Data.Product      using (_,_)
open import Data.List         using ([]; _∷_)
open import Data.Fin.Patterns using (1F)

--------------------------------------------------------------------------------

open import BitML.Example.Setup using (Participant; _≟ₚ_; Honest; A; B)

open import Prelude.Lists
open import BitML.BasicTypes

open import BitML.Contracts.Types         Participant _≟ₚ_ Honest hiding (A; B)
open import BitML.Contracts.Examples
open import BitML.Semantics.Actions.Types Participant _≟ₚ_ Honest

--------------------------------------------------------------------------------

-- secret
_ : Action
_ = ♯▷ ex-ad

-- spend
_ : Action
_ = "x" ▷ˢ ex-ad

-- take branch
_ : Action
_ = "x" ▷ (ex-contracts₄ ‼ 1F)

-- join
_ : Action
_ = "x" ↔ "y" ▷⟨ A , 10 ⟩

-- divide
_ : Action
_ = "x" ▷⟨ A , 33 , 67 ⟩

-- donate
_ : Action
_ = "x" ▷ᵈ B

-- destroy
_ : Action
_ = ("x₁" ∷ "x₂" ∷ "x₃" ∷ []) , 1F ▷ᵈˢ "y"
