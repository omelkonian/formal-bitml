------------------------------------------------------------------------
-- Examples of actions.
------------------------------------------------------------------------

module BitML.Example.Actions where

open import Data.Product using (_,_)
open import Data.Fin     using (#_)

open import Prelude.Lists

open import BitML.Example.Setup
open import BitML.Example.Contracts

open import BitML.BasicTypes
open import BitML.Predicate
open import BitML.Contracts.Types Participant Honest hiding (A; B)
open import BitML.Semantics.Action Participant Honest


-- secret
_ = ♯▷ ex-ad
-- spend
_ = "x" ▷ˢ ex-ad
-- take branch
_ = "x" ▷ (ex-contracts₄ ‼ # 1)
-- join
_ = "x" ↔ "y" ▷⟨ A , 10 ⟩
-- divide
_ = "x" ▷⟨ A , 33 , 67 ⟩
-- donate
_ = "x" ▷ᵈ B
-- destroy
_ = ⟦ "x₁" , "x₂" , "x₃" ⟧ , # 1 ▷ᵈˢ "y"
