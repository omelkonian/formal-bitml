------------------------------------------------------------------------
-- Examples of BitML contracts/advertisements.
------------------------------------------------------------------------

module BitML.Example.Contracts where

open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Sets

open import BitML.Example.Setup

open import BitML.BasicTypes
open import BitML.Predicate
open import BitML.Contracts.Types Participant Honest hiding (A; B)

--------------------------------------------------------------------------------

ex-contracts₁ : Contracts
ex-contracts₁ = withdraw A ∙

ex-contracts₂ : Contracts
ex-contracts₂ = A ⇒ withdraw A
              ⊕ put ∅ ⇒ (withdraw A ∙)
              ∙

ex-contracts₃ : Contracts
ex-contracts₃ = put (singleton "x") ⇒ (withdraw A ∙)
              ∙

ex-contracts₄ : Contracts
ex-contracts₄ = A ⇒ withdraw B
              ⊕ B ⇒ split ( 2 ⊸ (withdraw A ∙)
                          ⊕ 3 ⊸ (after 100 ⇒ withdraw B ∙)
                          ⊕ 0 ⊸ (put (singleton "y") ⇒ (A ⇒ withdraw B ∙) ∙)
                          ∙)
              ∙


-- see BitML paper, Section 2
pay-or-refund : Advertisement
pay-or-refund = ⟨ A :! 1 at "x" ∣∣ B :! 0 at "y" ⟩
                ( A ⇒ withdraw B
                ⊕ B ⇒ withdraw A
                ∙)


ex-ad : Advertisement
ex-ad = ⟨ B :! 2 at "x" ∣∣ A :! 3 at "y" ∣∣ A :? 100 at "z" ⟩ ex-contracts₃
