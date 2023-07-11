------------------------------------------------------------------------
-- Examples of BitML contracts/advertisements.
------------------------------------------------------------------------

module BitML.Example.Contracts where

open import Data.Unit using (tt)
open import Data.List using (List; []; _∷_; [_])
open import Data.List.Relation.Unary.Any using (here; there)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.List.Relation.Binary.Sublist.Heterogeneous as SB

--------------------------------------------------------------------------------

open import Prelude.Lists

open import BitML.Example.Setup

open import BitML.BasicTypes
open import BitML.Predicate
open import BitML.Contracts.Types ⋯ Participant , Honest ⋯ hiding (A; B)

--------------------------------------------------------------------------------

ex-contracts₁ : Contract
ex-contracts₁ = withdraw A ∙

ex-contracts₂ : Contract
ex-contracts₂ = A ⇒ withdraw A
              ⊕ put [] ⇒ (withdraw A ∙)
              ∙

ex-contracts₃ : Contract
ex-contracts₃ = put [ "x" ] ⇒ (withdraw A ∙)
              ∙

ex-contracts₄ : Contract
ex-contracts₄ = A ⇒ withdraw B
              ⊕ B ⇒ split ( 2 ⊸ (withdraw A ∙)
                          ⊕ 3 ⊸ (after 100 ⇒ withdraw B ∙)
                          ⊕ 0 ⊸ (put [ "y" ] ⇒ (A ⇒ withdraw B ∙) ∙)
                          ∙)
              ∙


-- see BitML paper, Section 2
pay-or-refund : Ad
pay-or-refund = ⟨ A :! 1 at "x" ∣∣ B :! 0 at "y" ⟩
                ( A ⇒ withdraw B
                ⊕ B ⇒ withdraw A
                ∙)


ex-ad : Ad
ex-ad = ⟨ B :! 2 at "x" ∣∣ A :! 3 at "y" ∣∣ A :? 100 at "z" ⟩ ex-contracts₃
