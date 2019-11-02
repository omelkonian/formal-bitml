------------------------------------------------------------------------
-- Examples of labels.
------------------------------------------------------------------------

module BitML.Semantics.Labels.Examples where

open import Data.List    using (List; []; _∷_; [_])

open import Relation.Nullary.Decidable            using (fromWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

--------------------------------------------------------------------------------

open import BitML.Example.Setup using (Participant; _≟ₚ_; Honest; A; B)

open import BitML.BasicTypes             Participant _≟ₚ_ Honest
open import BitML.Contracts.Types        Participant _≟ₚ_ Honest
open import BitML.Semantics.Labels.Types Participant _≟ₚ_ Honest

--------------------------------------------------------------------------------

-- empty
_ = empty

-- join
_ = auth-join[ A , 0 ↔ 1 ]
_ = join[ 0 ↔ 1 ]
