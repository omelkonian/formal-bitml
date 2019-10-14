------------------------------------------------------------------------
-- Examples of labels.
------------------------------------------------------------------------

module Semantics.Labels.Examples where

open import Data.List    using (List; []; _∷_; [_])

open import Relation.Nullary.Decidable            using (fromWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

--------------------------------------------------------------------------------

open import Example.Setup using (Participant; _≟ₚ_; Honest; A; B)

open import Types                  Participant _≟ₚ_ Honest
open import BitML.Types            Participant _≟ₚ_ Honest
open import Semantics.Labels.Types Participant _≟ₚ_ Honest

--------------------------------------------------------------------------------

-- empty
_ = empty

-- join
_ = auth-join[ A , 0 ↔ 1 ]
_ = join[ 0 ↔ 1 ]
