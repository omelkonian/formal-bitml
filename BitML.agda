open import Prelude.Init; open SetAsType
open import Prelude.DecEq

module BitML
  (Participant : Type) ⦃ _ : DecEq Participant ⦄ (Honest : List⁺ Participant)
  where

open import BitML.BasicTypes public
open import BitML.Predicate public
open import BitML.Contracts Participant Honest public
open import BitML.Semantics Participant Honest public
open import BitML.Properties Participant Honest public

open import BitML.Example.Main
