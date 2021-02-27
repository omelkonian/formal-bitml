open import Prelude.Init
open import Prelude.DecEq

module BitML.Contracts
  (Participant : Set) {{_ : DecEq Participant}} (Honest : List⁺ Participant)
  where

open import BitML.Contracts.Types     Participant Honest public
open import BitML.Contracts.Helpers   Participant Honest public
open import BitML.Contracts.Validity  Participant Honest public
module Induction where
  open import BitML.Contracts.Induction Participant Honest public
