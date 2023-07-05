open import Prelude.Init; open SetAsType
open import Prelude.DecEq

module BitML.Properties
  (Participant : Type) ⦃ _ : DecEq Participant ⦄ (Honest : List⁺ Participant)
  where

open import BitML.Properties.Helpers Participant Honest public
open import BitML.Properties.TraceAd Participant Honest public
open import BitML.Properties.TraceAuthCommit Participant Honest public
open import BitML.Properties.TraceAuthInit Participant Honest public
open import BitML.Properties.TraceInit Participant Honest public
open import BitML.Properties.TraceAuthControl Participant Honest public
open import BitML.Properties.Lifetime Participant Honest public
open import BitML.Properties.TraceContract Participant Honest public
