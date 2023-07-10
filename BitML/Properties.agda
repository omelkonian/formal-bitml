open import Prelude.Init; open SetAsType
open import Prelude.DecEq

open import BitML.BasicTypes

module BitML.Properties (⋯ : ⋯) where

open import BitML.Properties.Helpers ⋯ public
open import BitML.Properties.TraceAd ⋯ public
open import BitML.Properties.TraceAuthCommit ⋯ public
open import BitML.Properties.TraceAuthInit ⋯ public
open import BitML.Properties.TraceInit ⋯ public
open import BitML.Properties.TraceAuthControl ⋯ public
open import BitML.Properties.Lifetime ⋯ public
open import BitML.Properties.TraceContract ⋯ public
