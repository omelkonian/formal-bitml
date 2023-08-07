------------------------------------------------------------------------
-- Module macros for working with BitML contracts.
------------------------------------------------------------------------
open import Prelude.Init; open SetAsType
open import Prelude.Lists.Indexed

open import BitML.BasicTypes
open import BitML.Predicate

module BitML.Contracts.ModuleMacros ⋯ (let open ⋯ ⋯) where

open import BitML.Contracts.Types ⋯ hiding (d; C; G)
open import BitML.Contracts.Collections ⋯

-- selecting a sub-contract and stripping decorations
module ∣SELECT (c : Contract) (i : Index c) where
  d  = c ‼ i
  d∗ = removeTopDecorations d

-- opening an advertisement to get the underlying contract and preconditions,
-- as well as the involved participants
module ∣AD (ad : Ad) where
  C = ad .Ad.C
  G = ad .Ad.G
  partG = nub-participants G
