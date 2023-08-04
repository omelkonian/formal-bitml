open import Prelude.Init; open SetAsType
open import Prelude.DecEq

open import BitML.BasicTypes using (⋯)

module BitML (⋯ : ⋯) where

open import BitML.BasicTypes public hiding (⋯; ⋯_,_⋯)
open import BitML.Predicate public
open import BitML.Contracts ⋯ public
open import BitML.Example.Contracts
open import BitML.Semantics ⋯ public
open import BitML.Example.TimedCommitment
open import BitML.Properties ⋯ public
