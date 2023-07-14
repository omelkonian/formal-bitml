open import Prelude.Init; open SetAsType
open import Prelude.DecEq

open import BitML.BasicTypes

module BitML (⋯ : ⋯) where

open import BitML.Predicate public
open import BitML.Contracts ⋯ public
open import BitML.Semantics ⋯ public
open import BitML.Properties ⋯ public
open import BitML.BasicTypes public

open import BitML.Example.TimedCommitment
