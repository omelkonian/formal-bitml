------------------------------------------------------------------------
-- Basic BitML datatypes
------------------------------------------------------------------------
module BitML.BasicTypes where

open import Data.Nat    using (ℕ)
  renaming (_≟_ to _≟ℕ_)
open import Data.String using (String)
  renaming (_≟_ to _≟ₛ′_)
open import Data.List   using (List)
open import Data.Sum    using (_⊎_)
open import Data.Sum.Properties using (≡-dec)

open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

import Prelude.Set' as SET

Value  = ℕ
Values = List Value

Secret  = String
Secrets = List Secret

Id  = String
Ids = List String

Name : Set
Name = Secret ⊎ Id
Names = List Name

Time = ℕ

variable
  n : ℕ

  v v′ : Value
  vs vs′ : Values

  a a′ : Secret
  as as′ : Secrets

  x y z x′ y′ z′ : Id
  xs xs′ : Ids

  t t′ δ : Time

-- Sets of (time) values
module SETᵥ = SET {A = Value} _≟ℕ_
Set⟨Value⟩ = Set' where open SETᵥ

-- Sets of secrets/ids
_≟ₛ_ : Decidable {A = String} _≡_
_≟ₛ_ = _≟ₛ′_
module SETₛ = SET {A = String} _≟ₛ_
Set⟨Secret⟩ = Set' where open SETₛ
Set⟨Id⟩ = Set' where open SETₛ

-- Sets of names
_≟ₙ_ : Decidable {A = Name} _≡_
_≟ₙ_ = ≡-dec _≟ₛ_ _≟ₛ_
module SETₙ = SET {A = Name} _≟ₙ_
Set⟨Name⟩ = Set' where open SETₙ
