------------------------------------------------------------------------
-- Basic BitML datatypes
------------------------------------------------------------------------
module BitML.BasicTypes where

open import Data.List   using (List)
open import Data.Nat    using (ℕ)
  renaming (_≟_ to _≟ℕ_)
open import Data.String using (String)
  renaming (_≟_ to _≟ₛ′_)

open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

import Prelude.Set' as SET

Value  = ℕ
Values = List Value

Secret  = String
Secrets = List Secret

Id  = String
Ids = List String

Name  = String
Names = List String

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
module SETₙ = SET {A = Value} _≟ℕ_
Set⟨Value⟩ = Set' where open SETₙ

-- Sets of secrets/ids/names
_≟ₛ_ : Decidable {A = String} _≡_
_≟ₛ_ = _≟ₛ′_
module SETₛ = SET {A = String} _≟ₛ_
Set⟨Secret⟩ = Set' where open SETₛ
Set⟨Id⟩ = Set' where open SETₛ
