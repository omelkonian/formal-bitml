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

-------------------------------------------------------------------
-- Basic types.

Value : Set
Value = ℕ

Values : Set
Values = List Value

Secret : Set
Secret = String

Secrets : Set
Secrets = List Secret

Time : Set
Time = ℕ

variable
  n : ℕ

  v v′ v″ : Value
  vs vs′ vs″ vsᶜ vsᵛ vsᵖ vsᵛₗ vsᵖₗ vsᵛᵣ vsᵖᵣ : Values

  s s′ s″ : Secret

-- Sets of values
module SETₙ = SET {A = Value} _≟ℕ_

Set⟨Value⟩ : Set
Set⟨Value⟩ = Set' where open SETₙ

-- Sets of secrets
_≟ₛ_ : Decidable {A = Secret} _≡_
_≟ₛ_ = _≟ₛ′_

module SETₛ = SET {A = Secret} _≟ₛ_

Set⟨Secret⟩ : Set
Set⟨Secret⟩ = Set' where open SETₛ
