------------------------------------------------------------------------
-- Basic BitML datatypes
------------------------------------------------------------------------

module Types where

open import Data.Nat           using (ℕ; _≟_)
open import Data.String        using (String)
open import Data.Bool          using (Bool)   renaming (_≟_ to _≟ᵇ_)
open import Data.String.Unsafe using ()       renaming (_≟_ to _≟ₛ_)

open import Relation.Nullary                      using (yes; no)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-------------------------------------------------------------------
-- Basic types.

Value : Set
Value = ℕ

-- T0D0: Move as indices in the Contract datatype
Identifier : Set
Identifier = String

Secret : Set
Secret = Identifier

Time : Set
Time = ℕ

-------------------------------------------------------------------
-- Contract participants.

-- T0D0: Move as module parameters
data Participant : Set where
  A : Participant
  B : Participant

-------------------------------------------------------------------
-- Deposits.

record Deposit : Set where
  constructor _∷_≙_[_]
  field
    participant : Participant
    value       : Value
    name        : Identifier
    persistent  : Bool
open Deposit public

-------------------------------------------------------------------
-- Contract preconditions.

data Precondition : Set where

  -- volatile deposit of <Value>$, expected from <Participant> (named <Identifier>)
  _:?_≙_ : Participant → Value → Identifier → Precondition

  -- persistent deposit of <Value>$, expected from <Participant> (named <Identifier>)
  _:!_≙_ : Participant → Value → Identifier → Precondition

  -- committed secret (random nonce) by <Participant>
  _:secret_ : Participant → Secret → Precondition

  -- composition
  _∣_ : Precondition → Precondition → Precondition

-------------------------------------------------------------------
-- Set modules/types.

import Data.Set' as SET

-- Sets of participants
_≟ₚ_ : Decidable {A = Participant} _≡_
A ≟ₚ A = yes refl
A ≟ₚ B = no λ ()
B ≟ₚ A = no λ ()
B ≟ₚ B = yes refl

module SETₚ = SET {A = Participant} _≟ₚ_

Set⟨Participant⟩ : Set
Set⟨Participant⟩ = Set'
  where open SETₚ

-- Sets of identifiers
module SETᵢ = SET {A = Identifier} _≟ₛ_

Set⟨Identifier⟩ : Set
Set⟨Identifier⟩ = Set'
  where open SETᵢ

-- Sets of deposits
_≟ₑ_ : Decidable {A = Deposit} _≡_
x ≟ₑ y with participant x ≟ₚ participant y
          | value       x ≟  value       y
          | name        x ≟ₛ name        y
          | persistent  x ≟ᵇ persistent  y
... | no ¬p    | _        | _        | _        = no λ{refl → ¬p refl}
... | _        | no ¬p    | _        | _        = no λ{refl → ¬p refl}
... | _        | _        | no ¬p    | _        = no λ{refl → ¬p refl}
... | _        | _        | _        | no ¬p    = no λ{refl → ¬p refl}
... | yes refl | yes refl | yes refl | yes refl = yes refl

module SETₑ = SET {A = Deposit} _≟ₑ_

Set⟨Deposit⟩ : Set
Set⟨Deposit⟩ = Set'
  where open SETₑ
