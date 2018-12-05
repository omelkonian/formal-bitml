------------------------------------------------------------------------
-- Basic BitML datatypes
------------------------------------------------------------------------

module Types where

open import Data.Bool   using (Bool)
open import Data.Nat    using (ℕ)
open import Data.String using (String)

-------------------------------------------------------------------
-- Basic types.

Value : Set
Value = ℕ

Identifier : Set
Identifier = String

Secret : Set
Secret = Identifier

Time : Set
Time = ℕ

-------------------------------------------------------------------
-- Contract participants.

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

  -- volatile deposit of <Value>$, expected from <Participant> (named <String>)
  _:?_≙_ : Participant → Value → Identifier → Precondition

  -- persistent deposit of <Value>$, expected from <Participant> (named <String>)
  _:!_≙_ : Participant → Value → Identifier → Precondition

  -- committed secret (random nonce) by <Participant>
  _:secret_ : Participant → Secret → Precondition

  -- composition
  _∣_ : Precondition → Precondition → Precondition
