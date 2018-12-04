------------------------------------------------------------------------
-- Basic BitML datatypes
------------------------------------------------------------------------

module Types where

open import Data.Nat    using (ℕ)
open import Data.Bool   using (Bool)
open import Data.String using (String)
open import Level       using (Level)
open import Data.Product using (Σ-syntax)

-- Basic types
Value : Set
Value = ℕ

Identifier : Set
Identifier = String

Secret : Set
Secret = Identifier

Time : Set
Time = ℕ

-- Contract participants
data Participant : Set where
  A : Participant
  B : Participant

-- Contract preconditions
data Precondition : Set where

  -- volatile deposit of <Value>$, expected from <Participant> (named <String>)
  _:?_≙_ : Participant → Value → Identifier → Precondition

  -- persistent deposit of <Value>$, expected from <Participant> (named <String>)
  _:!_≙_ : Participant → Value → Identifier → Precondition

  -- committed secret (random nonce) by <Participant>
  _:secret_≙_ : Participant → Secret → Precondition

  -- composition
  _∣_ : Precondition → Precondition → Precondition
