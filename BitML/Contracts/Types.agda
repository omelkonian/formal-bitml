------------------------------------------------------------------------
-- BitML datatypes: Contracts & Advertisements
------------------------------------------------------------------------

open import Data.Product using (_×_; _,_; Σ-syntax; proj₁; proj₂)
open import Data.Nat     using (ℕ; _>_)
open import Data.List    using (List; []; _∷_; [_]; length; _++_; map; concatMap)

open import Relation.Binary using (Decidable)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Prelude.Lists
import Prelude.Set' as SET

open import BitML.BasicTypes
open import BitML.Predicate.Base

module BitML.Contracts.Types
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))
  where

Hon = proj₁ Honest

-- Sets of participants
module SETₚ = SET {A = Participant} _≟ₚ_

Set⟨Participant⟩ : Set
Set⟨Participant⟩ = Set' where open SETₚ

variable
  A B : Participant

------------------------------------------------------------------------
-- Contracts

data Contract : Set
Contracts = List Contract

data Contract where

  -- collect deposits and secrets
  put_&reveal_if_⇒_ : Ids → Secrets → Predicate → Contracts → Contract

  -- transfer the balance to a participant
  withdraw : Participant → Contract

  -- split the balance
  split : List (Value × Contracts) → Contract

  -- wait for participant's authorization
  _⇒_ : Participant → Contract → Contract

  -- wait of a period of time
  after_⇒_ : Time → Contract → Contract

variable
  d d′ : Contract
  c c′ : Contracts

_⊕_ : ∀ {A : Set} → A → List A → List A
_⊕_ = _∷_

_∙ : ∀ {A : Set} → A → List A
_∙ = [_]

_⊸_ : Value → Contracts → Value × Contracts
_⊸_ = _,_

put_&reveal_⇒_ : Ids → Secrets → Contracts → Contract
put xs &reveal as ⇒ c = put xs &reveal as if `true ⇒ c

put_⇒_ : Ids → Contracts → Contract
put xs ⇒ c = put xs &reveal [] ⇒ c

reveal_⇒_ : Secrets → Contracts → Contract
reveal as ⇒ c = put [] &reveal as ⇒ c


-------------------------------------------------------------------
-- Contract preconditions.

data Precondition : Set where

  -- volatile deposit
  _:?_at_ : Participant → Value → Id → Precondition

  -- persistent deposit
  _:!_at_ : Participant → Value → Id → Precondition

  -- committed secret (random nonce) by <Participant>
  _:secret_ : Participant → Secret → Precondition

  -- composition
  _∣∣_ : Precondition → Precondition → Precondition


------------------------------------------------------------------------
-- Advertisements.

record Advertisement : Set where
  constructor ⟨_⟩_

  field
    G : Precondition
    C : Contracts

open Advertisement public
variable ad ad′ : Advertisement

infix  2 ⟨_⟩_

infix  5 _:?_at_
infix  5 _:!_at_
infix  5 _:secret_
infixl 2 _∣∣_

infixr 9 _⇒_
infix  8 put_&reveal_if_⇒_
infix  8 put_&reveal_⇒_
infix  8 put_⇒_
infix  8 reveal_⇒_
infix  7 _⊸_
infix  6 _∙
infixr 5 _⊕_

DepositRef : Set
DepositRef = Participant × Value × Id
