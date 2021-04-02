------------------------------------------------------------------------
-- BitML datatypes: Contracts & Advertisements
------------------------------------------------------------------------
import Data.List.NonEmpty as NE

open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Lists

open import BitML.BasicTypes
open import BitML.Predicate

module BitML.Contracts.Types
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

Hon = NE.toList Honest

variable
  A B A′ B′ : Participant

------------------------------------------------------------------------
-- Contracts

data Contract : Set
Contracts = List Contract
VContracts = List (Value × Contracts)

data Contract where

  -- collect deposits and secrets
  put_&reveal_if_⇒_ : Ids → Secrets → Predicate → Contracts → Contract

  -- transfer the balance to a participant
  withdraw : Participant → Contract

  -- split the balance
  split : VContracts → Contract

  -- wait for participant's authorization
  _⇒_ : Participant → Contract → Contract

  -- wait of a period of time
  after_⇒_ : Time → Contract → Contract

{-# TERMINATING #-}
unquoteDecl DecEq-Contract = DERIVE DecEq [ quote Contract , DecEq-Contract ]

variable
  d d′ d″ : Contract
  ds ds′ ds″ c c′ c″ : Contracts
  vcs vcs′ vcs″ : VContracts

_⊕_ : ∀ {A : Set} → A → List A → List A
_⊕_ = _∷_

_∙ : ∀ {A : Set} → A → List A
_∙ = [_]

_⊸_ : Value → Contracts → Value × Contracts
_⊸_ = _,_

pattern put_&reveal_⇒_ xs as c = put xs &reveal as if `true ⇒ c
pattern put_⇒_ xs c            = put xs &reveal [] ⇒ c
pattern reveal_⇒_ as c         = put [] &reveal as ⇒ c

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

unquoteDecl DecEq-Precondition = DERIVE DecEq [ quote Precondition , DecEq-Precondition ]

variable
  g g′ g″ : Precondition

------------------------------------------------------------------------
-- Advertisements.

record Advertisement : Set where
  constructor ⟨_⟩_
  field
    G : Precondition
    C : Contracts
open Advertisement public
unquoteDecl DecEq-Advertisement = DERIVE DecEq [ quote Advertisement , DecEq-Advertisement ]

variable
  ad ad′ ad″ : Advertisement

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

data DepositType : Set where
  volatile persistent : DepositType

DepositRef  = Participant × Value × Id
TDepositRef = DepositType × DepositRef
