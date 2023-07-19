------------------------------------------------------------------------
-- BitML datatypes: Contracts & Ads
------------------------------------------------------------------------
open import Prelude.Init; open SetAsType
open import Prelude.DecEq

open import BitML.BasicTypes
open import BitML.Predicate

module BitML.Contracts.Types ⋯ (let open ⋯ ⋯) where

variable A B A′ B′ : Participant

------------------------------------------------------------------------
-- Contracts

data Branch : Type
Contract    = List Branch
Contracts   = List Contract
VContracts  = List (Value × Contract)
VIContracts = List (Value × Contract × Id)

data Branch where

  -- collect deposits and secrets
  put_&reveal_if_⇒_ : Ids → Secrets → Predicate → Contract → Branch

  -- transfer the balance to a participant
  withdraw : Participant → Branch

  -- split the balance
  -- T0D0: phrase as percentages to mitigate the need for `Validity.splitsOK`
  split : VContracts → Branch

  -- wait for participant's authorization
  _⇒_ : Participant → Branch → Branch

  -- wait of a period of time
  after_⇒_ : Time → Branch → Branch

{-# TERMINATING #-}
unquoteDecl DecEq-Branch = DERIVE DecEq [ quote Branch , DecEq-Branch ]

variable
  d d′ d″ : Branch
  ds ds′ ds″ c c′ c″ : Contract
  cs cs′ cs″ : Contracts
  vcs vcs′ vcs″ : VContracts

_⊕_ = (∀ {A : Type} → A → List A → List A) ∋ _∷_
_∙  = (∀ {A : Type} → A → List A)          ∋ [_]
_⊸_ = (∀ {A B : Type} → A → B → A × B)     ∋ _,_

pattern put_&reveal_⇒_ xs as c = put xs &reveal as if `true ⇒ c
pattern put_⇒_ xs c            = put xs &reveal []          ⇒ c
pattern put_if_⇒_ xs p c       = put xs &reveal [] if p     ⇒ c
pattern reveal_if_⇒_ as p c    = put [] &reveal as if p     ⇒ c
pattern reveal_⇒_ as c         = put [] &reveal as          ⇒ c

-------------------------------------------------------------------
-- Contract preconditions.

data Precondition : Type where

  -- volatile deposit
  _:?_at_ : Participant → Value → Id → Precondition

  -- persistent deposit
  _:!_at_ : Participant → Value → Id → Precondition

  -- committed secret (random nonce) by <Participant>
  _:secret_ : Participant → Secret → Precondition

  -- composition
  _∣∣_ : Precondition → Precondition → Precondition

unquoteDecl DecEq-Precondition =
  DERIVE DecEq [ quote Precondition , DecEq-Precondition ]

variable g g′ g″ : Precondition

------------------------------------------------------------------------
-- Advertisements.

record Ad : Type where
  constructor ⟨_⟩_
  field
    G : Precondition
    C : Contract
open Ad public
unquoteDecl DecEq-Ad =
  DERIVE DecEq [ quote Ad , DecEq-Ad ]

variable ad ad′ ad″ : Ad

infix  2 ⟨_⟩_
infix  5 _:?_at_ _:!_at_ _:secret_
infixl 2 _∣∣_

infixr 9 _⇒_
infix  8 put_&reveal_if_⇒_ put_&reveal_⇒_ put_⇒_ reveal_⇒_
infix  7 _⊸_
infix  6 _∙
infixr 5 _⊕_

data DepositType : Type where
  volatile persistent : DepositType

DepositRef   = Participant × Value × Id
DepositRefs  = List DepositRef
TDepositRef  = DepositType × DepositRef
TDepositRefs = List TDepositRef

-- Examples.

open import Prelude.General; open MultiTest
module _ (A B : Participant) where
  _ = Contract
   ∋⋮ (withdraw A ∙)
    ⋮ (A ⇒ withdraw A)
    ⊕ (put [] ⇒ (withdraw A ∙))
    ∙
    ⋮ (put [ "x" ] ⇒ (withdraw A ∙))
    ∙
    ⋮ A ⇒ withdraw B
    ⊕ B ⇒ split ( 2 ⊸ (withdraw A ∙)
                ⊕ 3 ⊸ (after 100 ⇒ withdraw B ∙)
                ⊕ 0 ⊸ (put [ "y" ] ⇒ (A ⇒ withdraw B ∙) ∙)
                ∙)
    ∙
    ⋮∅

  _ = Ad
   ∋⋮ ⟨ B :! 2 at "x" ∣∣ A :! 3 at "y" ∣∣ B :? 100 at "z" ⟩
      put [ "z" ] ⇒ (withdraw A ∙) ∙
    ⋮∅
