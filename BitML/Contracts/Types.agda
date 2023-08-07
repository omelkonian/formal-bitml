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
  _∶_ : Participant → Branch → Branch

  -- wait of a period of time
  after_∶_ : Time → Branch → Branch

{-# TERMINATING #-}
unquoteDecl DecEq-Branch = DERIVE DecEq [ quote Branch , DecEq-Branch ]

variable
  d d′ d″ : Branch
  ds ds′ ds″ c c′ c″ : Contract
  cs cs′ cs″ : Contracts
  vcs vcs′ vcs″ : VContracts

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
  _∣_ : Op₂ Precondition

unquoteDecl DecEq-PreC = DERIVE DecEq [ quote Precondition , DecEq-PreC ]

variable g g′ g″ : Precondition

------------------------------------------------------------------------
-- Advertisements.

record Ad : Type where
  constructor ⟨_⟩_
  field
    G : Precondition
    C : Contract
open Ad public
unquoteDecl DecEq-Ad = DERIVE DecEq [ quote Ad , DecEq-Ad ]

variable ad ad′ ad″ : Ad

------------------------------------------------------------------------
-- Auxiliary types.

data DepositType : Type where
  volatile persistent : DepositType

DepositRef   = Participant × Value × Id
DepositRefs  = List DepositRef
TDepositRef  = DepositType × DepositRef
TDepositRefs = List TDepositRef

PutComponent = Ids × Secrets × Predicate

-- Notation.

private variable X Y Z : Type

import Prelude.Lists.NoNil as NN
open NN using (List?; toL) public
instance
  ⊕-notation-𝕃 = NN.Pick𝕃
  ⊕-notation-ℝ = NN.Pickℝ
_⊕_ = NN._⊕_ {X = Branch}
_⊗_ = Op₂ VContracts ∋ _++_

_⊸_ : Value → X → ⦃ List? Branch X ⦄ → VContracts
v ⊸ c = [ v , toL c ]

open import Prelude.General; open MultiTest
module _ (b b′ : Branch) (c c′ : Contract) where
  _ = Contract
   ∋⋮ b ⊕ b′
    ⋮ b ⊕ c
    ⋮ c ⊕ b
    ⋮ c ⊕ c′
    ⋮∅

module _ ⦃ _ : List? Id X ⦄ ⦃ _ : List? Secret Y ⦄ ⦃ _ : List? Branch Z ⦄ where
  put_&reveal_if_．_ : X → Y → Predicate → Z → Branch
  put xs &reveal as if p ． bs = put toL xs &reveal toL as if p ⇒ toL bs

  put_&reveal_．_ : X → Y → Z → Branch
  put xs &reveal as ． bs = put toL xs &reveal toL as ⇒ toL bs

  infix 8 put_&reveal_if_．_ put_&reveal_．_

module _ ⦃ _ : List? String X ⦄ ⦃ _ : List? Branch Y ⦄ where
  put_．_ reveal_．_ : X → Y → Branch
  put    xs ． bs = put    toL xs ⇒ toL bs
  reveal as ． bs = reveal toL as ⇒ toL bs

  put_if_．_ reveal_if_．_ : X → Predicate → Y → Branch
  put    xs if p ． bs = put    toL xs if p ⇒ toL bs
  reveal as if p ． bs = reveal toL as if p ⇒ toL bs

  infix 8 put_．_ put_if_．_ reveal_．_ reveal_if_．_

infix  7 _:?_at_ _:!_at_ _:secret_
infixl 6 _∣_
infix  0 ⟨_⟩_

infixr 9 _∶_ after_∶_
infix  8 put_&reveal_if_⇒_ put_&reveal_⇒_ put_⇒_ put_if_⇒_ reveal_⇒_ reveal_if_⇒_
infixr 5 _⊕_
infix  4 _⊸_
infixr 3 _⊗_

-- Examples.

module _ (A B : Participant) where
  _ = Contract
   ∋⋮ [ withdraw A ]
    ⋮ A ∶ withdraw A
    ⊕ put [] ． withdraw A
    ⋮ [ put "x" ． withdraw A ]
    ⋮ A ∶ withdraw B
    ⊕ B ∶ split ( 2 ⊸ withdraw A
                ⊗ 3 ⊸ after 100 ∶ withdraw B
                    ⊕ after 200 ∶ withdraw A
                ⊗ 0 ⊸ put "y" ． (A ∶ withdraw B))
    ⋮∅

  _ = Ad
   ∋⋮ ⟨ B :! 2 at "x" ∣ A :! 3 at "y" ∣ B :? 100 at "z" ⟩
      [ put "z" ． withdraw A ]
    ⋮∅
