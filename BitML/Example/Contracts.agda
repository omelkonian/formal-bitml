------------------------------------------------------------------------
-- BitML contract examples (from §2 and §A.1 of BitML paper)
------------------------------------------------------------------------
module BitML.Example.Contracts where

open import Prelude.Init; open SetAsType
open import Prelude.Semigroup
open import Prelude.Ord
open import Prelude.Membership
open import Prelude.Validity
open import Prelude.Decidable
open import Prelude.DecEq
open import Prelude.Lists
open import Prelude.Lists.Dec
open import Prelude.Lists.NoNil using ()

open import BitML.BasicTypes
  hiding (a; t; t′; v)
open import BitML.Predicate

open import BitML.Example.Setup

open import BitML.Contracts ⋯ Participant , Honest ⋯
  hiding (A; B; C)

---------------------------------------------------------
-- constants (to unblock computation on closed formulas)
a = "a"; b = "b"
t = 10; t′ = 20
---------------------------------------------------------

----------------------
-- ** contracts

-- §2

PayOrRefund : Contract
PayOrRefund = A ∶ withdraw B
            ⊕ B ∶ withdraw A

Resolve : Value → Value → Branch
Resolve v v′ =
  split $ v  ⊸ withdraw M
        ⊗ v′ ⊸ M ∶ withdraw A
             ⊕ M ∶ withdraw B

Escrow : Contract
Escrow = PayOrRefund
       ⊕ A ∶ Resolve 1 9
       ⊕ B ∶ Resolve 1 9

TC : Contract
TC = reveal a ． withdraw A
   ⊕ after t ∶ withdraw B

EscrowPut : Contract
EscrowPut = PayOrRefund
          ⊕ after t ∶ withdraw B
          ⊕ put "x" ．
              put "y" ．
                  Resolve 2 10
                ⊕ after t′ ∶ withdraw A

-- §A.1
postulate instance _ : Ord Float
postulate _∗_ : Float → ℕ → ℕ

1-_ : Float → Float
1- f = 1.0 Float.- f

IsPercentage : Pred₀ Float
IsPercentage f = (0.0 ≤ f) × (f ≤ 1.0)

module _ (v : Value) (Z : List Float) {_ : All IsPercentage Z} where

  VariableResolve : Float → Branch
  VariableResolve ζ =
    split $ ζ ∗ v      ⊸ withdraw A
          ⊗ (1- ζ) ∗ v ⊸ withdraw B

  VariableEscrow : Contract
  VariableEscrow
    = PayOrRefund
    ⊕ map (λ ζ → M ∶ VariableResolve ζ) Z

----------------------
-- ** advertisements

-- §2

PayOrRefundAd : Ad
PayOrRefundAd =
  ⟨ A :! 1 at "𝔸" ∣ B :! 0 at "𝔹" ⟩
  PayOrRefund

_ = Valid PayOrRefundAd ∋ auto

OddsEvens : Ad
OddsEvens =
  ⟨ A :! 3 at "x" ∣ B :! 3 at "y"
  ∣ A :secret a   ∣ B :secret b
  ⟩
  [ split $ 2 ⊸ reveal b if ｀ 0ℤ `≤ ∥ b ∥ `≤ ｀ 1ℤ ． withdraw B
              ⊕ after t ∶ withdraw A
          ⊗ 2 ⊸ reveal a ． withdraw A
              ⊕ after t ∶ withdraw B
          ⊗ 2 ⊸ reveal [ a ⨾ b ] if ∥ a ∥ `= ∥ b ∥ ． withdraw A
              ⊕ reveal [ a ⨾ b ] if ∥ a ∥ `≠ ∥ b ∥ ． withdraw B ]

_ = Valid OddsEvens ∋ auto

EscrowPutAd : Ad
EscrowPutAd =
  ⟨ A :! 10 at "𝔸" ∣ B :! 0 at "𝔹" ∣ M :! 0 at "𝕄"
  ∣ A :? 1  at "x" ∣ B :? 1 at "y"
  ⟩
  EscrowPut

_ = Valid EscrowPutAd ∋ auto

-- §A.1

vᵇ = 2; vᶜ = 3

IntermediatedPayment : Ad
IntermediatedPayment =
  ⟨ A :! vᵇ + vᶜ at "x"
  ∣ C :! 0 at "y"
  ⟩
    split ( vᵇ ⊸ withdraw A
          ⊗ vᶜ ⊸ withdraw C)
  ⊕ after t ∶ withdraw A

_ = Valid IntermediatedPayment ∋ auto

v = 10

MutualTC : Ad
MutualTC =
  ⟨ A :! v at "x" ∣ A :secret a
  ∣ B :! v at "y" ∣ B :secret b
  ⟩
    reveal a ．
        reveal b ．
            split ( v ⊸ withdraw A
                  ⊗ v ⊸ withdraw B)
          ⊕ after t′ ∶ withdraw A
      ⊕ after t′ ∶ withdraw A
  ⊕ after t ∶ withdraw B

_ = Valid MutualTC ∋ auto

ZeroCollateralLottery : Ad
ZeroCollateralLottery =
  ⟨ A :! 1 at "x" ∣ A :secret a
  ∣ B :! 1 at "y" ∣ B :secret b
  ⟩
    reveal b if ｀ 0ℤ `≤ ∥ b ∥ `≤ ｀ 1ℤ ．
        reveal [ a ⨾ b ] if ∥ a ∥ `= ∥ b ∥ ． withdraw A
      ⊕ reveal [ a ⨾ b ] if ∥ a ∥ `≠ ∥ b ∥ ． withdraw B
      ⊕ after t′ ∶ withdraw B
  ⊕ after t ∶ withdraw A

_ = Valid ZeroCollateralLottery ∋ auto

RockPaperScissors : Ad
RockPaperScissors =
  ⟨ A :! 3 at "x" ∣ A :secret a
  ∣ B :! 3 at "y" ∣ B :secret b
  ⟩
  [ split $ 2 ⊸ reveal b if ｀ 0ℤ `≤ ∥ b ∥ `≤ ｀ 2ℤ ． withdraw B
              ⊕ after t ∶ withdraw A
          ⊗ 2 ⊸ reveal a if ｀ 0ℤ `≤ ∥ a ∥ `≤ ｀ 2ℤ ． withdraw A
              ⊕ after t ∶ withdraw B
          ⊗ 2 ⊸ reveal [ a ⨾ b ] if w ∥ a ∥ ∥ b ∥  ． withdraw A
              ⊕ reveal [ a ⨾ b ] if w ∥ b ∥ ∥ a ∥  ． withdraw B
              ⊕ reveal [ a ⨾ b ] if ∥ a ∥ `= ∥ b ∥ ． split ( 1 ⊸ withdraw A
                                                           ⊗ 1 ⊸ withdraw B) ]
  where
    w : Arith → Arith → Predicate
    w n m = (n `= ｀ 0ℤ `∧ m `= ｀ 2ℤ)
         `∨ (n `= ｀ 2ℤ `∧ m `= ｀ 1ℤ)
         `∨ (n `= ｀ 1ℤ `∧ m `= ｀ 0ℤ)

_ = Valid RockPaperScissors ∋ auto
