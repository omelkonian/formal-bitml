------------------------------------------------------------------------
-- Datatype for predicates used in contracts.
------------------------------------------------------------------------

open import Data.Nat           using (ℕ)
open import Data.Integer       using (ℤ; +_)
open import Data.Fin           using (Fin; 0F; 1F)
open import Data.Product       using (∃-syntax)
open import Data.List          using ([]; [_]; _++_)

open import BitML.BasicTypes

module BitML.Predicate.Base where

data Arith : Set where
  `    : ℤ → Arith
  ∣_∣  : Secret → Arith
  _`+_ : Arith → Arith → Arith
  _`-_ : Arith → Arith → Arith

data Predicate : Set where
  `true : Predicate
  _`∧_  : Predicate → Predicate → Predicate
  `¬_   : Predicate → Predicate
  _`=_  : Arith → Arith → Predicate
  _`<_  : Arith → Arith → Predicate

variable
  p p′ : Predicate

infix  4 ∣_∣
infixr 3 _`+_
infixr 3 _`-_
infix  2 _`=_
infix  2 _`<_
infixr 1 _`∧_

_ : Predicate
_ = ∣ "change_me" ∣ `= ∣ "change_me" ∣
 `∧ ` (+ 5) `= (` (+ 3) `+ ` (+ 2))

secretsᵖʳ : Predicate → Secrets
secretsᵃʳ : Arith → Secrets

secretsᵖʳ `true = []
secretsᵖʳ (x `∧ y) = secretsᵖʳ x ++ secretsᵖʳ y
secretsᵖʳ (`¬ x)   = secretsᵖʳ x
secretsᵖʳ (x `= y) = secretsᵃʳ x ++ secretsᵃʳ y
secretsᵖʳ (x `< y) = secretsᵃʳ x ++ secretsᵃʳ y

secretsᵃʳ (` _)    = []
secretsᵃʳ ∣ a ∣    = [ a ]
secretsᵃʳ (x `+ y) = secretsᵃʳ x ++ secretsᵃʳ y
secretsᵃʳ (x `- y) = secretsᵃʳ x ++ secretsᵃʳ y
