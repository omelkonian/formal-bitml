------------------------------------------------------------------------
-- Datatype for predicates used in contracts.
------------------------------------------------------------------------

open import Data.Nat     using (ℕ)
open import Data.Integer using (ℤ; +_)
open import Data.Fin     using (Fin)
open import Data.Product using (∃-syntax; _,_)
open import Data.List    using ([]; [_]; _++_)

open import BitML.BasicTypes

open import Prelude.DecEq

module BitML.Predicate where

data Arith : Set where
  `    : ℤ → Arith
  ∣_∣  : Secret → Arith
  _`+_ : Arith → Arith → Arith
  _`-_ : Arith → Arith → Arith
unquoteDecl DecEqᵃʳ = DERIVE DecEq [ quote Arith , DecEqᵃʳ ]

data Predicate : Set where
  `true : Predicate
  _`∧_  : Predicate → Predicate → Predicate
  `¬_   : Predicate → Predicate
  _`=_  : Arith → Arith → Predicate
  _`<_  : Arith → Arith → Predicate
unquoteDecl DecEqᵖʳ = DERIVE DecEq [ quote Predicate , DecEqᵖʳ ]

variable
  p p′ : Predicate

infix  4 ∣_∣
infixr 3 _`+_
infixr 3 _`-_
infix  2 _`=_
infix  2 _`<_
infixr 1 _`∧_

private
  _ : Predicate
  _ = ∣ "change_me" ∣ `= ∣ "change_me" ∣
   `∧ ` (+ 5) `= (` (+ 3) `+ ` (+ 2))
