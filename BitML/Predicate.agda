------------------------------------------------------------------------
-- Datatype for predicates used in contracts.
------------------------------------------------------------------------
module BitML.Predicate where

open import Prelude.Init; open SetAsType
open import Prelude.DecEq

open import BitML.BasicTypes

data Arith : Type where
  `         : ℤ → Arith
  ∣_∣       : Secret → Arith
  _`+_ _`-_ : Arith → Arith → Arith
unquoteDecl DecEqᵃʳ = DERIVE DecEq [ quote Arith , DecEqᵃʳ ]

data Predicate : Type where
  `true     : Predicate
  `¬_       : Predicate → Predicate
  _`∧_      : Predicate → Predicate → Predicate
  _`=_ _`<_ : Arith → Arith → Predicate
unquoteDecl DecEqᵖʳ = DERIVE DecEq [ quote Predicate , DecEqᵖʳ ]

variable p p′ : Predicate

infix  4 ∣_∣
infixr 3 _`+_ _`-_
infix  2 _`=_ _`<_ _`≠_ _`≤_ _`≮_ _`≰_ _`>_ _`≥_ _`≯_ _`≱_
infixr 1 _`∧_ _`∨_

_`∨_ : Op₂ Predicate
p `∨ q = `¬ (`¬ p `∧ `¬ q)

_`≠_ _`≤_ _`≮_ _`≰_ _`>_ _`≥_ _`≯_ _`≱_ : Arith → Arith → Predicate
x `≠ y = `¬ (x `= y)
x `≤ y = (x `= y) `∨ (x `< y)
x `≮ y = `¬ (x `< y)
x `≰ y = `¬ (x `≤ y)
_`>_ = flip _`<_; _`≥_ = flip _`≤_; _`≯_ = flip _`≮_; _`≱_ = flip _`≰_

_`≤_`≤_ _`≥_`≥_ : Arith → Arith → Arith → Predicate
x `≤ y `≤ z = (x `≤ y) `∧ (y `≤ z)
x `≥ y `≥ z = (x `≥ y) `∧ (y `≥ z)

_ : Predicate
_ = ∣ "change_me" ∣ `= ∣ "change_me" ∣
  `∧ ` 5ℤ `= ` 3ℤ `+ ` 2ℤ
