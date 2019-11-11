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

secretsᵃʳ : Arith → Secrets
secretsᵃʳ = {-SETₛ.nub ∘-} go
  where
    go : Arith → Secrets
    go (` _)    = []
    go ∣ a ∣    = [ a ]
    go (x `+ y) = go x ++ go y
    go (x `- y) = go x ++ go y

secretsᵖʳ : Predicate → Secrets
secretsᵖʳ = {-SETₛ.nub ∘-} go
  where
    go : Predicate → Secrets
    go `true = []
    go (x `∧ y) = go x ++ go y
    go (`¬ x)   = go x
    go (x `= y) = secretsᵃʳ x ++ secretsᵃʳ y
    go (x `< y) = secretsᵃʳ x ++ secretsᵃʳ y
