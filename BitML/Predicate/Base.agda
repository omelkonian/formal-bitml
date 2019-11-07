------------------------------------------------------------------------
-- Datatype for predicates used in contracts.
------------------------------------------------------------------------

open import Data.Nat           using (ℕ)
open import Data.Integer       using (ℤ; +_)
open import Data.Fin           using (Fin; 0F; 1F)
open import Data.Product       using (∃-syntax)

open import Relation.Nullary                      using (Dec; yes; no)
open import Relation.Nullary.Decidable            using (True; fromWitness; toWitness)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module BitML.Predicate.Base where

data ExpressionContext : Set where
  Ctx : ℕ → ExpressionContext

ctxToℕ : ExpressionContext → ℕ
ctxToℕ (Ctx n) = n

data ExpressionType : Set where
  `Bool `ℤ : ExpressionType

variable
  ctx ctx′ : ExpressionContext
  ty ty′ : ExpressionType

data Expression : ExpressionContext -- size of the environment/context
                → ExpressionType    -- result type
                → Set where

  -- Calculate the length of a secret, which is a variable in the context
  ∣_∣ : ∀ {n} → Fin n → Expression (Ctx n) `ℤ

  -- Arithmetic/boolean operations
  `     : ℤ → Expression ctx `ℤ
  _`+_  : Expression ctx `ℤ → Expression ctx `ℤ → Expression ctx `ℤ
  _`-_  : Expression ctx `ℤ → Expression ctx `ℤ → Expression ctx `ℤ
  _`=_  : Expression ctx `ℤ → Expression ctx `ℤ → Expression ctx `Bool
  _`<_  : Expression ctx `ℤ → Expression ctx `ℤ → Expression ctx `Bool

  `true : Expression ctx `Bool
  _`∧_  : Expression ctx `Bool → Expression ctx `Bool → Expression ctx `Bool
  `¬_   : Expression ctx `Bool → Expression ctx `Bool

∃Expression = ∃[ ctx ] ∃[ ty ] Expression ctx ty

Predicate : ExpressionContext → Set
Predicate ctx = Expression ctx `Bool

∃Predicate = ∃[ ctx ] Predicate ctx

-- operators' precedence
infix  4 ∣_∣
infixr 3 _`+_
infixr 3 _`-_
infix  2 _`=_
infix  2 _`<_
infixr 1 _`∧_

_ : Predicate (Ctx 2)
_ = ∣ 0F ∣ `= ∣ 1F ∣
 `∧ ` (+ 5) `= (` (+ 3) `+ ` (+ 2))
