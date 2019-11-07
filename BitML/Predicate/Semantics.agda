------------------------------------------------------------------------
-- Denotational semantics of predicates.
------------------------------------------------------------------------
module BitML.Predicate.Semantics where

open import Data.String  using (length)
open import Data.Bool    using (Bool; true; _∧_; not)
open import Data.Vec     using (Vec; lookup)
open import Data.Integer using (ℤ; +_; _+_; _-_; _<?_)
  renaming (_≟_ to _≟ℤ_)

open import Relation.Nullary.Decidable using (⌊_⌋)

open import BitML.Predicate.Base
open import BitML.BasicTypes

Environment : ExpressionContext → Set
Environment ctx = Vec Secret (ctxToℕ ctx)

⟦_⟧ₜ : ExpressionType → Set
⟦_⟧ₜ `Bool = Bool
⟦_⟧ₜ `ℤ    = ℤ

infix 8 ⟦_⟧_
⟦_⟧_ : Expression ctx ty → Environment ctx → ⟦ ty ⟧ₜ
⟦ ∣ x ∣   ⟧ ρ = + (length (lookup ρ x))
⟦ ` x     ⟧ ρ = x
⟦ e `+ e′ ⟧ ρ = ⟦ e ⟧ ρ + ⟦ e′ ⟧ ρ
⟦ e `- e′ ⟧ ρ = ⟦ e ⟧ ρ - ⟦ e′ ⟧ ρ
⟦ e `= e′ ⟧ ρ = ⌊ ⟦ e ⟧ ρ ≟ℤ ⟦ e′ ⟧ ρ ⌋
⟦ e `< e′ ⟧ ρ = ⌊ ⟦ e ⟧ ρ <? ⟦ e′ ⟧ ρ ⌋
⟦ `true   ⟧ ρ = true
⟦ e `∧ e′ ⟧ ρ = ⟦ e ⟧ ρ ∧ ⟦ e′ ⟧ ρ
⟦ `¬ e    ⟧ ρ = not (⟦ e ⟧ ρ)
