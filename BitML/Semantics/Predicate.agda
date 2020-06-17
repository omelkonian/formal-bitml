------------------------------------------------------------------------
-- Denotational semantics of predicates.
------------------------------------------------------------------------

open import Function using (const)

open import Data.Product using (Σ-syntax)
open import Data.Bool    using (Bool; true; _∧_; not; if_then_else_)
open import Data.Maybe   using (Maybe; just; nothing; ap; _<∣>_)
open import Data.Nat     using (_>_)
open import Data.Integer using (ℤ; +_; _+_; _-_; _<?_)

open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Prelude.Lists hiding (⟦_⟧)
open import Prelude.DecEq

open import BitML.BasicTypes
open import BitML.Predicate

module BitML.Semantics.Predicate
  (Participant : Set)
  {{_ : DecEq Participant}}
  (Honest : List⁺ Participant)
  where

open import BitML.Semantics.Configurations.Types Participant Honest hiding (`_)

-- To allow idiom brackets
pure : ∀ {A : Set} → A → Maybe A
pure  = just
_<*>_ = ap

infix 4 _<?ᵇ_
_<?ᵇ_ : ℤ → ℤ → Bool
x <?ᵇ y = ⌊ x <? y ⌋

lookupSecretLen : Secret → Configuration → Maybe ℤ
lookupSecretLen a (_ ∶ a′ ♯ N) = if a == a′ then ⦇ (+ N) ⦈ else nothing
lookupSecretLen a (l ∣ r)      = lookupSecretLen a l <∣> lookupSecretLen a r
lookupSecretLen _ _            = nothing

⟦_⟧ᵃʳ_ : Arith → Configuration → Maybe ℤ
⟦ ∣ a ∣   ⟧ᵃʳ Γ = lookupSecretLen a Γ
⟦ ` x     ⟧ᵃʳ _ = ⦇ x ⦈
⟦ e `+ e′ ⟧ᵃʳ Γ = ⦇ ⟦ e ⟧ᵃʳ Γ + ⟦ e′ ⟧ᵃʳ Γ ⦈
⟦ e `- e′ ⟧ᵃʳ Γ = ⦇ ⟦ e ⟧ᵃʳ Γ - ⟦ e′ ⟧ᵃʳ Γ ⦈


⟦_⟧_ : Predicate → Configuration → Maybe Bool
⟦ `true   ⟧ Γ = ⦇ true ⦈
⟦ e `∧ e′ ⟧ Γ = ⦇ ⟦ e ⟧ Γ ∧ ⟦ e′ ⟧ Γ ⦈
⟦ `¬ e    ⟧ Γ = ⦇ not (⟦ e ⟧ Γ) ⦈
⟦ e `= e′ ⟧ Γ = ⦇ ⟦ e ⟧ᵃʳ Γ == ⟦ e′ ⟧ᵃʳ Γ ⦈
⟦ e `< e′ ⟧ Γ = ⦇ ⟦ e ⟧ᵃʳ Γ <?ᵇ ⟦ e′ ⟧ᵃʳ Γ ⦈
