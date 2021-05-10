------------------------------------------------------------------------
-- Denotational semantics of predicates.
------------------------------------------------------------------------
open import Prelude.Init hiding (_+_; _<?_)
open Integer using (_+_; _-_; _<?_)
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Applicative
open import Prelude.Monad

open import BitML.BasicTypes
open import BitML.Predicate

module BitML.Semantics.Predicate
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import BitML.Semantics.Configurations.Types Participant Honest hiding (`_)

infix 4 _<?ᵇ_
_<?ᵇ_ : ℤ → ℤ → Bool
x <?ᵇ y = ⌊ x <? y ⌋

lookupSecretLen : Secret → Configuration → Maybe ℤ
lookupSecretLen a (_ ∶ a′ ♯ N) = if a == a′ then ⦇ (+ N) ⦈ else nothing
lookupSecretLen a (l ∣ r)      = lookupSecretLen a l <|> lookupSecretLen a r
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
