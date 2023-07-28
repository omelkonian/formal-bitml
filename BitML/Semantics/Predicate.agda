------------------------------------------------------------------------
-- Denotational semantics of predicates.
------------------------------------------------------------------------
open import Prelude.Init hiding (_+_)
open Integer using (_+_; _-_)
open import Prelude.Ord
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Applicative
open import Prelude.Monad

open import BitML.BasicTypes
open import BitML.Predicate

module BitML.Semantics.Predicate (⋯ : ⋯) (let open ⋯ ⋯) where

open import BitML.Semantics.Configurations.Types ⋯

⟦_⟧ᵃʳ_ : Arith → Cfg → Maybe ℤ
⟦ ∥ a ∥   ⟧ᵃʳ Γ = go Γ
  where
    go : Cfg → Maybe ℤ
    go = λ where
      (_ ∶ a′ ♯ N) → if a == a′ then ⦇ (+ N) ⦈ else nothing
      (l ∣ r)      → go l <|> go r
      _            → nothing
⟦ ｀ x     ⟧ᵃʳ _ = ⦇ x ⦈
⟦ e `+ e′ ⟧ᵃʳ Γ = ⦇ ⟦ e ⟧ᵃʳ Γ + ⟦ e′ ⟧ᵃʳ Γ ⦈
⟦ e `- e′ ⟧ᵃʳ Γ = ⦇ ⟦ e ⟧ᵃʳ Γ - ⟦ e′ ⟧ᵃʳ Γ ⦈


⟦_⟧ᵖ_ : Predicate → Cfg → Maybe Bool
⟦ `true   ⟧ᵖ Γ = ⦇ true ⦈
⟦ e `∧ e′ ⟧ᵖ Γ = ⦇ ⟦ e ⟧ᵖ Γ ∧ ⟦ e′ ⟧ᵖ Γ ⦈
⟦ `¬ e    ⟧ᵖ Γ = ⦇ not (⟦ e ⟧ᵖ Γ) ⦈
⟦ e `= e′ ⟧ᵖ Γ = ⦇ ⟦ e ⟧ᵃʳ Γ ==  ⟦ e′ ⟧ᵃʳ Γ ⦈
⟦ e `< e′ ⟧ᵖ Γ = ⦇ ⟦ e ⟧ᵃʳ Γ <ᵇ  ⟦ e′ ⟧ᵃʳ Γ ⦈
