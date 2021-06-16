------------------------------------------------------------------------
-- Chain reasoning for BitML's small-step semantics.
------------------------------------------------------------------------
open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq

open import BitML.BasicTypes

module BitML.Semantics.Reasoning
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import BitML.Semantics.Configurations.Types Participant Honest
open import BitML.Semantics.Configurations.Helpers Participant Honest
open import BitML.Semantics.Label Participant Honest
open import BitML.Semantics.InferenceRules Participant Honest

-----------------------------------------------------------------------------------
-- Reflexive transitive closure for —→.

infix  -1 _—↠[_]_
infix  -2 begin_
infixr -1 _—→⟨_⟩_⊢_ _—→⟨_⟩_
infix  0 _∎

data _—↠[_]_ : Configuration → Labels → Configuration → Set where

  _∎ : ∀ (M : Configuration)

      --———————————————————————————————————
    → M —↠[ [] ] M

  _—→⟨_⟩_⊢_ : ∀ (L : Configuration) {L′ M M′ N}

    → L′ —→[ α ] M′
    → L ≈ L′ × M ≈ M′
    → M —↠[ αs ]  N
      --———————————————————————————————————
    → L —↠[ α ∷ αs ] N

begin_ : ∀ {M N}

  → M —↠[ αs ] N
    --———————————————————————————————————
  → M —↠[ αs ] N

begin_ M—↠N = M—↠N

_—→⟨_⟩_ : ∀ (L    : Configuration) {L′ M M′ N}
  → L′ —→[ α ] M′
  → M —↠[ αs ]  N
  → {True $ L ≈? L′}
  → {True $ M ≈? M′}
    --———————————————————————————————————
  → L —↠[ α ∷ αs ] N
(L —→⟨ L′—→M′ ⟩ M—↠N) {p₁} {p₂} = L —→⟨ L′—→M′ ⟩ toWitness p₁ , toWitness p₂ ⊢ M—↠N

-----------------------------------------------------------------------------------
-- Reflexive transitive closure for —→ₜ.

infix  -1 _—↠ₜ[_]_
infix  -2 beginₜ_
infixr -1 _—→ₜ⟨_⟩_
infix  0 _∎ₜ

data _—↠ₜ[_]_ : TimedConfiguration → Labels → TimedConfiguration → Set where

  _∎ₜ : ∀ (M : TimedConfiguration)

      --———————————————————————————————————
    → M —↠ₜ[ [] ] M

  _—→ₜ⟨_⟩_ : ∀ (L : TimedConfiguration)
               {M : TimedConfiguration}
               {N : TimedConfiguration}

    → L —→ₜ[ α ] M
    → M —↠ₜ[ αs ] N
      --———————————————————————————————————
    → L —↠ₜ[ α ∷ αs ] N

beginₜ_ : ∀ {M : TimedConfiguration} {N : TimedConfiguration}

  → M —↠ₜ[ αs ] N
    --———————————————————————————————————
  → M —↠ₜ[ αs ] N

beginₜ_ M—↠N = M—↠N
