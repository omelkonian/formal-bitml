------------------------------------------------------------------------
-- Utilities for constructing configurations.
------------------------------------------------------------------------
open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Set'
open import Prelude.Collections
open import Prelude.Applicative
open import Prelude.Semigroup
open import Prelude.Nary

open import BitML.BasicTypes

module BitML.Semantics.Configurations.Helpers
  (Participant : Set)
  {{_ : DecEq Participant}}
  (Honest : List⁺ Participant)
  where

open import BitML.Contracts.Types Participant Honest
open import BitML.Contracts.Helpers Participant Honest
open import BitML.Semantics.Action Participant Honest
open import BitML.Semantics.Configurations.Types Participant Honest

-------------------------------------------------------------------

-- Re-ordering configurations
cfgToList : Configuration → List Configuration
cfgToList ∅ᶜ       = []
cfgToList (l ∣ r) = cfgToList l ++ cfgToList r
cfgToList c        = [ c ]

infix 3 _≈_
_≈_ : Configuration → Configuration → Set
c ≈ c′ = cfgToList c ↭ cfgToList c′

infix 3 _≈?_
_≈?_ : Decidable² {A = Configuration} _≈_
c ≈? c′ = cfgToList c ↭? cfgToList c′

instance
  HNᵃᶜ : Action has Name
  HNᵃᶜ .collect ac with ac
  ... | ♯▷ ad            = collect ad
  ... | x ▷ˢ ad          = inj₁ x ∷ collect ad
  ... | x ▷ c            = inj₁ x ∷ collect c
  ... | x ↔ y ▷⟨ _ , _ ⟩ = map inj₁ ⟦ x , y ⟧
  ... | x ▷⟨ _ , _ , _ ⟩ = [ inj₁ x ]
  ... | x ▷ᵈ _           = [ inj₁ x ]
  ... | xs , _ ▷ᵈˢ x     = map inj₁ (x ∷ xs)

  HDᶜᶠ : Configuration has DepositRef
  HDᶜᶠ .collect cf with cf
  ... | ⟨ A has v ⟩at x = [ A , v , x ]
  ... | l ∣ r           = collect l ++ collect r
  ... | _               = []

  HNᶜᶠ : Configuration has Name
  HNᶜᶠ .collect c with c
  ... | ∅ᶜ              = []
  ... | ` ad            = collect ad
  ... | ⟨ cs , _ ⟩at x  = inj₂ x ∷ collect cs
  ... | ⟨ _ has _ ⟩at x = [ inj₂ x ]
  ... | _ auth[ ac ]    = collect ac
  ... | ⟨ _ ∶ s ♯ _ ⟩   = [ inj₁ s ]
  ... | _ ∶ s ♯ _       = [ inj₁ s ]
  ... | l ∣ r           = collect l ++ collect r

  HNᵗᶜᶠ : TimedConfiguration has Name
  HNᵗᶜᶠ .collect (Γ at _) = collect Γ

secretsOfᶜᶠ : Participant → Configuration → Secrets
secretsOfᶜᶠ A = {- Set'.nub ∘-} go
  where
    go : Configuration → Secrets
    go (⟨ B ∶ a ♯ _ ⟩) = if A == B then [ a ] else []
    go (l ∣ r)         = go l ++ go r
    go _               = []

committedParticipants : Configuration → Advertisement → List Participant
committedParticipants (p auth[ (♯▷ ad′) ]) ad = if ad == ad′ then [ p ] else []
committedParticipants (l ∣ r) ad = committedParticipants l ad ++ committedParticipants r ad
committedParticipants _       _  = []

isInitial : Configuration → Bool
isInitial (⟨ _ has _ ⟩at _) = true
isInitial (l ∣ r)           = isInitial l ∧ isInitial r
isInitial _                 = false

Initial : Configuration → Set
Initial = T ∘ isInitial
