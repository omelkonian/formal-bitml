------------------------------------------------------------------------
-- Utilities for contracts, preconditions and advertisments.
------------------------------------------------------------------------

open import Function using (_∘_)

open import Data.Product using (_×_; _,_; Σ-syntax; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Nat     using (_>_)
open import Data.List    using (List; []; _∷_; [_]; length; _++_; map; partitionSums)

open import Relation.Nullary                      using (yes; no)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Prelude.Lists

open import BitML.BasicTypes
open import BitML.Predicate.Base

module BitML.Contracts.Helpers
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))
  where

open import BitML.Contracts.Types             Participant _≟ₚ_ Honest
open import BitML.Contracts.DecidableEquality Participant _≟ₚ_ Honest

-- T0D0 use Set'.nub on all results

namesᵖ : Precondition → Ids
namesᵖ = SETₛ.nub ∘ go
  where
    go : Precondition → Ids
    go (_ :? _ at x) = [ x ]
    go (_ :! _ at x) = [ x ]
    go (_ :secret _) = []
    go (p₁ ∣∣ p₂)     = namesᵖ p₁ ++ namesᵖ p₂

namesᶜ   : Contract                 → Ids
namesᶜˢ  : Contracts                → Ids
namesᵛᶜˢ : List (Value × Contracts) → Ids

namesᶜˢ []       = []
namesᶜˢ (c ∷ cs) = namesᶜ c ++ namesᶜˢ cs

namesᵛᶜˢ []               = []
namesᵛᶜˢ ((_ , cs) ∷ vcs) = namesᶜˢ cs ++ namesᵛᶜˢ vcs

namesᶜ (put xs &reveal _ if _ ⇒ cs) = xs ++ namesᶜˢ cs
namesᶜ (withdraw _)                 = []
namesᶜ (split vcs)                  = namesᵛᶜˢ vcs
namesᶜ (_ ⇒ c)                      = namesᶜ c
namesᶜ (after _ ⇒ c)                = namesᶜ c

participantsᶜ   : Contract                 → List Participant
participantsᶜˢ  : Contracts                → List Participant
participantsᵛᶜˢ : List (Value × Contracts) → List Participant

participantsᶜˢ []       = []
participantsᶜˢ (c ∷ cs) = participantsᶜ c ++ participantsᶜˢ cs

participantsᵛᶜˢ []               = []
participantsᵛᶜˢ ((_ , cs) ∷ vcs) = participantsᶜˢ cs ++ participantsᵛᶜˢ vcs

participantsᶜ (put _ &reveal _ if _ ⇒ cs) = participantsᶜˢ cs
participantsᶜ (withdraw p)                = [ p ]
participantsᶜ (split vcs)                 = participantsᵛᶜˢ vcs
participantsᶜ (p ⇒ c)                     = p ∷ participantsᶜ c
participantsᶜ (after _ ⇒ c)               = participantsᶜ c

participantsᵖ : Precondition → List Participant
participantsᵖ = SETₚ.nub ∘ go
  where
    go : Precondition → List Participant
    go (p :? _ at _) = [ p ]
    go (p :! _ at _) = [ p ]
    go (p :secret _) = [ p ]
    go (p₁ ∣∣ p₂)    = participantsᵖ p₁ ++ participantsᵖ p₂

putComponentsᶜ   : Contract                 → List (Ids × Secrets × Predicate)
putComponentsᶜˢ  : Contracts                → List (Ids × Secrets × Predicate)
putComponentsᵛᶜˢ : List (Value × Contracts) → List (Ids × Secrets × Predicate)

putComponentsᶜˢ []       = []
putComponentsᶜˢ (c ∷ cs) = putComponentsᶜ c ++ putComponentsᶜˢ cs

putComponentsᵛᶜˢ []               = []
putComponentsᵛᶜˢ ((_ , cs) ∷ vcs) = putComponentsᶜˢ cs ++ putComponentsᵛᶜˢ vcs

putComponentsᶜ (put xs &reveal as if p ⇒ cs) = (xs , as , p) ∷ putComponentsᶜˢ cs
putComponentsᶜ (withdraw _)                  = []
putComponentsᶜ (split vcs)                   = putComponentsᵛᶜˢ vcs
putComponentsᶜ (_ ⇒ c)                       = putComponentsᶜ c
putComponentsᶜ (after _ ⇒ c)                 = putComponentsᶜ c

depositsᵖ : Precondition → List DepositRef
depositsᵖ = SETₑ.nub ∘ go
  where
    go : Precondition → List DepositRef
    go (a :! v at x) = [ a , v , x ]
    go (a :? v at x) = [ a , v , x ]
    go (_ :secret _) = []
    go (p₁ ∣∣ p₂)    = depositsᵖ p₁ ++ depositsᵖ p₂

persistentDepositsᵖ : Precondition → List DepositRef
persistentDepositsᵖ = SETₑ.nub ∘ go
  where
    go : Precondition → List DepositRef
    go (a :! v at x) = [ a , v , x ]
    go (p₁ ∣∣ p₂)    = persistentDepositsᵖ p₁ ++ persistentDepositsᵖ p₂
    go _             = []

persistentParticipantsᵖ : Precondition → List Participant
persistentParticipantsᵖ = SETₚ.nub ∘ go
  where
    go : Precondition → List Participant
    go (A :! _ at _) = [ A ]
    go (p ∣∣ p₁)     = persistentParticipantsᵖ p ++ persistentParticipantsᵖ p₁
    go _             = []

secretsᵖ : Participant → Precondition → Secrets
secretsᵖ A = SETₛ.nub ∘ go
  where
    go : Precondition → Secrets
    go (B :secret s) with A ≟ₚ B
    ... | yes _ = [ s ]
    ... | no  _ = []
    go (l ∣∣ r )     = secretsᵖ A l ++ secretsᵖ A r
    go _             = []

depositsᵃ : Advertisement → List DepositRef
depositsᵃ = depositsᵖ ∘ G

decorations⊎ : Contract → List (Participant ⊎ Time)
decorations⊎ (A       ⇒ d) = inj₁ A ∷ decorations⊎ d
decorations⊎ (after t ⇒ d) = inj₂ t ∷ decorations⊎ d
decorations⊎ _             = []

decorations : Contract → List Participant × List Time
decorations c with partitionSums (decorations⊎ c)
... | (ps , ts) = SETₚ.nub ps , SETₙ.nub ts

authDecorations : Contract → List Participant
authDecorations = proj₁ ∘ decorations

timeDecorations : Contract → List Time
timeDecorations = proj₂ ∘ decorations

removeTopDecorations : Contract → Contract
removeTopDecorations (_       ⇒ d) = removeTopDecorations d
removeTopDecorations (after _ ⇒ d) = removeTopDecorations d
removeTopDecorations d             = d
