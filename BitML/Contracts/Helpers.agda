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

-- T0D0 use Set'.nub on all results? or only on use-sites

-- Names

namesᶜ   : Contract                 → Names
namesᶜˢ  : Contracts                → Names
namesᵛᶜˢ : List (Value × Contracts) → Names

namesᶜˢ []       = []
namesᶜˢ (c ∷ cs) = namesᶜ c ++ namesᶜˢ cs

namesᵛᶜˢ []               = []
namesᵛᶜˢ ((_ , cs) ∷ vcs) = namesᶜˢ cs ++ namesᵛᶜˢ vcs

namesᶜ (put xs &reveal as if _ ⇒ cs) = xs ++ as ++ namesᶜˢ cs
namesᶜ (withdraw _)                 = []
namesᶜ (split vcs)                  = namesᵛᶜˢ vcs
namesᶜ (_ ⇒ c)                      = namesᶜ c
namesᶜ (after _ ⇒ c)                = namesᶜ c

namesᵖ : Precondition → Names
namesᵖ = {-SETₛ.nub ∘-} go
  where
    go : Precondition → Names
    go (_ :? _ at x) = [ x ]
    go (_ :! _ at x) = [ x ]
    go (_ :secret a) = [ a ]
    go (p₁ ∣∣ p₂)     = go p₁ ++ go p₂

-- Secrets

secretsᶜ   : Contract                 → Secrets
secretsᶜˢ  : Contracts                → Secrets
secretsᵛᶜˢ : List (Value × Contracts) → Secrets

secretsᶜˢ []       = []
secretsᶜˢ (c ∷ cs) = secretsᶜ c ++ secretsᶜˢ cs

secretsᵛᶜˢ []               = []
secretsᵛᶜˢ ((_ , cs) ∷ vcs) = secretsᶜˢ cs ++ secretsᵛᶜˢ vcs

secretsᶜ (put _ &reveal as if _ ⇒ cs) = as ++ secretsᶜˢ cs
secretsᶜ (withdraw _)                 = []
secretsᶜ (split vcs)                  = secretsᵛᶜˢ vcs
secretsᶜ (_ ⇒ c)                      = secretsᶜ c
secretsᶜ (after _ ⇒ c)                = secretsᶜ c

secretsᵖ : Precondition → Secrets
secretsᵖ = {-SETₛ.nub ∘-} go
  where
    go : Precondition → Secrets
    go (_ :secret s) = [ s ]
    go (l ∣∣ r )     = go l ++ go r
    go _             = []

secretsOfᵖ : Participant → Precondition → Secrets
secretsOfᵖ A = {-SETₛ.nub ∘-} go
  where
    go : Precondition → Secrets
    go (B :secret s) with A ≟ₚ B
    ... | yes _ = [ s ]
    ... | no  _ = []
    go (l ∣∣ r )     = go l ++ go r
    go _             = []

-- Participants

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
participantsᵖ = {-SETₚ.nub ∘-} go
  where
    go : Precondition → List Participant
    go (p :? _ at _) = [ p ]
    go (p :! _ at _) = [ p ]
    go (p :secret _) = [ p ]
    go (p₁ ∣∣ p₂)    = go p₁ ++ go p₂

-- Put components

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

-- Deposits

depositsᵖ : Precondition → List DepositRef
depositsᵖ = {-SETₑ.nub ∘-} go
  where
    go : Precondition → List DepositRef
    go (a :! v at x) = [ a , v , x ]
    go (a :? v at x) = [ a , v , x ]
    go (_ :secret _) = []
    go (p₁ ∣∣ p₂)    = go p₁ ++ go p₂

persistentDepositsᵖ : Precondition → List DepositRef
persistentDepositsᵖ = {-SETₑ.nub ∘-} go
  where
    go : Precondition → List DepositRef
    go (a :! v at x) = [ a , v , x ]
    go (p₁ ∣∣ p₂)    = go p₁ ++ go p₂
    go _             = []

persistentParticipantsᵖ : Precondition → List Participant
persistentParticipantsᵖ = {-SETₚ.nub ∘-} go
  where
    go : Precondition → List Participant
    go (A :! _ at _) = [ A ]
    go (p ∣∣ p₁)     = go p ++ go p₁
    go _             = []

depositsᵃ : Advertisement → List DepositRef
depositsᵃ = depositsᵖ ∘ G

-- Decorations

decorations⊎ : Contract → List (Participant ⊎ Time)
decorations⊎ (A       ⇒ d) = inj₁ A ∷ decorations⊎ d
decorations⊎ (after t ⇒ d) = inj₂ t ∷ decorations⊎ d
decorations⊎ _             = []

decorations : Contract → List Participant × List Time
decorations c with partitionSums (decorations⊎ c)
... | (ps , ts) = {-SETₚ.nub-} ps , {-SETₙ.nub-} ts

authDecorations : Contract → List Participant
authDecorations = proj₁ ∘ decorations

timeDecorations : Contract → List Time
timeDecorations = proj₂ ∘ decorations

removeTopDecorations : Contract → Contract
removeTopDecorations (_       ⇒ d) = removeTopDecorations d
removeTopDecorations (after _ ⇒ d) = removeTopDecorations d
removeTopDecorations d             = d
