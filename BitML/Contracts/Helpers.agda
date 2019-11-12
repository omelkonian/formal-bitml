------------------------------------------------------------------------
-- Utilities for contracts, preconditions and advertisments.
------------------------------------------------------------------------

open import Function using (_∘_)

open import Data.Product using (_×_; _,_; Σ-syntax; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Nat     using (_>_)
open import Data.List    using (List; []; _∷_; [_]; length; _++_; map; partitionSums)

open import Data.List.Membership.Propositional            using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any                  using (Any; here; there)

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

namesᶜ (put xs &reveal as if _ ⇒ cs) = map inj₂ xs ++ map inj₁ as ++ namesᶜˢ cs
namesᶜ (withdraw _)                 = []
namesᶜ (split vcs)                  = namesᵛᶜˢ vcs
namesᶜ (_ ⇒ c)                      = namesᶜ c
namesᶜ (after _ ⇒ c)                = namesᶜ c

namesᵖ : Precondition → Names
namesᵖ = {-SETₛ.nub ∘-} go
  where
    go : Precondition → Names
    go (_ :? _ at x) = [ inj₂ x ]
    go (_ :! _ at x) = [ inj₂ x ]
    go (_ :secret a) = [ inj₁ a ]
    go (p₁ ∣∣ p₂)     = go p₁ ++ go p₂

-- Secrets

secretsᶜ   : Contract                 → Secrets
secretsᶜˢ  : Contracts                → Secrets
secretsᵛᶜˢ : List (Value × Contracts) → Secrets
secretsᶜ   = filter₁ ∘ namesᶜ
secretsᶜˢ  = filter₁ ∘ namesᶜˢ
secretsᵛᶜˢ = filter₁ ∘ namesᵛᶜˢ

secretsᵖ : Precondition → Secrets
secretsᵖ = filter₁ ∘ namesᵖ

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

getDeposit : ∀ {x g} → inj₂ x ∈ namesᵖ g → DepositRef
getDeposit {g = A :? v at x} (here refl) = A , v , x
getDeposit {g = A :! v at x} (here refl) = A , v , x
getDeposit {g = _ :secret _} (here ())
getDeposit {g = _ :secret _} (there ())
getDeposit {g = l ∣∣ r}      x∈
  with ∈-++⁻ (namesᵖ l) x∈
... | inj₁ x∈l = getDeposit {g = l} x∈l
... | inj₂ x∈r = getDeposit {g = r} x∈r

getName : (A , v , x) ∈ persistentDepositsᵖ g
        → inj₂ x ∈ namesᵖ g
getName {g = _ :! _ at _} (here refl) = here refl
getName {g = _ :! _ at _} (there ())
getName {g = l ∣∣ r}      d∈
  with ∈-++⁻ (persistentDepositsᵖ l) d∈
... | inj₁ d∈l = ∈-++⁺ˡ (getName {g = l} d∈l)
... | inj₂ d∈r = ∈-++⁺ʳ _ (getName {g = r} d∈r)

-- Decorations

decorations⊎ : Contract → List (Participant ⊎ Time)
decorations⊎ (A       ⇒ d) = inj₁ A ∷ decorations⊎ d
decorations⊎ (after t ⇒ d) = inj₂ t ∷ decorations⊎ d
decorations⊎ _             = []

decorations : Contract → List Participant × List Time
decorations c with partitionSums (decorations⊎ c)
... | (ps , ts) = {-SETₚ.nub-} ps , {-SETᵥ.nub-} ts

authDecorations : Contract → List Participant
authDecorations = proj₁ ∘ decorations

timeDecorations : Contract → List Time
timeDecorations = proj₂ ∘ decorations

removeTopDecorations : Contract → Contract
removeTopDecorations (_       ⇒ d) = removeTopDecorations d
removeTopDecorations (after _ ⇒ d) = removeTopDecorations d
removeTopDecorations d             = d

remove-putComponents : (putComponentsᶜ d) ≡ putComponentsᶜ (removeTopDecorations d)
remove-putComponents {_       ⇒ d} rewrite remove-putComponents {d} = refl
remove-putComponents {after _ ⇒ d} rewrite remove-putComponents {d} = refl
remove-putComponents {put _ &reveal _ if _ ⇒ _} = refl
remove-putComponents {withdraw _}               = refl
remove-putComponents {split _}                  = refl

remove-names : namesᶜ d ≡ namesᶜ (removeTopDecorations d)
remove-names {_       ⇒ d} rewrite remove-names {d} = refl
remove-names {after _ ⇒ d} rewrite remove-names {d} = refl
remove-names {put _ &reveal _ if _ ⇒ _} = refl
remove-names {withdraw _}               = refl
remove-names {split _}                  = refl
