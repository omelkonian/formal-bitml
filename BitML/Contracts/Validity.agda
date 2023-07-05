------------------------------------------------------------------------
-- Validity of advertisements.
------------------------------------------------------------------------
open import Function using (id)

open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Binary.Subset.Propositional.Properties

open import Prelude.Init
open import Prelude.General
open import Prelude.Lists
open import Prelude.Lists.Dec
open import Prelude.DecEq
open import Prelude.Sets
open import Prelude.Measurable
open import Prelude.Lists.Collections
open import Prelude.Membership
open import Prelude.Functor
open import Prelude.Foldable
open import Prelude.Traversable
open import Prelude.Monad
open import Prelude.Validity
open import Prelude.Decidable

open import BitML.BasicTypes
open import BitML.Predicate hiding (∣_∣)

module BitML.Contracts.Validity
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import BitML.Contracts.Types Participant Honest hiding (B)
open import BitML.Contracts.Helpers Participant Honest

splitsOK : Precondition → Contract → Bool
splitsOK G C₀ = goᶜ C₀ (persistentValue G)
  where
    goᵈ  : Branch → Value → Bool
    goᶜ  : Contract → Value → Bool
    goᵛᶜ : VContracts → Bool

    goᵛᶜ [] = true
    goᵛᶜ ((v , cs) ∷ vcs) = goᶜ cs v

    goᶜ [] _ = true
    goᶜ (c ∷ cs) v = goᵈ c v ∧ goᶜ cs v

    goᵈ c₀@(put xs &reveal as if p ⇒ c) v
      with sequenceM $ map (λ x → checkDeposit volatile x G) xs
    ... | nothing = false
    ... | just vs = goᶜ c (∑ℕ vs)
    goᵈ (split vcs)   v = (∑₁ vcs == v) ∧ goᵛᶜ vcs
    goᵈ (after _ ⇒ c) v = goᵈ c v
    goᵈ (_ ⇒ c)       v = goᵈ c v
    goᵈ (withdraw _)  _ = true

record ValidAdvertisement (ad : Advertisement) : Set where
  -- open Advertisement ad renaming (C to c; G to g) -- ⟨ G ⟩ C = ad
  field
    -- (i) names in G are distinct
    names-uniq : Unique (names $ G ad)

    -- (ii) each name in C appears in G
    names-⊆ : names (C ad) ⊆ names (G ad)

    -- (iii) the names in put_&reveal_ are distinct and secrets in `if ...` appear in `reveal ...`
    names-put : All (λ{ (xs , as , p) → Unique xs × (secrets p ⊆ as)}) (putComponents $ C ad)

    -- (iv) each participant has a persistent deposit in G
    participants-⊆ : participants (G ad) ++ participants (C ad) ⊆ persistentParticipants (G ad)

    -- (extra) split commands are valid
    splits-OK : T $ splitsOK (G ad) (C ad)

open ValidAdvertisement public

instance
  𝕍Ad : Validable Advertisement
  𝕍Ad .Valid = ValidAdvertisement

  Dec-𝕍Ad : Valid ⁇¹
  Dec-𝕍Ad {x = ⟨ G ⟩ C} .dec
    with unique? (names G)
       | names C ⊆? names G
       | all? (λ{ (xs , as , p) → unique? xs ×-dec (secrets p ⊆? as)}) (putComponents C)
       | participants G ++ participants C ⊆? persistentParticipants G
       | T? (splitsOK G C)
  ... | no ¬names-uniq | _ | _ | _ | _     = no $ ¬names-uniq ∘ names-uniq
  ... | _ | no ¬names-⊆ | _ | _ | _        = no $ ¬names-⊆ ∘ names-⊆
  ... | _ | _ | no ¬names-put | _ | _      = no $ ¬names-put ∘ names-put
  ... | _ | _ | _ | no ¬participants-⊆ | _ = no $ ¬participants-⊆ ∘ participants-⊆
  ... | _ | _ | _ | _ | no ¬splits-OK      = no $ ¬splits-OK ∘ splits-OK
  ... | yes p₁ | yes p₂ | yes p₃ | yes p₄ | yes p₅ = yes λ where
    .names-uniq → p₁; .names-⊆ → p₂; .names-put → p₃; .participants-⊆ → p₄; .splits-OK → p₅


-- Properties.

Valid⇒part⊆ : let ⟨ G ⟩ C = ad in
  Valid ad → participants C ⊆ participants G
Valid⇒part⊆ {⟨ G ⟩ C} vad
  = persistentParticipants⊆ {g = G}
  ∘ vad .participants-⊆
  ∘ ∈-++⁺ʳ (participants G)

subterms′-part⊆ᵃ : Valid ad → d ∈ subtermsᵃ′ ad → participants d ⊆ participants (ad .G)
subterms′-part⊆ᵃ {ad@(⟨ G ⟩ C)}{d} vad d∈ = Valid⇒part⊆ vad ∘ subterms′-part⊆ᶜ {ds = C} d∈
