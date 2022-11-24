------------------------------------------------------------------------
-- Validity of advertisements.
------------------------------------------------------------------------
open import Prelude.Init
open import Prelude.General
open import Prelude.Lists
open import Prelude.DecLists
open import Prelude.DecEq
open import Prelude.Sets
open import Prelude.Measurable
open import Prelude.Collections
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

splitsOK : Precondition → Contracts → Bool
splitsOK G C₀ = goᶜˢ C₀ (persistentValue G)
  where mutual
    goᶜ : Contract → Value → Bool
    goᶜ c₀@(put xs &reveal as if p ⇒ c) v
      with sequenceMˢ (mapˢ (λ x → checkDeposit volatile x G) xs)
    ... | nothing = false
    ... | just vs = goᶜˢ c (sumˢ vs)
    goᶜ (split vcs)   v = (∑₁ vcs == v) ∧ goᵛᶜˢ vcs
    goᶜ (after _ ⇒ c) v = goᶜ c v
    goᶜ (_ ⇒ c)       v = goᶜ c v
    goᶜ (withdraw _)  _ = true


    goᶜˢ : Contracts → Value → Bool
    goᶜˢ [] _ = true
    goᶜˢ (c ∷ cs) v = goᶜ c v ∧ goᶜˢ cs v

    goᵛᶜˢ : VContracts → Bool
    goᵛᶜˢ [] = true
    goᵛᶜˢ ((v , cs) ∷ vcs) = goᶜˢ cs v

record ValidAdvertisement (ad : Advertisement) : Set where
  -- open Advertisement ad renaming (C to c; G to g) -- ⟨ G ⟩ C = ad
  field
    -- (i) names in G are distinct (BY CONSTRUCTION)

    -- (ii) each name in C appears in G
    names-⊆ : names (C ad) ⊆ˢ names (G ad)

    -- (iii) the names in put_&reveal_ are distinct and secrets in `if ...` appear in `reveal ...`
    names-put : Allˢ (λ{ (xs , as , p) → secrets p ⊆ˢ as}) (putComponents $ ad .C)

    -- (iv) each participant has a persistent deposit in G
    participants-⊆ : participants (ad .G) ∪ participants (ad .C) ⊆ˢ persistentParticipants (ad .G)

    -- (extra) split commands are valid
    splits-OK : T $ splitsOK (ad .G) (ad .C)

open ValidAdvertisement public

instance
  𝕍Ad : Validable Advertisement
  𝕍Ad .Valid = ValidAdvertisement

  Dec-𝕍Ad : Valid ⁇¹
  Dec-𝕍Ad {x = ⟨ G ⟩ C} .dec
    with names C ⊆?ˢ names G
       | allˢ? (λ{ (xs , as , p) → (secrets p ⊆?ˢ as)}) (putComponents C)
       | (participants G ∪ participants C) ⊆?ˢ persistentParticipants G
       | T? (splitsOK G C)
  ... | no ¬names-⊆ | _ | _ | _        = no $ ¬names-⊆ ∘ names-⊆
  ... | _ | no ¬names-put | _ | _      = no $ ¬names-put ∘ names-put
  ... | _ | _ | no ¬participants-⊆ | _ = no $ ¬participants-⊆ ∘ participants-⊆
  ... | _ | _ | _ | no ¬splits-OK      = no $ ¬splits-OK ∘ splits-OK
  ... | yes p₁ | yes p₂ | yes p₃ | yes p₄ = yes λ where
    .names-⊆ → p₁; .names-put → p₂; .participants-⊆ → p₃; .splits-OK → p₄

-- Properties.

Valid⇒part⊆ : let ⟨ G ⟩ C = ad in
  Valid ad → participants C ⊆ˢ participants G
Valid⇒part⊆ {⟨ G ⟩ C} vad
  = persistentParticipants⊆ {g = G}
  ∘ vad .participants-⊆
  ∘ ∈-∪⁺ʳ _ (participants G) (participants C)

subterms′-part⊆ᵃ : Valid ad → d ∈ subtermsᵃ′ ad → participants d ⊆ˢ participants (ad .G)
subterms′-part⊆ᵃ {ad@(⟨ G ⟩ C)}{d} vad d∈ = Valid⇒part⊆ vad ∘ subterms′-part⊆ᶜˢ {ds = C} d∈
