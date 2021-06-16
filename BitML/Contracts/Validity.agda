------------------------------------------------------------------------
-- Validity of advertisements.
------------------------------------------------------------------------
open import Function using (id)

open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Binary.Subset.Propositional.Properties

open import Prelude.Init
open import Prelude.General
open import Prelude.Lists
open import Prelude.DecLists
open import Prelude.DecEq
-- open import Prelude.Membership
open import Prelude.Sets
open import Prelude.Measurable
open import Prelude.Collections
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
  where
    goᶜ : (C : Contract) → Value → Bool
    goᶜˢ : (C : Contracts) → Value → Bool
    goᵛᶜˢ : (C : VContracts) → Bool

    goᵛᶜˢ [] = true
    goᵛᶜˢ ((v , cs) ∷ vcs) = goᶜˢ cs v

    goᶜˢ [] _ = true
    goᶜˢ (c ∷ cs) v = goᶜ c v ∧ goᶜˢ cs v

    goᶜ c₀@(put xs &reveal as if p ⇒ c) v
      with sequenceM $ map (λ x → checkDeposit volatile x G) xs
    ... | nothing = false
    ... | just vs = goᶜˢ c (∑ℕ vs)
    goᶜ (split vcs)   v = (∑₁ vcs == v) ∧ goᵛᶜˢ vcs
    goᶜ (after _ ⇒ c) v = goᶜ c v
    goᶜ (_ ⇒ c)       v = goᶜ c v
    goᶜ (withdraw _)  _ = true

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
