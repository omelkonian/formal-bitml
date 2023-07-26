------------------------------------------------------------------------
-- Validity of advertisements.
------------------------------------------------------------------------
open import Function using (id)

open import Prelude.Init hiding (_⊆_); open SetAsType
open L.Mem
open import Prelude.General
open import Prelude.Lists renaming (_⊆′_ to _⊆_)
open import Prelude.Lists.Dec hiding (_⊆?_) renaming (_⊆′?_ to _⊆?_)
open import Prelude.DecEq
open import Prelude.Sets
open import Prelude.Measurable
open import Prelude.Lists.Collections
open import Prelude.Functor
open import Prelude.Foldable
open import Prelude.Traversable
open import Prelude.Monad
open import Prelude.Validity
open import Prelude.Decidable

open import BitML.BasicTypes
open import BitML.Predicate hiding (∣_∣)

module BitML.Contracts.Validity (⋯ : ⋯) where

open import BitML.Contracts.Types ⋯ hiding (B)
open import BitML.Contracts.Helpers ⋯

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

    goᵈ c₀@(put xs &reveal as if p ⇒ c) v =
      case sequenceM $ map (λ x → checkDeposit volatile x G) xs of λ where
        nothing   → false
        (just vs) → goᶜ c (v + ∑ℕ vs)
    goᵈ (split vcs)   v = (∑₁ vcs == v) ∧ goᵛᶜ vcs
    goᵈ (after _ ∶ c) v = goᵈ c v
    goᵈ (_ ∶ c)       v = goᵈ c v
    goᵈ (withdraw _)  _ = true

module _ (ad : Ad) (let ⟨ G ⟩ C = ad) where
  record ValidAd : Type where
    field
      -- (i) names in G are distinct
      names-uniq :
        Unique $ names G

      -- (ii) each name in C appears in G
      names-⊆ :
        names C ⊆ names G

      -- (iii) names in `put&reveal` are distinct and secrets in `if` appear in `reveal`
      names-put :
        All (λ (xs , as , p) → Unique xs × secrets p ⊆ as) (putComponents C)

      -- (iv) each participant has a persistent deposit in G
      parts-⊆ :
        participants G ++ participants C ⊆ persistentParticipants G

      -- (extra) split commands are valid
      splits-OK :
        T $ splitsOK G C

open ValidAd public

instance
  𝕍Ad : Validable Ad
  𝕍Ad .Valid = ValidAd

  Dec-𝕍Ad : Valid ⁇¹
  Dec-𝕍Ad {x = ⟨ G ⟩ C} .dec
    with unique? $ names G
       | names C ⊆? names G
       | all? (λ (xs , as , p) → unique? xs ×-dec secrets p ⊆? as) (putComponents C)
       | participants G ++ participants C ⊆? persistentParticipants G
       | T? $ splitsOK G C
  ... | no ¬names-uniq | _ | _ | _ | _             = no $ ¬names-uniq ∘ names-uniq
  ... | _ | no ¬names-⊆ | _ | _ | _                = no $ ¬names-⊆    ∘ names-⊆
  ... | _ | _ | no ¬names-put | _ | _              = no $ ¬names-put  ∘ names-put
  ... | _ | _ | _ | no ¬parts-⊆ | _                = no $ ¬parts-⊆    ∘ parts-⊆
  ... | _ | _ | _ | _ | no ¬splits-OK              = no $ ¬splits-OK  ∘ splits-OK
  ... | yes p₁ | yes p₂ | yes p₃ | yes p₄ | yes p₅ = yes λ where
    .names-uniq → p₁; .names-⊆ → p₂; .names-put → p₃; .parts-⊆ → p₄; .splits-OK → p₅


-- Properties.

Valid⇒part⊆ : let ⟨ G ⟩ C = ad in
  Valid ad → participants C L.SubS.⊆ participants G
Valid⇒part⊆ {⟨ G ⟩ C} vad
  = persistentParticipants⊆ {g = G}
  ∘ vad .parts-⊆ .unmk⊆
  ∘ ∈-++⁺ʳ (participants G)

subterms′-part⊆ᵃ : Valid ad → d ∈ subtermsᵃ′ ad →
  participants d L.SubS.⊆ participants (ad .G)
subterms′-part⊆ᵃ {ad@(⟨ G ⟩ C)}{d} vad d∈ =
  Valid⇒part⊆ vad ∘ subterms′-part⊆ᶜ {ds = C} d∈
