------------------------------------------------------------------------
-- Utilities for constructing configurations.
------------------------------------------------------------------------
open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Sets
open import Prelude.Collections
open import Prelude.Applicative
open import Prelude.Semigroup
open import Prelude.Nary

open import BitML.BasicTypes

module BitML.Semantics.Configurations.Helpers
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
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
_≈_ : Rel₀ Configuration
c ≈ c′ = cfgToList c ↭ cfgToList c′

infix 3 _≈?_
_≈?_ : Decidable² {A = Configuration} _≈_
c ≈? c′ = cfgToList c ↭? cfgToList c′

infix 4 _∈ᶜ_
_∈ᶜ_ : Rel₀ Configuration
c ∈ᶜ c′ = c ∈ cfgToList c′

private variable X : Set

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
  -- secrets
  ... | ⟨ _ ∶ s ♯ _ ⟩   = [ inj₁ s ]
  ... | _ ∶ s ♯ _       = [ inj₁ s ]
  -- names
  ... | ⟨ _ ,   _ ⟩at x = [ inj₂ x ]
  ... | ⟨ _ has _ ⟩at x = [ inj₂ x ]
  -- other
  ... | l ∣ r           = collect l ++ collect r
  ... | _               = []
  -- ... | ∅ᶜ              = []
  -- ... | ` ad            = []
  -- ... | ` (⟨ G ⟩ _)     = collect G
  -- ... | _ auth[ ac ]    = []

  HAᶜᶠ : Configuration has Action
  HAᶜᶠ .collect c with c
  ... | _ auth[ a ] = [ a ]
  ... | l ∣ r       = collect l ++ collect r
  ... | _           = []

  -- ** See `authorizedHonAds` below
  -- HAᶜᶠ : Configuration has Advertisement
  -- HAᶜᶠ .collect c with c
  -- ... | ` ad  = [ ad ]
  -- ... | l ∣ r = collect l ++ collect r
  -- ... | _     = []

  Hᶜᶠ⇒Hᵗᶜᶠ : ∀ {X : Set} ⦃ _ : Configuration has X ⦄ → TimedConfiguration has X
  Hᶜᶠ⇒Hᵗᶜᶠ .collect (Γ at _) = collect Γ

advertisements : ⦃ _ :  X has Advertisement ⦄ → X → List Advertisement
advertisements = collect

-- authorizedActions : ⦃ _ :  X has Action ⦄ → X → List Action
-- authorizedActions = collect

-- authorizedAds : ⦃ _ :  X has Action ⦄ → X → List Advertisement
-- authorizedAds = mapMaybe (case_of λ{ (♯▷ ad) → just ad; _ → nothing })
--               ∘ authorizedActions

authorizedHonAds : Configuration → List Advertisement
authorizedHonAds (A auth[ ♯▷ ad ])
 with does (A ∈? Hon)
... | true  = [ ad ]
... | false = []
authorizedHonAds (l ∣ r) = authorizedHonAds l ++ authorizedHonAds r
authorizedHonAds _       = []

instance
  HAdᶜᶠ : Configuration has Advertisement
  HAdᶜᶠ .collect = authorizedHonAds

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

module _ (A∈ : A ∈ Hon) where
  committed⇒authAd :
      A ∈ committedParticipants Γ ad
    → ad ∈ authorizedHonAds Γ
  -- committed⇒authAd {Γ} {ad} P
  committed⇒authAd {p auth[ ♯▷ ad′ ]} {ad} P
    with ad ≟ ad′ | P
  ... | no _    | ()
  ... | yes ad≡ | here refl
    rewrite dec-true (A ∈? Hon) A∈
    = here ad≡
  committed⇒authAd {l ∣ r} {ad} P with L.Mem.∈-++⁻ (committedParticipants l ad) P
  ... | inj₁ ∈l = L.Mem.∈-++⁺ˡ (committed⇒authAd {Γ = l} ∈l)
  ... | inj₂ ∈r = L.Mem.∈-++⁺ʳ _ (committed⇒authAd {Γ = r} ∈r)

isInitial : Configuration → Bool
isInitial (⟨ _ has _ ⟩at _) = true
isInitial (l ∣ r)           = isInitial l ∧ isInitial r
isInitial _                 = false

Initial : Configuration → Set
Initial = T ∘ isInitial
