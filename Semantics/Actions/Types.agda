------------------------------------------------------------------------
-- Types of actions.
------------------------------------------------------------------------

open import Level        using (0ℓ)
open import Data.Nat     using (ℕ; _≟_; _>_; _+_)
open import Data.Product using (∃; ∃-syntax; Σ; Σ-syntax; _,_)
open import Data.List    using (List; []; _∷_; [_]; _++_; map; length)
open import Data.Fin     using ()
  renaming (_≟_ to _≟ᶠ_)

open import Relation.Nullary                      using (yes; no)
open import Relation.Nullary.Decidable            using (True; False; fromWitness)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Category.Functor using (RawFunctor)
open import Data.List.Categorical renaming (functor to listFunctor)
open RawFunctor {0ℓ} listFunctor using (_<$>_)

module Semantics.Actions.Types
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))
  where

open import Utilities.Lists

open import Types       Participant _≟ₚ_ Honest
open import BitML.Types Participant _≟ₚ_ Honest

--------------------------------------------------------------------------------

AdvertisedContracts : Set
AdvertisedContracts = List (∃[ v ] ∃[ vsᶜ ] ∃[ vsᵍ ] Advertisement v vsᶜ vsᵍ)

ActiveContracts : Set
ActiveContracts = List (∃[ v ] ∃[ vs ] Contracts v vs)

data Action (p : Participant) -- the participant that authorises this action
  : AdvertisedContracts -- the contract advertisments it requires
  → ActiveContracts     -- the active contracts it requires
  → Values              -- the deposits it requires from this participant
  → Deposits            -- the deposits it produces
  → Set where

  -- commit secrets to stipulate {G}C
  ♯▷_ : ∀ {v vsᶜ vsᵍ} → (ad : Advertisement v vsᶜ vsᵍ)
      → Action p [ v , vsᶜ , vsᵍ , ad ] [] [] []

  -- spend x to stipulate {G}C
  _▷ˢ_ : ∀ {v vsᶜ vsᵍ}
       → (ad : Advertisement v vsᶜ vsᵍ)
       → (i : Index vsᵍ)
       → {vs : Values}
       → .{pr : True (vs SETₙ.≟ₗ [ vsᵍ ‼ i ])}
       → Action p [ v , vsᶜ , vsᵍ , ad ] [] vs []

  -- take branch
  _▷ᵇ_ : ∀ {v vs}
      → (c : Contracts v vs)
      → (i : Index c)
      → Action p [] [ v , vs , c ] [] []

  -- join deposits
  _↔_ : ∀ {vs}
      → (x : Index vs)
      → (y : Index vs)
      → {ds : Deposits}
      → .{pr₁ : False (x ≟ᶠ y)}
      → .{pr₂ : True (ds SETₑ.≟ₗ ((p has_) <$> vs at x ⟨ (vs ‼ x) + (vs ‼ y) ⟩remove y))}
      → Action p [] [] vs ds

  -- divide a deposit
  _▷_,_ : ∀ {vs}
    → (i : Index vs)
    → (v₁ : Value)
    → (v₂ : Value)
    → {ds : Deposits}
    → .{pr₁ : True ((vs ‼ i) ≟ (v₁ + v₂))}
    → .{pr₂ : True (ds SETₑ.≟ₗ ((p has_) <$> (vs at i ⟨ v₁ ⟩ ++ [ v₂ ])))}
    → Action p [] [] vs ds

  -- donate deposit to participant
  _▷ᵈ_ : ∀ {vs}
      → (i : Index vs)
      → (p′ : Participant)
      → {ds : Deposits}
      → .{pr : True (ds SETₑ.≟ₗ [ p′ has (vs ‼ i) ])}
      → Action p [] [] vs ds

  -- destroy deposit
  destroy : ∀ {vs}
        → (i : Index vs)
        → {ds : Deposits}
        → .{pr : True (ds SETₑ.≟ₗ (p has_ <$> remove vs i))}
        → Action p [] [] vs ds
