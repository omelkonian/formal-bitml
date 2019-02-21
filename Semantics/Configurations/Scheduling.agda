------------------------------------------------------------------------
-- Scheduling configurations.
------------------------------------------------------------------------

open import Level        using (0ℓ)
open import Function     using (_∘_)
open import Data.Empty   using (⊥)
open import Data.Unit    using (⊤; tt)
open import Data.Nat     using (ℕ; suc; _+_; _≤_; _>_; _≟_)
open import Data.Product using (∃; ∃-syntax; Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.List    using (List; []; _∷_; [_]; _++_; length; map; concatMap)
open import Data.String  using ()
  renaming (length to lengthₛ)

open import Relation.Binary using (Decidable)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (True; False)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; sym)

open import Category.Functor using (RawFunctor)
open import Data.List.Categorical renaming (functor to listFunctor)
open RawFunctor {0ℓ} listFunctor using (_<$>_)

module Semantics.Configurations.Scheduling
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))
  where

open import Utilities.Lists
open import Types                               Participant _≟ₚ_ Honest
open import BitML.Types                         Participant _≟ₚ_ Honest
open import BitML.DecidableEquality             Participant _≟ₚ_ Honest
open import Semantics.Actions.Types             Participant _≟ₚ_ Honest
open import Semantics.Actions.DecidableEquality Participant _≟ₚ_ Honest
open import Semantics.Configurations.Types      Participant _≟ₚ_ Honest
open import Semantics.Configurations.Helpers    Participant _≟ₚ_ Honest

-------------------------------------------------------------------

Cfgs : Set
Cfgs = List (∃[ p₁ ] ∃[ p₂ ] ∃[ p₃ ] Configuration′ p₁ p₂ p₃)

all-ads : Cfgs → AdvertisedContracts
all-ads = concatMap (proj₁ ∘ proj₁)

all-rads : Cfgs → AdvertisedContracts
all-rads = concatMap (proj₂ ∘ proj₁)

all-cs : Cfgs → ActiveContracts
all-cs = concatMap (proj₁ ∘ proj₁ ∘ proj₂)

all-rcs : Cfgs → ActiveContracts
all-rcs = concatMap (proj₂ ∘ proj₁ ∘ proj₂)

all-ds : Cfgs → Deposits
all-ds = concatMap (proj₁ ∘ proj₁ ∘ proj₂ ∘ proj₂)

all-rds : Cfgs → Deposits
all-rds = concatMap (proj₂ ∘ proj₁ ∘ proj₂ ∘ proj₂)

postulate
  σ : ∀ {ads cs ds rads rcs rds}
    → (Γ : Configuration′ (ads , rads) (cs , rcs) (ds , rds))
    → Σ[ front ∈ Cfgs ]
        let
          init : Cfgs
          init = cfgToList Γ

          ads′  = ads SETₐ.\\ all-ads front
          rads′ = -- fresh rads resulting from extracted ads
                  map {!!} (all-ads front)
                  -- previous rads that have not been extracted
               ++ ( rads SETₐ.\\ {!!})
          cs′   = cs SETᶜ.\\ all-cs front
          rcs′  = -- fresh rcs resulting from extracted cs
                  map {!!} (all-cs front)
                  -- previous rcs that have not been extracted
               ++ ( rcs SETᶜ.\\ {!!})
          ds′   = {!!}
          rds′  = {!!}
        in
          Configuration′ (ads′ , rads′) (cs′ , rcs′) (ds′ , rds′)
