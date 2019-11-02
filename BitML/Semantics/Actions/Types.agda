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

open import Prelude.Lists

module BitML.Semantics.Actions.Types
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))
  where

open import BitML.BasicTypes      Participant _≟ₚ_ Honest
open import BitML.Contracts.Types Participant _≟ₚ_ Honest

--------------------------------------------------------------------------------

AdvertisedContracts : Set
AdvertisedContracts = List ∃Advertisement

ActiveContracts : Set
ActiveContracts = List ∃Contracts

variable
  ads ads′ ads″ rads adsˡ radsˡ adsʳ radsʳ : AdvertisedContracts
  cs cs′ cs″ rcs csˡ rcsˡ csʳ rcsʳ : ActiveContracts
  ds ds′ ds″ rds dsˡ rdsˡ dsʳ rdsʳ : Deposits

-- Indices for `Action`.
record Actionⁱ : Set where
  constructor Iᵃᶜ[_,_,_,_]
  field
    advertisements   : AdvertisedContracts -- the contract advertisements it requires
    contracts        : ActiveContracts     -- the active contracts it requires
    depositsRequired : Values              -- the deposits it requires from this participant
    depositsProduced : Deposits            -- the deposits it produces
open Actionⁱ public
variable aci : Actionⁱ

data Action (p : Participant) : Actionⁱ → Set where

  -- commit secrets to stipulate {G}C
  ♯▷_ : (ad : Advertisement ci pi)
      → Action p Iᵃᶜ[ [ ci , pi , ad ] , [] , [] , [] ]

  -- spend x to stipulate {G}C
  _▷ˢ_ : (ad : Advertisement ci Iᵖ[ vsᵛ , vsᵖ ])
       → (i : Index vsᵖ)
       → {vs : Values}
       → .{pr : True (vs SETₙ.≟ₗ [ vsᵖ ‼ i ])}
       → Action p Iᵃᶜ[ [ ci , Iᵖ[ vsᵛ , vsᵖ ] , ad ] , [] , vs , [] ]

  -- take branch
  _▷ᵇ_ : (c : Contracts ci)
       → (i : Index c)
       → Action p Iᵃᶜ[ [] , [ ci , c ] , [] , [] ]

  -- join deposits
  _↔_ : (x : Index vs)
      → (y : Index vs)
      → {ds : Deposits}
      → .{pr₁ : False (x ≟ᶠ y)}
      → .{pr₂ : True (ds SETₑ.≟ₗ ((p has_) <$> vs at x ⟨ (vs ‼ x) + (vs ‼ y) ⟩remove y))}
      → Action p Iᵃᶜ[ [] , [] , vs , ds ]

  -- divide a deposit
  _▷_,_ : (i : Index vs)
        → (v₁ : Value)
        → (v₂ : Value)
        → {ds : Deposits}
        → .{pr₁ : True ((vs ‼ i) ≟ (v₁ + v₂))}
        → .{pr₂ : True (ds SETₑ.≟ₗ ((p has_) <$> (vs at i ⟨ v₁ ⟩ ++ [ v₂ ])))}
        → Action p Iᵃᶜ[ [] , [] , vs , ds ]

  -- donate deposit to participant
  _▷ᵈ_ : (i : Index vs)
       → (p′ : Participant)
       → {ds : Deposits}
       → .{pr : True (ds SETₑ.≟ₗ [ p′ has (vs ‼ i) ])}
       → Action p Iᵃᶜ[ [] , [] , vs , ds ]

  -- destroy deposit
  destroy : (i : Index vs)
          → {ds : Deposits}
          → .{pr : True (ds SETₑ.≟ₗ (p has_ <$> remove vs i))}
          → Action p Iᵃᶜ[ [] , [] , vs , ds ]

∃Action : Set
∃Action = ∃[ p ] ∃[ aci ] Action p aci
