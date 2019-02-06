------------------------------------------------------------------------
-- Types of configurations.
------------------------------------------------------------------------

open import Level        using (0ℓ)
open import Data.Empty   using (⊥)
open import Data.Unit    using (⊤; tt)
open import Data.Nat     using (ℕ; suc; _+_; _≤_; _>_; _≟_)
open import Data.Product using (∃; ∃-syntax; Σ; Σ-syntax; _×_; _,_)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.List    using (List; []; _∷_; [_]; _++_; length)
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

module Semantics.Configurations.Types
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

-------------------------------------------------------------------

infix  6 _auth[_]∶-_
infixl 4 _∣∣_∶-_

isValidSecret : Secret → ℕ ⊎ ⊥ → Set
isValidSecret _ (inj₂ _) = ⊤
isValidSecret s (inj₁ n) with lengthₛ s ≟ n
... | yes _ = ⊤
... | no  _ = ⊥

data Configuration′ :
    ------ current ------ × ----- required ------
    ( AdvertisedContracts × AdvertisedContracts )
  → ( ActiveContracts     × ActiveContracts     )
  → ( Deposits            × Deposits            )
  → Set where

  -- empty
  ∅ᶜ : Configuration′ ([] , []) ([] , []) ([] , [])

  -- contract advertisement
  `_ : ∀ {v vsᶜ vsᵍ}
     → (ad : Advertisement v vsᶜ vsᵍ)
     → Configuration′ ([ v , vsᶜ , vsᵍ , ad ] , []) ([] , []) ([] , [])

  -- active contract
  ⟨_,_⟩ᶜ : ∀ {v vs}
         → (c : Contracts v vs)
         → (v′ : Value) -- T0D0 remove, redundant?
         -- → .{pr : True (v ≟ v′)}
         → Configuration′ ([] , []) ([ v , vs , c ] , []) ([] , [])

  -- deposit redeemable by a participant
  ⟨_,_⟩ᵈ : (p : Participant)
         → (v : Value)
         → Configuration′ ([] , []) ([] , []) ([ p has v ] , [])

  -- authorization to perform an action
  _auth[_]∶-_ : ∀ {ads cs vs ds} {p₁ p₂ p₃}
              → (p : Participant)
              → Action p ads cs vs ds
              → .( (p₁ ≡ ([] , ads))
                 × (p₂ ≡ ([] , cs))
                 × (p₃ ≡ (ds , ((p has_) <$> vs)))
                 )
              → Configuration′ p₁ p₂ p₃

  -- committed secret
  ⟨_∶_♯_⟩ : Participant
          → (s : Secret)
          → (n : ℕ ⊎ ⊥)
          → .{pr : isValidSecret s n}
          → Configuration′ ([] , []) ([] , []) ([] , [])

  -- revealed secret
  _∶_♯_ : Participant
        → (s : Secret)
        → (n : ℕ)
        → .{pr : True (lengthₛ s ≟ n)}
        → Configuration′ ([] , []) ([] , []) ([] , [])

  -- parallel composition
  _∣∣_∶-_ : ∀ {adsˡ radsˡ adsʳ radsʳ ads rads : AdvertisedContracts}
              {csˡ rcsˡ csʳ rcsʳ cs rcs : ActiveContracts}
              {dsˡ rdsˡ dsʳ rdsʳ ds rds : Deposits}
          → Configuration′ (adsˡ , radsˡ) (csˡ , rcsˡ) (dsˡ , rdsˡ)
          → Configuration′ (adsʳ , radsʳ) (csʳ , rcsʳ) (dsʳ , rdsʳ)
          → .( ads  ≡ adsˡ ++ adsʳ
             × rads ≡ radsˡ ++ (radsʳ SETₐ.\\ adsˡ)
             × cs   ≡ csˡ  ++ csʳ
             × rcs  ≡ rcsˡ ++ (rcsʳ SETᶜ.\\ csˡ)
             × ds   ≡ (dsˡ SETₑ.\\ rdsʳ) ++ dsʳ -- NB: deposits are "linear"
             × rds  ≡ rdsˡ ++ (rdsʳ SETₑ.\\ dsˡ)
             )
          → Configuration′ (ads , rads) (cs , rcs) (ds , rds)

-- "Closed" configurations; they stand on their own.
Configuration : AdvertisedContracts → ActiveContracts → Deposits → Set
Configuration ads cs ds = Configuration′ (ads , []) (cs , []) (ds , [])
