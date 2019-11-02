------------------------------------------------------------------------
-- Types of configurations.
------------------------------------------------------------------------

open import Level        using (0ℓ)
open import Data.Empty   using (⊥)
open import Data.Unit    using (⊤; tt)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Nat     using (ℕ; suc; _+_; _≤_; _>_; _≟_)
open import Data.Product using (∃; ∃-syntax; Σ; Σ-syntax; _×_; _,_)
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

open import Prelude.Lists

module BitML.Semantics.Configurations.Types
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))
  where

open import BitML.BasicTypes                          Participant _≟ₚ_ Honest
open import BitML.Contracts.Types                     Participant _≟ₚ_ Honest
open import BitML.Contracts.DecidableEquality         Participant _≟ₚ_ Honest
open import BitML.Semantics.Actions.Types             Participant _≟ₚ_ Honest
open import BitML.Semantics.Actions.DecidableEquality Participant _≟ₚ_ Honest

-------------------------------------------------------------------

infix  6 _auth[_]∶-_
infixl 4 _∣∣_∶-_

isValidSecret : Secret → Maybe ℕ → Set
isValidSecret _ nothing = ⊤
isValidSecret s (just n) with lengthₛ s ≟ n
... | yes _ = ⊤
... | no  _ = ⊥

record Configuration′ⁱ : Set where
  constructor Iᶜᶠ[_,_,_]
  field             ------ current ---- × ----- required ----
    advertisments : AdvertisedContracts × AdvertisedContracts
    contracts     : ActiveContracts     × ActiveContracts
    deposits      : Deposits            × Deposits
open Configuration′ⁱ public
variable cf′i cf′i′ cf′i″ : Configuration′ⁱ

data Configuration′ : Configuration′ⁱ → Set where

  -- empty
  ∅ᶜ : Configuration′ Iᶜᶠ[ [] & [] , [] & [] , [] & [] ]

  -- contract advertisement
  `_ : (ad : Advertisement ci pi)
     → Configuration′ Iᶜᶠ[ [ ci , pi , ad ] & [] , [] & [] , [] & [] ]

  -- active contract
  ⟨_⟩ᶜ : (c : Contracts ci)
       → Configuration′ Iᶜᶠ[ [] & [] , [ ci , c ] & [] , [] & [] ]

  -- deposit redeemable by a participant
  ⟨_,_⟩ᵈ : (p : Participant)
         → (v : Value)
         → Configuration′ Iᶜᶠ[ [] & [] , [] & [] , [ p has v ] & [] ]

  -- authorization to perform an action
  _auth[_]∶-_ : ∀ {p₁₁ p₁₂ p₂₁ p₂₂ p₃₁ p₃₂}
              → (p : Participant)
              → Action p Iᵃᶜ[ ads , cs , vs , ds ]
              → .( (p₁₁ ≡ [])
                 × (p₁₂ ≡ ads)
                 × (p₂₁ ≡ [])
                 × (p₂₂ ≡ cs)
                 × (p₃₁ ≡ ds)
                 × (p₃₂ ≡ ((p has_) <$> vs))
                 )
              → Configuration′ Iᶜᶠ[ p₁₁ & p₁₂ , p₂₁ & p₂₂ , p₃₁ & p₃₂ ]

  -- committed secret
  ⟨_∶_♯_⟩ : Participant
          → (s : Secret)
          → (n : Maybe ℕ)
          → .{pr : isValidSecret s n}
          → Configuration′ Iᶜᶠ[ [] & [] , [] & [] , [] & [] ]

  -- revealed secret
  _∶_♯_ : Participant
        → (s : Secret)
        → (n : ℕ)
        → .{pr : True (lengthₛ s ≟ n)}
        → Configuration′ Iᶜᶠ[ [] & [] , [] & [] , [] & [] ]

  -- parallel composition
  _∣∣_∶-_ : Configuration′ Iᶜᶠ[ adsˡ & radsˡ , csˡ & rcsˡ , dsˡ & rdsˡ ]
          → Configuration′ Iᶜᶠ[ adsʳ & radsʳ , csʳ & rcsʳ , dsʳ & rdsʳ ]
          → .( ads  ≡ adsˡ ++ adsʳ
             × rads ≡ radsˡ ++ (radsʳ SETₐ.\\ adsˡ)
             × cs   ≡ csˡ  ++ csʳ
             × rcs  ≡ rcsˡ ++ (rcsʳ SETᶜ.\\ csˡ)
             × ds   ≡ (dsˡ SETₑ.\\ rdsʳ) ++ dsʳ -- NB: deposits are "linear"
             × rds  ≡ rdsˡ ++ (rdsʳ SETₑ.\\ dsˡ)
             )
          → Configuration′ Iᶜᶠ[ ads & rads , cs & rcs , ds & rds ]

∃Configuration′ : Set
∃Configuration′ = ∃[ cfi′ ] Configuration′ cfi′

-- "Closed" configurations; they stand on their own.

record Configurationⁱ : Set where
  constructor Iᶜᶠ[_,_,_]
  field
    advertisments : AdvertisedContracts
    contracts     : ActiveContracts
    deposits      : Deposits
open Configurationⁱ public
variable cfi cfi′ cfi″ : Configurationⁱ

Configuration : Configurationⁱ → Set
Configuration Iᶜᶠ[ ads , cs , ds ] = Configuration′ Iᶜᶠ[ ads & [] , cs & [] , ds & [] ]

∃Configuration : Set
∃Configuration = ∃[ cfi ] Configuration cfi

record TimedConfiguration (cfi : Configurationⁱ) : Set where
  -- constructor _at_
  field
    cfg  : Configuration cfi
    time : Time
pattern _at_ Γ t = record {cfg = Γ ; time = t}
open TimedConfiguration public

∃TimedConfiguration : Set
∃TimedConfiguration = ∃[ cfi ] TimedConfiguration cfi
