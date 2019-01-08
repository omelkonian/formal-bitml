open import Level         using (0ℓ)
open import Function      using (_on_; const; _∘_; id; _∋_; _$_)
open import Data.Empty    using (⊥; ⊥-elim)
open import Data.Unit     using (⊤; tt)
open import Data.Bool     using (T; Bool; true; false; _∧_)
open import Data.Maybe    using (Maybe; just; nothing; maybe′)
open import Data.Nat      using (ℕ; suc; _+_; _>_; _≟_)
open import Data.Product  using (∃; ∃-syntax; Σ; Σ-syntax; _×_; _,_)
open import Data.Sum      using (_⊎_; inj₁; inj₂; isInj₁; isInj₂)
open import Data.List     using (List; []; _∷_; [_]; _++_; length; filter; boolFilter)
open import Data.Fin      using (Fin; fromℕ)
  renaming (zero to 0ᶠ; suc to sucᶠ; _≟_ to _≟ᶠ_)
open import Data.String  hiding (_++_)
  renaming (length to lengthₛ)

open import Data.List.All using (All)
  renaming ([] to ∀[]; _∷_ to _∀∷_)
open import Data.List.Any using (Any)
open import Data.List.Properties using (++-identityʳ)

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋; True; False; toWitness; fromWitness)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary using (Decidable)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; decSetoid; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

open import Category.Functor using (RawFunctor)
open import Data.List.Categorical renaming (functor to listFunctor)
open RawFunctor {0ℓ} listFunctor using (_<$>_)

open import Data.List.Relation.Pointwise using (decidable)

module Semantics
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))
  where

open import Utilities.Lists
open import Types Participant _≟ₚ_ Honest
open import BitML Participant _≟ₚ_ Honest hiding (_≟ᶜˢ_)

open SETₙ  using ()
  renaming ( _∈_ to _∈ₙ_; _∉?_ to _∉?ₙ_; _∈?_ to _∈?ₙ_ ; _⊆_ to _⊆ₙ_ ; _≟ₗ_ to _≟ₙₛ_ )
open SETₚ  using ()
  renaming (_∈_ to _∈ₚ_; _∉?_ to _∉?ₚ_; _∈?_ to _∈?ₚ_ ; _⊆_ to _⊆ₚ_ ; _≟ₗ_ to _≟ₚₛ_)
open SETₑ using ()
  renaming ( _∈_ to _∈ₑ_; _∉?_ to _∉?ₑ_; _∈?_ to _∈?ₑ_
           ; _⊆_ to _⊆ₑ_; _⊆?_ to _⊆?ₑ_; sound-⊆ to sound-⊆ₑ
           ; _≟ₗ_ to _≟ₑₛ_
           )
open SETₑᵣ using ()
  renaming (_∈_ to _∈ₑᵣ_; _∉?_ to _∉?ₑᵣ_; _∈?_ to _∈?ₑᵣ_ ; _⊆_ to _⊆ₑᵣ_ ; _≟ₗ_ to _≟ₑᵣₛ_)
open SETₛ  using ()
  renaming (_∈_ to _∈ₛ_; _∉?_ to _∉?ₛ_; _∈?_ to _∈?ₛ_ ; _⊆_ to _⊆ₛ_ ; _≟ₗ_ to _≟ₛₛ_)
open SETᶜ  using ()
  renaming (_∈_ to _∈ᶜ_; _∉?_ to _∉?ᶜ_; _∈?_ to _∈?ᶜ_ ; _⊆_ to _⊆ᶜ_ ; _≟ₗ_ to _≟ᶜˢ_)
open SETₐ  using ()
  renaming ( _∈_ to _∈ₐ_; _∉?_ to _∉?ₐ_; _∈?_ to _∈?ₐ_
           ; _⊆_ to _⊆ₐ_; _⊆?_ to _⊆?ₐ_; sound-⊆ to sound-⊆ₐ; head⊆ to head⊆ₐ
           ; _≟ₗ_ to _≟ₐₛ_
           )

-------------------------------------------------------------------
-- Actions.

AdvertisedContracts : Set
AdvertisedContracts = List (∃[ v ] ∃[ vsᶜ ] ∃[ vsᵍ ] Advertisement v vsᶜ vsᵍ)

ActiveContracts : Set
ActiveContracts = List (∃[ v ] ∃[ vs ] Contracts v vs)

data Action (p : Participant) -- the participant that authorises this action
  : Values              -- the deposits it requires from this participant
  → Deposits            -- the deposits it produces
  → AdvertisedContracts -- the contract advertisments it requires
  → Set where

  -- commit secrets to stipulate {G}C
  ♯▷_ : ∀ {v vsᶜ vsᵍ} → (ad : Advertisement v vsᶜ vsᵍ)
      → Action p [] [] [ v , vsᶜ , vsᵍ , ad ]

  -- spend x to stipulate {G}C
  _▷ˢ_ : ∀ {v vsᶜ vsᵍ}
       → (ad : Advertisement v vsᶜ vsᵍ)
       → (i : Index vsᵍ)
       -- → .{p₁ : True (vs ≟ₙₛ [ vsᵍ ‼ i ])}
       → Action p [ vsᵍ ‼ i ] [] [ v , vsᶜ , vsᵍ , ad ]

  -- take branch (extend to inherently-typed using Γ)
  _▷ᵇ_ : ∀ {v vs vs′ vsᶜ vsᵍ}
    → (ad : Advertisement v vsᶜ vsᵍ)
    → (i : Index (C ad))
    → Action p vs vs′ [ v , vsᶜ , vsᵍ , ad ]

  -- join deposits
  _↔_ : ∀ {vs}
    → (x : Index vs)
    → (y : Index vs)
    → .{p₁ : False (x ≟ᶠ y)}
    -- → .{p₂ : ds ≡ ((p has_) <$> vs at x ⟨ (vs ‼ x) + (vs ‼ y) ⟩remove y)}
    → Action p vs ((p has_) <$> vs at x ⟨ (vs ‼ x) + (vs ‼ y) ⟩remove y) []

  -- divide a deposit
  _▷_,_ : ∀ {vs}
    → (i : Index vs)
    → (v₁ : Value)
    → (v₂ : Value)
    → .{p₁ : True ((vs ‼ i) ≟ (v₁ + v₂))}
    -- → .{p₂ : True (ds ≟ₑₛ ((p has_) <$> (vs at i ⟨ v₁ ⟩ ++ [ v₂ ])))}
    → Action p vs ((p has_) <$> (vs at i ⟨ v₁ ⟩ ++ [ v₂ ])) []

  -- donate deposit to participant
  _▷ᵈ_ : ∀ {vs}
      → (i : Index vs)
      → (p′ : Participant)
      -- → .{pr : True (_ ≟ₑₛ [ p′ has (vs ‼ i) ])}
      → Action p vs [ p′ has (vs ‼ i) ] []

  -- destroy deposit
  -- _♯_▷_ : {!!}

module ActionExamples where

  open AdvertisementExample

  -- donate
  _ : Action A (0 ∷ 10 ∷ 20 ∷ []) [ B has 10 ] []
  _ = sucᶠ 0ᶠ ▷ᵈ B

  -- divide
  _ : Action A [ 100 ] (A has 33 ∷ A has 67 ∷ []) []
  _ = 0ᶠ ▷ 33 , 67

  -- join
  _ : Action A (33 ∷ 67 ∷ []) [ A has 100 ] []
  _ = 0ᶠ ↔ sucᶠ 0ᶠ

  -- secret
  _ : Action A [] [] [ 5 , [ 100 ] , 200 ∷ 100 ∷ [] , ex-ad ]
  _ = ♯▷ ex-ad

  -- spend
  _ : Action A [ 100 ] [] [ 5 , [ 100 ] , 200 ∷ 100 ∷ [] , ex-ad ]
  _ = ex-ad ▷ˢ sucᶠ 0ᶠ

  -- take branch
  _ : ∀ {ds} → Action A [ 100 ] ds [ 5 , [ 100 ] , 200 ∷ 100 ∷ [] , ex-ad ]
  _ = ex-ad ▷ᵇ 0ᶠ

-------------------------------------------------------------------
-- Configurations.

data Configuration′ :
    AdvertisedContracts -- the current advertised contracts
  → ActiveContracts     -- the current active (stipulated) contracts
  → Deposits            -- the current owned deposits
  → AdvertisedContracts -- the ads required
  → Deposits            -- the deposits required
  → Set where

  -- empty
  ∅ᶜ : Configuration′ [] [] [] [] []

  -- contract advertisement
  `_ : ∀ {v vsᶜ vsᵍ} → (ad : Advertisement v vsᶜ vsᵍ)
     → Configuration′ [ v , vsᶜ , vsᵍ , ad ] [] [] [] []

  -- active contract
  ⟨_,_⟩ᶜ : ∀ {v vs}
         → (c : Contracts v vs)
         → (v′ : Value)
         -- → .{pr : True (v ≟ v′)}
         → Configuration′ [] [ v , vs , c ] [] [] []

  -- deposit redeemable by a participant
  ⟨_,_⟩ᵈ : (p : Participant)
         → (v : Value)
         → Configuration′ [] [] [ p has v ] [] []

  -- authorization to perform an action
  _auth[_] : ∀ {vs vs′ ads}
           → (p : Participant)
           → Action p vs vs′ ads
           → Configuration′ [] [] vs′ ads ((p has_) <$> vs)

  -- committed secret
  ⟨_∶_♯_⟩ : Participant
          → (s : Secret)
          → (n : ℕ ⊎ ⊥)
          → .{pr : maybe′ (True ∘ (lengthₛ s ≟_)) ⊤ (isInj₁ n)}
          → Configuration′ [] [] [] [] []

  -- revealed secret
  _∶_♯_ : Participant
        → (s : Secret)
        → (n : ℕ)
        → .{pr : True (lengthₛ s ≟ n)}
        → Configuration′ [] [] [] [] []

  -- parallel composition
  _∣∣_∶-_ : ∀ {adsˡ csˡ dsˡ adsʳ csʳ dsʳ rads rds ads cs ds}
          → Configuration′ adsˡ csˡ dsˡ [] []
          → Configuration′ adsʳ csʳ dsʳ rads rds
          → .( rads ⊆ₐ adsˡ
             × rds ⊆ₑ dsˡ
             × ads ≡ filter (_∉?ₐ rads) adsˡ ++ adsʳ
             × cs ≡ csˡ ++ csʳ
             × ds ≡ filter (_∉?ₑ rds) dsˡ ++ dsʳ)
          → Configuration′ ads cs ds [] []

-- "Closed" configurations.
Configuration : AdvertisedContracts → ActiveContracts → Deposits → Set
Configuration ads cs ds = Configuration′ ads cs ds [] []

-- Implicit-proof operators for configurations.
infixl 0 _∣∣_∶-_
-- infixl 5 _∣∣_
-- _∣∣_ : ∀ {adsˡ csˡ dsˡ adsʳ csʳ dsʳ rads rds ads cs ds}
--     → Configuration adsˡ csˡ dsˡ
--     → Configuration′ adsʳ csʳ dsʳ rads rds
--     → .{p₁ : rads ⊆?ₐ adsˡ}
--     → .{p₂ : rds  ⊆?ₑ dsˡ}
--     → .{p₃ : True (ads ≟ₐₛ filter (_∉?ₐ rads) adsˡ ++ adsʳ)}
--     → .{p₄ : True (cs ≟ᶜˢ csˡ ++ csʳ)}
--     → .{p₅ : True (ds ≟ₑₛ filter (_∉?ₑ rds) dsˡ ++ dsʳ)}
--     → Configuration ads cs ds
-- (c₁ ∣∣ c₂) {p₁} {p₂} {p₃} {p₄} {p₅} =
--   c₁ ∣∣ c₂
--   ∶- {!!} & {!!} & toWitness p₃ & toWitness p₄ & toWitness p₅

isInitial : ∀ {ads cs ds rads rds} → Configuration′ ads cs ds rads rds → Bool
isInitial (⟨ _ , _ ⟩ᵈ)    = true
isInitial (c₁ ∣∣ c₂ ∶- _) = isInitial c₁ ∧ isInitial c₂
isInitial _               = false

Initial : ∀ {ads cs ds rads rds} → Configuration′ ads cs ds rads rds → Set
Initial = T ∘ isInitial

depositsᶜ : ∀ {ads cs ds} → Configuration ads cs ds → List Deposit
depositsᶜ {_} {_} {ds} _ = ds

committedSecrets : ∀ {ads cs ds rads rds}
                 → Configuration′ ads cs ds rads rds
                 → List (Participant × Secret × (ℕ ⊎ ⊥))
committedSecrets ⟨ x ∶ s ♯ n ⟩ =  [  x , s , n ]
committedSecrets (l ∣∣ r ∶- _) = committedSecrets l ++ committedSecrets r
committedSecrets _ = []

committedParticipants : ∀ {v vsᶜ vsᵍ} {ads cs ds rads rds}
                      → Configuration′ ads cs ds rads rds
                      → Advertisement v vsᶜ vsᵍ
                      → List Participant
committedParticipants {v} {vsᶜ} {vsᵍ} (p auth[ (♯▷_ {v′} {vsᶜ′} {vsᵍ′} ad′) ]) ad
  with (v , vsᶜ , vsᵍ , ad) ∃≟ₐ (v′ , vsᶜ′ , vsᵍ′ , ad′)
... | yes _ = [ p ]
... | no  _ = []
committedParticipants (l ∣∣ r ∶- _) ad = committedParticipants l ad
                                      ++ committedParticipants r ad
committedParticipants _ _ = []

spentForStipulation : ∀ {v vsᶜ vsᵍ} {ads cs ds rads rds}
                    → Configuration′ ads cs ds rads rds
                    → Advertisement v vsᶜ vsᵍ
                    → List (Participant × Value)
spentForStipulation {v} {vsᶜ} {vsᵍ}
                    (p auth[ (_▷ˢ_ {v′} {vsᶜ′} {vsᵍ′} ad′ iᵍ) ]) ad
  with (v , vsᶜ , vsᵍ , ad) ∃≟ₐ (v′ , vsᶜ′ , vsᵍ′ , ad′)
... | yes _ = [ p , (vsᵍ′ ‼ iᵍ) ]
... | no  _ = []
spentForStipulation (l ∣∣ r ∶- _) ad = spentForStipulation l ad
                                    ++ spentForStipulation r ad
spentForStipulation _ _ = []

module ConfigurationExamples where
  open AdvertisementExample

  ex-cs : ∃[ v ] ∃[ vs ] Contracts v vs
  ex-cs = Contracts∃ 1  ←v
                     [] ←vs
                     [ withdraw A ]

  -- empty
  _ : Configuration [] [] []
  _ = ∅ᶜ

  -- advertisements
  _ : Configuration [ 5 , [ 100 ] , 200 ∷ 100 ∷ [] , ex-ad ] [] []
  _ = ` ex-ad

  -- active contracts
  _ : Configuration [] [ 1 , [] , [ withdraw A ] ] []
  _ = ⟨ ex-contracts₁ , 1 ⟩ᶜ

  -- deposits
  _ : Configuration [] [] (A has 4 ∷ [ A has 6 ])
  _ = ⟨ A , 4 ⟩ᵈ ∣∣ ⟨ A , 6 ⟩ᵈ
      ∶- (λ {x} z → z) & (λ ()) & refl & refl & refl

  -- authorized actions
  -- 1. donate
  _ : ∀ {v} → Configuration′ [] [] [ B has v ] [] [ A has v ]
  _ = A auth[ 0ᶠ ▷ᵈ B ]
  -- 2. divide
  _ : Configuration′ [] [] (A has 33 ∷ A has 67 ∷ []) [] [ A has 100 ]
  _ = A auth[ 0ᶠ ▷ 33 , 67 ]
  -- 3. join
  _ : Configuration′ [] [] [ A has 100 ] [] (A has 33 ∷ A has 67 ∷ [])
  _ = A auth[ 0ᶠ ↔ sucᶠ 0ᶠ ]
  -- 4. secret
  _ : Configuration′ [] [] [] [ 5 , [ 100 ] , 200 ∷ 100 ∷ [] , ex-ad ] []
  _ = A auth[ ♯▷ ex-ad ]
  -- 5. spend
  _ : Configuration′ [] [] [] [ 5 , [ 100 ] , 200 ∷ 100 ∷ [] , ex-ad ] [ A has 200 ]
  _ = A auth[ ex-ad ▷ˢ 0ᶠ ]
  -- 6. take branch
  _ : Configuration′ [] [] [] [ 5 , [ 100 ] , 200 ∷ 100 ∷ [] , ex-ad ] []
  _ = A auth[ ex-ad ▷ᵇ 0ᶠ ]
  -- 7. combination
  Γ₁ : Configuration [ 5 , [ 100 ] , 200 ∷ 100 ∷ [] , ex-ad ]
                     [ 1 , [] , [ withdraw A ] ]
                     []
  Γ₁ = ` ex-ad ∣∣ ⟨ ex-contracts₁ , 1 ⟩ᶜ
       ∶- (λ ()) & (λ {x} z → z) & refl & refl & refl

  Γ₂ : Configuration [ 5 , [ 100 ] , 200 ∷ 100 ∷ [] , ex-ad ]
                     [ 1 , [] , [ withdraw A ] ]
                     [ A has 40 ]
  Γ₂ = Γ₁ ∣∣ ⟨ A , 40 ⟩ᵈ
       ∶- (λ ()) & (λ {x} z → z) & refl & refl & refl

  Γ₃ : Configuration [ 5 , [ 100 ] , 200 ∷ 100 ∷ [] , ex-ad ]
                     [ 1 , [] , [ withdraw A ] ]
                     (A has 40 ∷ A has 60 ∷ [])
  Γ₃ = Γ₂ ∣∣ ⟨ A , 60 ⟩ᵈ
       ∶- (λ ()) & (λ {x} ()) & refl & refl & refl

  Γ₄ : Configuration [ 5 , [ 100 ] , 200 ∷ 100 ∷ [] , ex-ad ]
                     [ 1 , [] , [ withdraw A ] ]
                     [ A has 100 ]
  Γ₄ = Γ₃ ∣∣ A auth[ _↔_ {A} {40 ∷ 60 ∷ []} 0ᶠ (sucᶠ 0ᶠ) ]
       ∶- (λ ()) & (λ {x} z → z) & refl & refl & {!!}


  Γ₅ : Configuration [ 5 , [ 100 ] , 200 ∷ 100 ∷ [] , ex-ad ]
                     [ 1 , [] , [ withdraw A ] ]
                     []
  Γ₅ = Γ₄ ∣∣ A auth[ ex-ad ▷ˢ sucᶠ 0ᶠ ]
       ∶- (λ {x} z → z) & (λ {x} z → z) & {!!} & refl & {!!}


  -- secrets
  _ : Configuration [] [] []
  _ = A ∶ "qwerty" ♯ 6

  _ : Configuration [] [] []
  _ = ⟨ A ∶ "qwerty" ♯ inj₁ 6 ⟩

  _ : Configuration [] [] []
  _ = ⟨ A ∶ "qwerty" ♯ inj₂ impossible ⟩
    where postulate impossible : ⊥

infix -1 _—→_
data _—→_ :
  ∀ {ads cs ds ads′ cs′ ds′}
  → Configuration ads cs ds
  → Configuration ads′ cs′ ds′
  → Set where

  -- i) Rules for deposits
  [DEP-AuthJoin] :
    ∀ {A : Participant}
      {v v′ : Value}
      {ads cs ds} {Γ : Configuration ads cs ds}

      ----------------------------------------------------------------------------------
    → Configuration ads cs (A has v ∷ A has v′ ∷ ds) ∋
      (  ⟨ A , v ⟩ᵈ
      ∣∣ ⟨ A , v′ ⟩ᵈ ∶- (λ {x} z → z) & (λ ()) & refl & refl & refl
      ∣∣ Γ           ∶- (λ {x} z → z) & (λ ()) & refl & refl & refl
      )
      —→
      Configuration ads cs (A has (v + v′) ∷ ds) ∋
      (  ⟨ A , v ⟩ᵈ
      ∣∣ ⟨ A , v′ ⟩ᵈ            ∶- (λ {x} z → z) & (λ ()) & refl & refl & refl
      ∣∣ A auth[ 0ᶠ ↔ sucᶠ 0ᶠ ] ∶- (λ {x} z → z) & (λ {x} z → z) & refl & refl & refl
      ∣∣ Γ                      ∶- (λ {x} z → z) & (λ ()) & refl & refl & {!!}
      )


  [DEP-Join] :
    ∀ {A : Participant}
      {v v′ : Value}
      {ads cs ds} {Γ : Configuration ads cs ds}

      --------------------------------------------------------------------------------
    → Configuration ads cs (A has (v + v′) ∷ ds) ∋
      (  ⟨ A , v ⟩ᵈ
      ∣∣ ⟨ A , v′ ⟩ᵈ            ∶- (λ {x} z → z) & (λ ()) & refl & refl & refl
      ∣∣ A auth[ 0ᶠ ↔ sucᶠ 0ᶠ ] ∶- (λ {x} z → z) & (λ {x} z → z) & refl & refl & refl
      ∣∣ Γ                      ∶- (λ {x} z → z) & (λ ()) & refl & refl & {!!}
      )
      —→
      Configuration ads cs (A has (v + v′) ∷ ds) ∋
      (  ⟨ A , v + v′ ⟩ᵈ
      ∣∣ Γ ∶- (λ {x} z → z) & (λ ()) & refl & refl & refl
      )

  [DEP-AuthDivide] :
    ∀ {A : Participant}
      {v v′ : Value}
      {ads cs ds} {Γ : Configuration ads cs ds}

      ----------------------------------------------------------------
    → Configuration ads cs (A has (v + v′) ∷ ds) ∋
      (  ⟨ A , v + v′ ⟩ᵈ
      ∣∣ Γ
      ∶- (λ {x} z → z) & (λ ()) & refl & refl & refl
      )
      —→
      Configuration [] [] (A has v ∷ A has v′ ∷ []) ∋
      (  ⟨ A , v + v′ ⟩ᵈ
      ∣∣ A auth[ _▷_,_ {A} {[ v + v′ ]} 0ᶠ v v′ {fromWitness refl} ]
      ∶- (λ {x} z → z) & (λ {x} z → z) & refl & refl & {!!}
      )
      ∣∣ Γ
      ∶- (λ {x} z → z) & (λ ()) & refl & refl & refl


  [DEP-DIVIDE] :
    ∀ {A : Participant}
      {v v′ : Value}
      {ads cs ds} {Γ : Configuration ads cs ds}

      -----------------------------------------------------------------
    → Configuration ads cs (A has v ∷ A has v′ ∷ ds) ∋
      (  Configuration [] [] (A has v ∷ A has v′ ∷ []) ∋
      (  ⟨ A , v + v′ ⟩ᵈ
      ∣∣ A auth[ _▷_,_ {A} {[ v + v′ ]} 0ᶠ v v′ {fromWitness refl} ]
      ∶- (λ {x} z → z) & (λ {x} z → z) & refl & refl & {!!}
      )
      ∣∣ Γ
      ∶- (λ {x} z → z) & (λ ()) & refl & refl & refl
      )
      —→
      Configuration ads cs (A has v ∷ A has v′ ∷ ds) ∋
      (  ⟨ A , v ⟩ᵈ
      ∣∣ ⟨ A , v′ ⟩ᵈ ∶- (λ {x} z → z) & (λ ()) & refl & refl & refl
      ∣∣ Γ           ∶- (λ {x} z → z) & (λ ()) & refl & refl & refl
      )

  [DEP-AuthDonate] :
    ∀ {A B : Participant}
      {v : Value}
      {ads cs ds} {Γ : Configuration ads cs ds}

      ---------------------------------------------------------------------
    → Configuration ads cs (A has v ∷ ds) ∋
      (  ⟨ A , v ⟩ᵈ
      ∣∣ Γ
      ∶- (λ {x} z → z) & (λ ()) & refl & refl & refl
      )
      —→
      Configuration ads cs (B has v ∷ ds) ∋
      (  Configuration [] [] [ B has v ] ∋
      (  ⟨ A , v ⟩ᵈ
      ∣∣ A auth[ _▷ᵈ_ {A} {[ v ]} 0ᶠ B ]
      ∶- (λ {x} z → z) & (λ {x} z → z) & refl & refl & {!!}
      )
      ∣∣ Γ
      ∶- (λ {x} z → z) & (λ ()) & refl & refl & refl
      )

  [DEP-Donate] :
    ∀ {A B : Participant}
      {v : Value}
      {ads cs ds} {Γ : Configuration ads cs ds}

      -----------------------------------------------------------
    → Configuration ads cs (B has v ∷ ds) ∋
      ( Configuration [] [] [ B has v ] ∋
      (  ⟨ A , v ⟩ᵈ
      ∣∣ A auth[ _▷ᵈ_ {A} {[ v ]} 0ᶠ B ]
      ∶- (λ {x} z → z) & (λ {x} z → z) & refl & refl & {!!}
      )
      ∣∣ Γ
      ∶- (λ {x} z → z) & (λ ()) & refl & refl & refl
      )
      —→
      Configuration ads cs (B has v ∷ ds) ∋
      ( ⟨ B , v ⟩ᵈ
      ∣∣ Γ
      ∶- (λ {x} z → z) & (λ ()) & refl & refl & refl
      )

  -- [DEP-AuthDestroy]
  -- [DEP-Destroy]

  -- ii) Rules for contract advertisements and stipulation

  [C-Advertise] :
    ∀ {A : Participant}
      {v vsᶜ vsᵍ} {ad : Advertisement v vsᶜ vsᵍ}
      {ads cs ds} {Γ : Configuration ads cs ds}

    → ∃[ p ] (p ∈ₚ participantsᵍ (G ad) → p ∈ₚ Hon)
    → (∀ d → d ∈ₑ depositsᵃ ad → deposit d ∈ₑ depositsᶜ Γ)
      ------------------------------------------------------------------------
    → Γ
      —→
      Configuration ((v , vsᶜ , vsᵍ , ad) ∷ ads) cs ds ∋
      (  ` ad
      ∣∣ Γ
      ∶- (λ ()) & (λ {x} z → z) & refl & refl & refl
      )

  [C-AuthCommit] :
    ∀ {A : Participant}
      {v vsᶜ vsᵍ} {ad : Advertisement v vsᶜ vsᵍ}
      {ads cs ds} {Γ : Configuration ads cs ds}
      {Δ : Configuration [] [] []}

      -- 1. Δ contains commits from A's secrets in G
      -- 2. only dishonest participants can commit to invalid lengths ⊥
    → All (λ s →
        ∃[ n ] ( Any (λ {(p , s′ , n′) → p ≡ A × s ≡ s′ × n ≡ n′})
                     (committedSecrets Δ)
               × (A ∈ₚ Hon → (isInj₂ n ≡ nothing)))
               )
        (secretsᵖ A (G ad))
      -----------------------------------------------------------------------
    → Configuration ((v , vsᶜ , vsᵍ , ad) ∷ ads) cs ds ∋
      (  ` ad
      ∣∣ Γ
      ∶- (λ ()) & (λ {x} z → z) & refl & refl & refl
      )
      —→
      Configuration ads cs ds ∋
      (  Configuration ((v , vsᶜ , vsᵍ , ad) ∷ ads) cs ds ∋
      (  ` ad
      ∣∣ Γ
      ∶- (λ ()) & (λ {x} z → z) & refl & refl & refl
      ∣∣ Δ
      ∶- (λ ()) & (λ ()) & {!!} & sym (++-identityʳ cs) & {!!}
      )
      ∣∣ A auth[ ♯▷ ad ]
      ∶- {!!} & (λ ()) & {!!} & {!!} & {!!}
      )

  [C-AuthInit] :
    ∀ {A : Participant}
      {v vsᶜ vsᵍ} {ad : Advertisement v vsᶜ vsᵍ}
      {iᵍ : Index vsᵍ}
      {ads cs dsˡ dsʳ ds} {Γ : Configuration ads cs ds}
      {p : ds ≡ dsˡ ++ [ A has (vsᵍ ‼ iᵍ) ] ++ dsʳ}

      -- all participants have committed their secrets
    → All (λ p → p ∈ₚ committedParticipants Γ ad) (participantsᵍ (G ad))
      -------------------------------------------------------------------
    → Configuration ((v , vsᶜ , vsᵍ , ad) ∷ ads) cs ds ∋
      (  ` ad
      ∣∣ Γ
      ∶- (λ ()) & (λ {x} z → z) & refl & refl & refl
      )
      —→
      Configuration ads cs (dsˡ ++ dsʳ) ∋
      (  ` ad
      ∣∣ Γ
      ∶- (λ ()) & (λ {x} z → z) & refl & refl & refl
      ∣∣ A auth[ ad ▷ˢ iᵍ ]
      ∶- {!!} & {!!} & {!!} & sym (++-identityʳ cs) & {!!}
      )

  [C-Init] :
    ∀ {v vsᶜ vsᵍ} {ad : Advertisement v vsᶜ vsᵍ}
      {ads cs ds} {Γ : Configuration ads cs ds}
      {Δ : Configuration′ [] [] [] [ v , vsᶜ , vsᵍ , ad ] []}

      -- all participants have committed their secrets
    → All (λ p → p ∈ₚ committedParticipants Δ ad) (participantsᵍ (G ad))

      -- all participants have spent the required (persistent) deposits for stipulation
    → toStipulate (G ad) ≡ spentForStipulation Δ ad

      ----------------------------------------------------------------------

    → Configuration ads cs ds ∋
      (  Configuration ((v , vsᶜ , vsᵍ , ad) ∷ ads) cs ds ∋
      (  ` ad
      ∣∣ Γ
      ∶- (λ ()) & (λ {x} z → z) & refl & refl & refl
      )
      ∣∣ Δ
      ∶- {!!} & (λ ()) & {!!} & sym (++-identityʳ cs) & {!!}
      )
      —→
      Configuration ads ((v , vsᶜ , C ad) ∷ cs) ds ∋
      (  ⟨ C ad , v ⟩ᶜ
      ∣∣ Γ
      ∶- (λ ()) & (λ ()) & refl & refl & refl
      )

  -- iii) Rules for executing active contracts

  -- [C-Split]
  -- [C-AuthRev]
  -- [C-PutRev]
  -- [C-Withdraw]
  -- [C-AuthControl]
  -- [C-Control]

  -- iv) Rules for handling time

  -- [Action]
  -- [Delay]
  -- [Timeout]
