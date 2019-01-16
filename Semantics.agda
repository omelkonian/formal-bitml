open import Level        using (0ℓ)
open import Function     using (_on_; const; _∘_; id; _∋_; _$_)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Bool    using (T; Bool; true; false; _∧_)
open import Data.Maybe   using (Maybe; just; nothing; maybe′)
open import Data.Nat     using (ℕ; suc; _+_; _≤_; _>_; _≟_)
open import Data.Product using (∃; ∃-syntax; Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂; isInj₁; isInj₂)
open import Data.Fin     using (Fin; fromℕ)
  renaming (zero to 0ᶠ; suc to sucᶠ; _≟_ to _≟ᶠ_)
open import Data.String  hiding (_++_)
  renaming (length to lengthₛ)

open import Data.List using (List; []; _∷_; [_]; _++_; map; length; filter; boolFilter)
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

open import Utilities.Lists hiding (Σ-sum-syntax)
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
  renaming ( _∈_ to _∈ᶜ_; _∉?_ to _∉?ᶜ_; _∈?_ to _∈?ᶜ_
           ; _⊆_ to _⊆ᶜ_; _⊆?_ to _⊆?ᶜ_; sound-⊆ to sound-⊆ᶜ
           ; _≟ₗ_ to _≟ᶜˢ_
           )
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
       → (i : Index vsᵍ) -- T0D0 better indexing
       -- → .{p₁ : True (vs ≟ₙₛ [ vsᵍ ‼ i ])}
       → Action p [ v , vsᶜ , vsᵍ , ad ] [] [ vsᵍ ‼ i ] []

  -- take branch
  _▷ᵇ_ : ∀ {v vs}
      → (c : Contracts v vs)
      → (i : Index c)
      → Action p [] [ v , vs , c ] [] []

  -- join deposits
  _↔_ : ∀ {vs : Values}
      → (x : Index vs)
      → (y : Index vs)
      → .{p₁ : False (x ≟ᶠ y)}
      -- → .{p₂ : ds ≡ ((p has_) <$> vs at x ⟨ (vs ‼ x) + (vs ‼ y) ⟩remove y)}
      → Action p [] [] vs ((p has_) <$> vs at x ⟨ (vs ‼ x) + (vs ‼ y) ⟩remove y)

  -- divide a deposit
  _▷_,_ : ∀ {vs : Values}
    → (i : Index vs)
    → (v₁ : Value)
    → (v₂ : Value)
    → .{p₁ : True ((vs ‼ i) ≟ (v₁ + v₂))}
    -- → .{p₂ : True (ds ≟ₑₛ ((p has_) <$> (vs at i ⟨ v₁ ⟩ ++ [ v₂ ])))}
    → Action p [] [] vs ((p has_) <$> (vs at i ⟨ v₁ ⟩ ++ [ v₂ ]))

  -- donate deposit to participant
  _▷ᵈ_ : ∀ {vs : Values}
      → (i : Index vs)
      → (p′ : Participant)
      -- → .{pr : True (_ ≟ₑₛ [ p′ has (vs ‼ i) ])}
      → Action p [] [] vs [ p′ has (vs ‼ i) ]

  -- destroy deposit
  destroy : ∀ {vs : Values}
        → (i : Index vs)
        -- → .{pr : participant (vs ‼ i) ≡ A}
        → Action p [] [] vs (p has_ <$> remove vs i)


module ActionExamples where

  open AdvertisementExample

  -- donate
  _ : Action A [] [] (0 ∷ 10 ∷ 20 ∷ []) [ B has 10 ]
  _ = sucᶠ 0ᶠ ▷ᵈ B

  -- divide
  _ : Action A [] [] [ 100 ] (A has 33 ∷ A has 67 ∷ [])
  _ = 0ᶠ ▷ 33 , 67

  -- join
  _ : Action A [] [] (33 ∷ 67 ∷ []) [ A has 100 ]
  _ = 0ᶠ ↔ sucᶠ 0ᶠ

  -- secret
  _ : Action A [ 5 , [ 100 ] , 200 ∷ 100 ∷ [] , ex-ad ] [] [] []
  _ = ♯▷ ex-ad

  -- spend
  _ : Action A [ 5 , [ 100 ] , 200 ∷ 100 ∷ [] , ex-ad ] [] [ 100 ] []
  _ = ex-ad ▷ˢ sucᶠ 0ᶠ

  -- take branch
  _ : Action A [] [ 5 , [ 100 ] , ex-contracts₃ ] [] []
  _ = ex-contracts₃ ▷ᵇ 0ᶠ

  -- destroy
  _ : Action A [] [] [ 100 ] []
  _ = destroy 0ᶠ

-------------------------------------------------------------------
-- Configurations.

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
  _auth[_] : ∀ {ads cs vs ds}
           → (p : Participant)
           → Action p ads cs vs ds
           → Configuration′ ([] , ads) ([] , cs) (ds , ((p has_) <$> vs))

  -- committed secret
  ⟨_∶_♯_⟩ : Participant
          → (s : Secret)
          → (n : ℕ ⊎ ⊥)
          → {pr : (∃[ n′ ] ((n ≡ inj₁ n′) × True (lengthₛ s ≟ n′)))
                ⊎ (∃[ x ] (n ≡ inj₂ x)) }
          → Configuration′ ([] , []) ([] , []) ([] , [])

  -- revealed secret
  _∶_♯_ : Participant
        → (s : Secret)
        → (n : ℕ)
        → .{pr : True (lengthₛ s ≟ n)}
        → Configuration′ ([] , []) ([] , []) ([] , [])

  -- parallel composition
  _∣∣_∶-_ : ∀ {adsˡ csˡ dsˡ adsʳ csʳ dsʳ rads rcs rds ads cs ds}
          → Configuration′ ( adsˡ , []  ) ( csˡ , [] ) (dsˡ , [] )
          → Configuration′ ( adsʳ , rads) ( csʳ , rcs) (dsʳ , rds)
          → .( rads ⊆ₐ adsˡ
             × rcs  ⊆ᶜ csˡ
             × rds  ⊆ₑ dsˡ
             × ads ≡ adsˡ ++ adsʳ
             × cs  ≡ csˡ  ++ csʳ
             × ds  ≡ filter (_∉?ₑ rds) dsˡ ++ dsʳ
             )
          → Configuration′ (ads , []) (cs , []) (ds , [])

-- "Closed" configurations; they stand on their own.
Configuration : AdvertisedContracts → ActiveContracts → Deposits → Set
Configuration ads cs ds = Configuration′ (ads , []) (cs , []) (ds , [])

-- Implicit-proof operators for configurations.
infixl 0 _∣∣_∶-_
infixl 5 _∣∣_
_∣∣_ : ∀ {adsˡ csˡ dsˡ adsʳ csʳ dsʳ rads rcs rds ads cs ds}
    → Configuration′ ( adsˡ , []  ) ( csˡ , [] ) (dsˡ , [] )
    → Configuration′ ( adsʳ , rads) ( csʳ , rcs) (dsʳ , rds)
    → .{p₁ : rads ⊆?ₐ adsˡ}
    → .{p₂ : rcs  ⊆?ᶜ csˡ}
    → .{p₃ : rds  ⊆?ₑ dsˡ}
    → .{p₄ : True (ads ≟ₐₛ adsˡ ++ adsʳ)}
    → .{p₅ : True (cs  ≟ᶜˢ csˡ  ++ csʳ )}
    → .{p₆ : True (ds  ≟ₑₛ filter (_∉?ₑ rds ) dsˡ ++ dsʳ)}
    → Configuration′ (ads , []) (cs , []) (ds , [])
(c₁ ∣∣ c₂) {p₁} {p₂} {p₃} {p₄} {p₅} {p₆} =
  c₁ ∣∣ c₂
  ∶- {!!} & {!!} & {!!} & toWitness p₄ & toWitness p₅ & toWitness p₆

isInitial : ∀ {ads cs ds rads rcs rds}
          → Configuration′ (ads , rads) (cs , rcs) (ds , rds)
          → Bool
isInitial (⟨ _ , _ ⟩ᵈ)    = true
isInitial (c₁ ∣∣ c₂ ∶- _) = isInitial c₁ ∧ isInitial c₂
isInitial _               = false

Initial : ∀ {ads cs ds rads rcs rds}
        → Configuration′ (ads , rads) (cs , rcs) (ds , rds)
        → Set
Initial = T ∘ isInitial

depositsᶜ : ∀ {ads cs ds rads rcs rds}
          → Configuration′ (ads , rads) (cs , rcs) (ds , rds)
          → List Deposit
depositsᶜ {_} {_} {ds} _ = ds

committedSecrets : ∀ {ads cs ds rads rcs rds}
                 → Configuration′ (ads , rads) (cs , rcs) (ds , rds)
                 → List (Participant × Secret × (ℕ ⊎ ⊥))
committedSecrets ⟨ x ∶ s ♯ n ⟩ =  [  x , s , n ]
committedSecrets (l ∣∣ r ∶- _) = committedSecrets l ++ committedSecrets r
committedSecrets _ = []

committedParticipants : ∀ {v vsᶜ vsᵍ} {ads cs ds rads rcs rds}
                      → Configuration′ (ads , rads) (cs , rcs) (ds , rds)
                      → Advertisement v vsᶜ vsᵍ
                      → List Participant
committedParticipants {v} {vsᶜ} {vsᵍ} (p auth[ (♯▷_ {v′} {vsᶜ′} {vsᵍ′} ad′) ]) ad
  with (v , vsᶜ , vsᵍ , ad) ∃≟ₐ (v′ , vsᶜ′ , vsᵍ′ , ad′)
... | yes _ = [ p ]
... | no  _ = []
committedParticipants (l ∣∣ r ∶- _) ad = committedParticipants l ad
                                      ++ committedParticipants r ad
committedParticipants _ _ = []

spentForStipulation : ∀ {v vsᶜ vsᵍ} {ads cs ds rads rcs rds}
                    → Configuration′ (ads , rads) (cs , rcs) (ds , rds)
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
  ex-cs = 1 , [] , [ withdraw A ]

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
      ∶- (λ {x} z → z) & (λ {x} z → z) & (λ ()) & refl & refl & refl

  -- authorized actions
  -- 1. donate
  _ : ∀ {v} → Configuration′ ([] , []) ([] , []) ([ B has v ] , [ A has v ])
  _ = A auth[ 0ᶠ ▷ᵈ B ]
  -- 2. divide
  _ : Configuration′ ([] , []) ([] , []) (A has 33 ∷ A has 67 ∷ [] , [ A has 100 ])
  _ = A auth[ 0ᶠ ▷ 33 , 67 ]
  -- 3. join
  _ : Configuration′ ([] , []) ([] , []) ([ A has 100 ] , A has 33 ∷ A has 67 ∷ [])
  _ = A auth[ 0ᶠ ↔ sucᶠ 0ᶠ ]
  -- 4. secret
  _ : Configuration′ ([] , [ 5 , [ 100 ] , 200 ∷ 100 ∷ [] , ex-ad ]) ([] , []) ([] , [])
  _ = A auth[ ♯▷ ex-ad ]
  -- 5. spend
  _ : Configuration′ ([] , [ 5 , [ 100 ] , 200 ∷ 100 ∷ [] , ex-ad ]) ([] , []) ([] , [ A has 200 ])
  _ = A auth[ ex-ad ▷ˢ 0ᶠ ]
  -- 6. take branch
  _ : Configuration′ ([] , []) ([] , [ 5 , [ 100 ] , ex-contracts₃ ]) ([] , [])
  _ = A auth[ ex-contracts₃ ▷ᵇ 0ᶠ ]
  -- 7. combination
  Γ₁ : Configuration [ 5 , [ 100 ] , 200 ∷ 100 ∷ [] , ex-ad ]
                     [ 1 , [] , [ withdraw A ] ]
                     []
  Γ₁ = ` ex-ad ∣∣ ⟨ ex-contracts₁ , 1 ⟩ᶜ
       ∶- (λ ()) & (λ {x} z → z) & (λ {x} z → z) & refl & refl & refl

  Γ₂ : Configuration [ 5 , [ 100 ] , 200 ∷ 100 ∷ [] , ex-ad ]
                     [ 1 , [] , [ withdraw A ] ]
                     [ A has 40 ]
  Γ₂ = Γ₁ ∣∣ ⟨ A , 40 ⟩ᵈ
       ∶- (λ ()) & (λ ()) & (λ {x} z → z) & refl & refl & refl

  Γ₃ : Configuration [ 5 , [ 100 ] , 200 ∷ 100 ∷ [] , ex-ad ]
                     [ 1 , [] , [ withdraw A ] ]
                     (A has 40 ∷ A has 60 ∷ [])
  Γ₃ = Γ₂ ∣∣ ⟨ A , 60 ⟩ᵈ
       ∶- (λ ()) & (λ ()) & (λ {x} ()) & refl & refl & refl

  Γ₄ : Configuration [ 5 , [ 100 ] , 200 ∷ 100 ∷ [] , ex-ad ]
                     [ 1 , [] , [ withdraw A ] ]
                     [ A has 100 ]
  Γ₄ = Γ₃ ∣∣ A auth[ _↔_ {A} {40 ∷ 60 ∷ []} 0ᶠ (sucᶠ 0ᶠ) ]
       ∶- (λ ()) & (λ ()) & (λ {x} z → z) & refl & refl & {!!}


  Γ₅ : Configuration [ 5 , [ 100 ] , 200 ∷ 100 ∷ [] , ex-ad ]
                     [ 1 , [] , [ withdraw A ] ]
                     []
  Γ₅ = Γ₄ ∣∣ A auth[ ex-ad ▷ˢ sucᶠ 0ᶠ ]
       ∶- (λ {x} z → z) & (λ ()) & (λ {x} z → z) & {!!} & refl & {!!}


  -- secrets
  _ : Configuration [] [] []
  _ = (A ∶ "qwerty" ♯ 6)

  _ : Configuration [] [] []
  _ = ⟨ A ∶ "qwerty" ♯ inj₁ 6 ⟩ {inj₁ (6 , refl , tt)}

  _ : Configuration [] [] []
  _ = ⟨ A ∶ "qwerty" ♯ inj₂ impossible ⟩ {inj₂ (impossible , refl)}
    where postulate impossible : ⊥

-------------------------------------------------------------------
-- Utilities for constructing configurations.

_∣∣ᶜˢ_ : ∀ {ads cs ds}
      → (cs′ : ActiveContracts)
      → Configuration ads cs ds
      → Configuration ads (cs′ ++ cs) ds
[]                  ∣∣ᶜˢ Γ = Γ
((v , vs , c) ∷ cs) ∣∣ᶜˢ Γ = ⟨ c , v ⟩ᶜ
                          ∣∣ (cs ∣∣ᶜˢ Γ)
                          ∶- (λ {x} z → z) & (λ ()) & (λ {x} z → z) & refl & refl & refl

_∣∣ᵈˢ_ : ∀ {ads cs ds}
      → (ds′ : Deposits)
      → Configuration ads cs ds
      → Configuration ads cs (ds′ ++ ds)
[]       ∣∣ᵈˢ Γ = Γ
(d ∷ ds) ∣∣ᵈˢ Γ = ⟨ participant d , value d ⟩ᵈ
               ∣∣ (ds ∣∣ᵈˢ Γ)
               ∶- (λ {x} z → z) & (λ {x} z → z) & (λ ()) & refl & refl & refl

ValidSecret : Set
ValidSecret = Participant × ∃[ s ] ∃[ n ] (lengthₛ s ≡ n)

_∣∣ˢˢ_ : ∀ {ads cs ds}
      → (ss : List ValidSecret)
      → Configuration ads cs ds
      → Configuration ads cs ds
[]                      ∣∣ˢˢ Γ = Γ
((p , s , n , pr) ∷ ss) ∣∣ˢˢ Γ = (p ∶ s ♯ n) {fromWitness pr}
                              ∣∣ (ss ∣∣ˢˢ Γ)
                              ∶- (λ {x} z → z) & (λ {x} z → z) & (λ {x} z → z) & refl & refl & refl

_∣∣ᵇ_ : ∀ {ads cs ds}
      → Configuration ads cs ds
      → ( Σ[ x ∈ Index cs ] (Index ((proj₂ ∘ proj₂) (cs ‼ x)) × List Participant)
        )
      → Configuration ads cs ds
_∣∣ᵇ_ {_} {cs} Γ (i , j , [])     = Γ
_∣∣ᵇ_ {_} {cs} Γ (i , j , p ∷ ps) = ( Γ
                                    ∣∣ p auth[ ((proj₂ ∘ proj₂) (cs ‼ i)) ▷ᵇ j ]
                                    ∶- (λ ()) & {!!} & (λ ()) & {!!} & {!!} & {!!}
                                    ) ∣∣ᵇ (i , j , ps)

casesToContracts : ContractCases → ActiveContracts
casesToContracts = map (λ{ (v , vs , c) → v , vs , [ c ] })

-------------------------------------------------------------------
-- Other utilities.

authDecorations : ∀ {v vs} → Contract v vs → List Participant
authDecorations (x       ∶ c) = x ∷ authDecorations c
authDecorations (after _ ∶ c) = authDecorations c
authDecorations _             = []

timeDecorations : ∀ {v vs} → Contract v vs → List Time
timeDecorations (_       ∶ c) = timeDecorations c
timeDecorations (after t ∶ c) = t ∷ timeDecorations c
timeDecorations _             = []

removeTopDecorations : ∀ {v vs} → Contract v vs → Contract v vs
removeTopDecorations (_       ∶ c) = removeTopDecorations c
removeTopDecorations (after _ ∶ c) = removeTopDecorations c
removeTopDecorations c             = c


-----------------------------------------------------------------------------------
-- Semantic rules for untimed configurations.

-- T0D0 [GENERALISE] single configurations inside list, instead of head
-- T0D0 Keep transition labels?

infix -1 _—→_
data _—→_ : ∀ {ads cs ds ads′ cs′ ds′}
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
      ∣∣ ⟨ A , v′ ⟩ᵈ ∶- (λ {x} z → z) & (λ {x} z → z) & (λ ()) & refl & refl & refl
      ∣∣ Γ           ∶- (λ {x} z → z) & (λ {x} z → z) & (λ ()) & refl & refl & refl
      )
      —→
      Configuration ads cs (A has (v + v′) ∷ ds) ∋
      (  ⟨ A , v ⟩ᵈ
      ∣∣ ⟨ A , v′ ⟩ᵈ
      ∶- (λ {x} z → z) & (λ {x} z → z) & (λ ()) & refl & refl & refl
      ∣∣ A auth[ 0ᶠ ↔ sucᶠ 0ᶠ ]
      ∶- (λ {x} z → z) & (λ {x} z → z) & (λ {x} z → z) & refl & refl & refl
      ∣∣ Γ
      ∶- (λ {x} z → z) & (λ {x} z → z) & (λ ()) & refl & refl & {!!}
      )


  [DEP-Join] :
    ∀ {A : Participant}
      {v v′ : Value}
      {ads cs ds} {Γ : Configuration ads cs ds}

      --------------------------------------------------------------------------------
    → Configuration ads cs (A has (v + v′) ∷ ds) ∋
      (  ⟨ A , v ⟩ᵈ
      ∣∣ ⟨ A , v′ ⟩ᵈ
      ∶- (λ {x} z → z) & (λ {x} z → z) & (λ ()) & refl & refl & refl
      ∣∣ A auth[ 0ᶠ ↔ sucᶠ 0ᶠ ]
      ∶- (λ {x} z → z) & (λ {x} z → z) & (λ {x} z → z) & refl & refl & refl
      ∣∣ Γ
      ∶- (λ {x} z → z) & (λ {x} z → z) & (λ ()) & refl & refl & {!!}
      )
      —→
      Configuration ads cs (A has (v + v′) ∷ ds) ∋
      (  ⟨ A , v + v′ ⟩ᵈ
      ∣∣ Γ
      ∶- (λ {x} z → z) & (λ {x} z → z) & (λ ()) & refl & refl & refl
      )

  [DEP-AuthDivide] :
    ∀ {A : Participant}
      {v v′ : Value}
      {ads cs ds} {Γ : Configuration ads cs ds}

      ----------------------------------------------------------------
    → Configuration ads cs (A has (v + v′) ∷ ds) ∋
      (  ⟨ A , v + v′ ⟩ᵈ
      ∣∣ Γ
      ∶- (λ {x} z → z) & (λ {x} z → z) & (λ ()) & refl & refl & refl
      )
      —→
      Configuration [] [] (A has v ∷ A has v′ ∷ []) ∋
      (  ⟨ A , v + v′ ⟩ᵈ
      ∣∣ A auth[ _▷_,_ {A} {[ v + v′ ]} 0ᶠ v v′ {fromWitness refl} ]
      ∶- (λ {x} z → z) & (λ {x} z → z) & (λ {x} z → z) & refl & refl & {!!}
      )
      ∣∣ Γ
      ∶- (λ {x} z → z) & (λ {x} z → z) & (λ ()) & refl & refl & refl


  [DEP-DIVIDE] :
    ∀ {A : Participant}
      {v v′ : Value}
      {ads cs ds} {Γ : Configuration ads cs ds}

      -----------------------------------------------------------------
    → Configuration ads cs (A has v ∷ A has v′ ∷ ds) ∋
      (  Configuration [] [] (A has v ∷ A has v′ ∷ []) ∋
      (  ⟨ A , v + v′ ⟩ᵈ
      ∣∣ A auth[ _▷_,_ {A} {[ v + v′ ]} 0ᶠ v v′ {fromWitness refl} ]
      ∶- (λ {x} z → z) & (λ {x} z → z) & (λ {x} z → z) & refl & refl & {!!}
      )
      ∣∣ Γ
      ∶- (λ {x} z → z) & (λ {x} z → z) & (λ ()) & refl & refl & refl
      )
      —→
      Configuration ads cs (A has v ∷ A has v′ ∷ ds) ∋
      (  ⟨ A , v ⟩ᵈ
      ∣∣ ⟨ A , v′ ⟩ᵈ ∶- (λ {x} z → z) & (λ {x} z → z) & (λ ()) & refl & refl & refl
      ∣∣ Γ           ∶- (λ {x} z → z) & (λ {x} z → z) & (λ ()) & refl & refl & refl
      )

  [DEP-AuthDonate] :
    ∀ {A B : Participant}
      {v : Value}
      {ads cs ds} {Γ : Configuration ads cs ds}

      ---------------------------------------------------------------------
    → Configuration ads cs (A has v ∷ ds) ∋
      (  ⟨ A , v ⟩ᵈ
      ∣∣ Γ
      ∶- (λ {x} z → z) & (λ {x} z → z) & (λ ()) & refl & refl & refl
      )
      —→
      Configuration ads cs (B has v ∷ ds) ∋
      (  Configuration [] [] [ B has v ] ∋
      (  ⟨ A , v ⟩ᵈ
      ∣∣ A auth[ _▷ᵈ_ {A} {[ v ]} 0ᶠ B ]
      ∶- (λ {x} z → z) & (λ {x} z → z) & (λ {x} z → z) & refl & refl & {!!}
      )
      ∣∣ Γ
      ∶- (λ {x} z → z) & (λ {x} z → z) & (λ ()) & refl & refl & refl
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
      ∶- (λ {x} z → z) & (λ {x} z → z) & (λ {x} z → z) & refl & refl & {!!}
      )
      ∣∣ Γ
      ∶- (λ {x} z → z) & (λ {x} z → z) & (λ ()) & refl & refl & refl
      )
      —→
      Configuration ads cs (B has v ∷ ds) ∋
      ( ⟨ B , v ⟩ᵈ
      ∣∣ Γ
      ∶- (λ {x} z → z) & (λ {x} z → z) & (λ ()) & refl & refl & refl
      )

  [DEP-AuthDestroy] :
    ∀ {A : Participant}
      {ads cs ds} {Γ : Configuration ads cs ds}
      {v : Value}

      ------------------------------------------------------------
    → Configuration ads cs (A has v ∷ ds) ∋
      (  ⟨ A , v ⟩ᵈ
      ∣∣ Γ
      ∶- (λ {x} z → z) & (λ {x} z → z) & (λ ()) & refl & refl & refl
      )
      —→
      Configuration ads cs ds ∋
      (  ⟨ A , v ⟩ᵈ
      ∣∣ A auth[ destroy {vs = [ v ]} 0ᶠ ]
      ∶- (λ {x} z → z) & (λ {x} z → z) & (λ {x} z → z) & refl & refl & {!!}
      ∣∣ Γ
      ∶- (λ {x} z → z) & (λ {x} z → z) & (λ {x} z → z) & refl & refl & refl
      )

  [DEP-Destroy] :
    ∀ {A : Participant}
      {ads cs ds} {Γ : Configuration ads cs ds}
      {v : Value}

      ------------------------------------------------------------
    → Configuration ads cs ds ∋
      ( Configuration [] [] [] ∋
      (  ⟨ A , v ⟩ᵈ
      ∣∣ A auth[ destroy {vs = [ v ]} 0ᶠ ]
      ∶- (λ {x} z → z) & (λ {x} z → z) & (λ {x} z → z) & refl & refl & {!!}
      )
      ∣∣ Γ
      ∶- (λ {x} z → z) & (λ {x} z → z) & (λ {x} z → z) & refl & refl & refl
      )
      —→
      Γ

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
      ∶- (λ ()) & (λ {x} z → z) & (λ {x} z → z) & refl & refl & refl
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
      ∶- (λ ()) & (λ {x} z → z) & (λ {x} z → z) & refl & refl & refl
      )
      —→
      Configuration ads cs ds ∋
      (  Configuration ((v , vsᶜ , vsᵍ , ad) ∷ ads) cs ds ∋
      (  ` ad
      ∣∣ Γ
      ∶- (λ ()) & (λ {x} z → z) & (λ {x} z → z) & refl & refl & refl
      ∣∣ Δ
      ∶- (λ ()) & (λ ()) & (λ ()) & {!!} & {!!} & {!!}
      )
      ∣∣ A auth[ ♯▷ ad ]
      ∶- {!!} & (λ ()) & (λ ()) & {!!} & {!!} & {!!}
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
      ∶- (λ ()) & (λ {x} z → z) & (λ {x} z → z) & refl & refl & refl
      )
      —→
      Configuration ads cs (dsˡ ++ dsʳ) ∋
      (  ` ad
      ∣∣ Γ
      ∶- (λ ()) & (λ {x} z → z) & (λ {x} z → z) & refl & refl & refl
      ∣∣ A auth[ ad ▷ˢ iᵍ ]
      ∶- {!!} & {!!} & {!!} & {!!} & {!!}
      )

  [C-Init] :
    ∀ {v vsᶜ vsᵍ} {ad : Advertisement v vsᶜ vsᵍ}
      {ads cs ds} {Γ : Configuration ads cs ds}
      {Δ : Configuration′ ([] , [ v , vsᶜ , vsᵍ , ad ]) ([] , []) ([] , [])}

      -- all participants have committed their secrets
    → All (λ p → p ∈ₚ committedParticipants Δ ad) (participantsᵍ (G ad))

      -- all participants have spent the required (persistent) deposits for stipulation
    → toStipulate (G ad) ≡ spentForStipulation Δ ad

      ----------------------------------------------------------------------

    → Configuration ads cs ds ∋
      (  Configuration ((v , vsᶜ , vsᵍ , ad) ∷ ads) cs ds ∋
      (  ` ad
      ∣∣ Γ
      ∶- (λ ()) & (λ {x} z → z) & (λ {x} z → z) & refl & refl & refl
      )
      ∣∣ Δ
      ∶- {!!} & (λ ()) & (λ ()) & {!!} & {!!} & {!!}
      )
      —→
      Configuration ads ((v , vsᶜ , C ad) ∷ cs) ds ∋
      (  ⟨ C ad , v ⟩ᶜ
      ∣∣ Γ
      ∶- (λ ()) & (λ ()) & (λ ()) & refl & refl & refl
      )

  -- iii) Rules for executing active contracts

  [C-Split] :
    ∀ {ads cs ds} {Γ : Configuration ads cs ds}
      {v vs} {c : Contract v vs}

      {cs′ : ActiveContracts}
      {cases : ContractCases}

      -- `split` command
    → (pr : Split cases v)
    → c ≡ split cases ∶- pr

      -- inner contracts
    → cs′ ≡ casesToContracts cases

      ------------------------------------------------------------

    → Configuration ads ((v , vs , [ c ]) ∷ cs) ds ∋
      (  ⟨ [ c ] , v ⟩ᶜ
      ∣∣ Γ
      ∶- (λ {x} z → z) & (λ ()) & (λ {x} z → z) & refl & refl & refl
      )
      —→
      Configuration ads (cs′ ++ cs) ds ∋
      (    cs′
      ∣∣ᶜˢ Γ
      )

  [C-AuthRev] :
    ∀ {A : Participant} {s : Secret} {n : ℕ} {n′ : ℕ ⊎ ⊥}

      -- only valid lengths
    → (p : n′ ≡ inj₁ n)
    → (len_s : True (lengthₛ s ≟ n))

      -----------------------------

    → ⟨ A ∶ s ♯ n′ ⟩  {inj₁ (n , p , len_s)}
      —→
      (A ∶ s ♯ n)     {len_s}

  [C-PutRev] :
    ∀ {ads cs ds} {Γ : Configuration ads cs ds}
      {v vs″} {c : Contract v vs″}
      {v′ vs′} {c′ : Contract v′ vs′}
      {s s′ : Secrets} {p : Predicate s′}
      {vs : Values} {ds′ : Deposits}
      {ss : List ValidSecret}

      -- `put` command
    → (pr : Put v vs v′
          × s′ ⊆ₛ s
          × vs″ ≡ vs′ ++ vs)
    → c ≡ (put vs &reveal s if p ⇒ c′ ∶- pr)

      -- revealed secrets
    → map (proj₁ ∘ proj₂) ss ≡ s

      -- put deposits
    → map value ds′ ≡ vs

      -- predicate is true
    → ⟦ p ⟧ᵇ ≡ true
      ------------------------------------------------------------

    → Configuration ads ((v , vs″ , [ c ]) ∷ cs) (ds′ ++ ds) ∋
      (  ⟨ [ c ] , v ⟩ᶜ
      ∣∣ (ds′ ∣∣ᵈˢ (ss ∣∣ˢˢ Γ))
      ∶- (λ {x} z → z) & (λ ()) & (λ {x} z → z) & refl & refl & refl
      )
      —→
      Configuration ads ((v′ , vs′ , [ c′ ]) ∷ cs) ds ∋
      (  ⟨ [ c′ ] , v′ ⟩ᶜ
      ∣∣ (ss ∣∣ˢˢ Γ)
      ∶- (λ {x} z → z) & (λ ()) & (λ {x} z → z) & refl & refl & refl
      )

  [C-Withdraw] :
    ∀ {ads cs ds} {Γ : Configuration ads cs ds}
      {A : Participant}
      {v} {c : Contract v []}

      -- `withdraw` command
    → c ≡ withdraw A

      -------------------------------------------------------

    → Configuration ads ((v , [] , [ c ]) ∷ cs) ds ∋
      (  ⟨ [ c ] , v ⟩ᶜ
      ∣∣ Γ
      ∶- (λ {x} z → z) & (λ ()) & (λ {x} z → z) & refl & refl & refl
      )
      —→
      Configuration ads cs (A has v ∷ ds) ∋
      (  ⟨ A , v ⟩ᵈ
      ∣∣ Γ
      ∶- (λ {x} z → z) & (λ {x} z → z) & (λ {x} ()) & refl & refl & refl
      )

  [C-AuthControl] :
    ∀ {ads cs ds} {Γ : Configuration ads cs ds}
      {A : Participant}
      {v vs} {contract : Contracts v vs} {i : Index contract}

      -- `auth` decoration
    → A ∈ₚ authDecorations (contract ‼ i)

      ------------------------------------------------------------------

    → Configuration ads ((v , vs , contract) ∷ cs) ds ∋
      (  ⟨ contract , v ⟩ᶜ
      ∣∣ Γ
      ∶- (λ {x} z → z) & (λ ()) & (λ {x} z → z) & refl & refl & refl
      )
      —→
      Configuration ads ((v , vs , contract) ∷ cs) ds ∋
      (  Configuration [] [ (v , vs , contract) ] [] ∋
      (  ⟨ contract , v ⟩ᶜ
      ∣∣ A auth[ contract ▷ᵇ i  ]
      ∶- (λ {x} z → z) & (λ {x} z → z) & (λ {x} z → z) & refl & refl & refl
      )
      ∣∣ Γ
      ∶- (λ {x} z → z) & (λ {x} ()) & (λ {x} z → z) & refl & refl & refl
      )


  [C-Control] :
    ∀ {ads cs ds} {Γ : Configuration ads cs ds}
      {ads′ cs′ ds′} {Γ′ : Configuration ads′ cs′ ds′}
      {A : Participant}
      {v vs} {contract : Contracts v vs} {i : Index contract}

      -- resulting state if we pick branch `i`
    → Configuration ads ((v , vs , [ contract ‼ i ]) ∷ cs) ds ∋
       (  ⟨ [ contract ‼ i ] , v ⟩ᶜ
       ∣∣ Γ
       ∶- (λ {x} z → z) & (λ ()) & (λ {x} z → z) & refl & refl & refl
       )
      —→
      Γ′

      ------------------------------------------------------------------

    → Configuration ads ((v , vs , contract) ∷ cs) ds ∋
      (  Configuration [] [ v , vs , contract ] [] ∋
      (   ⟨ contract , v ⟩ᶜ
      ∣∣ᵇ (0ᶠ , i , authDecorations (contract ‼ i))
      )
      ∣∣ Γ
      ∶- (λ {x} z → z) & (λ ()) & (λ {x} z → z) & refl & refl & refl
      )
      —→
      Γ′


-----------------------------------------------------------------------------------
-- Semantic rules for timed configurations.

record TimedConfiguration (ads : AdvertisedContracts)
                          (cs  : ActiveContracts)
                          (ds  : Deposits)
                          : Set where

  constructor _at_
  field
    cfg  : Configuration ads cs ds
    time : Time

open TimedConfiguration

infix -1 _—→ₜ_
data _—→ₜ_ : ∀ {ads cs ds ads′ cs′ ds′}
           → TimedConfiguration ads cs ds
           → TimedConfiguration ads′ cs′ ds′
           → Set where

  -- iv) Rules for handling time
  [Action] :
    ∀ {ads cs ds} {Γ : Configuration ads cs ds}
      {ads′ cs′ ds′} {Γ′ : Configuration ads′ cs′ ds′}
      {t : Time}

    → Γ —→ Γ′
      ----------------------------------------
    → Γ at t —→ₜ Γ′ at t

  [Delay] :
    ∀ {ads cs ds} {Γ : Configuration ads cs ds}
      {t δ : Time}

      ----------------------------------------
    → Γ at t —→ₜ Γ at (t + δ)

  [Timeout] :
    ∀ {ads cs ds} {Γ : Configuration ads cs ds}
      {ads′ cs′ ds′} {Γ′ : Configuration ads′ cs′ ds′}
      {v vs} {contract : Contracts v vs} {i : Index contract}
      {t : Time}

      -- all time constraints are satisfied
    → All (_≤ t) (timeDecorations (contract ‼ i))

      -- resulting state if we pick branch `i`
    → Configuration ads ((v , vs , [ contract ‼ i ]) ∷ cs) ds ∋
       (  ⟨ [ contract ‼ i ] , v ⟩ᶜ
       ∣∣ Γ
       ∶- (λ {x} z → z) & (λ ()) & (λ {x} z → z) & refl & refl & refl
       )
      —→
      Γ′

      ----------------------------------------

    → TimedConfiguration ads ((v , vs , contract) ∷ cs) ds ∋
      (  ⟨ contract , v ⟩ᶜ
      ∣∣ Γ
      ∶- (λ {x} z → z) & (λ ()) & (λ {x} z → z) & refl & refl & refl
      ) at t
      —→ₜ
      Γ′ at t
