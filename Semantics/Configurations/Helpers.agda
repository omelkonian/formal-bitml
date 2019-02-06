------------------------------------------------------------------------
-- Utilities for constructing configurations.
------------------------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas #-}
open import Level        using (0ℓ)
open import Function     using (_∘_)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Bool    using (T; Bool; true; false; _∧_; if_then_else_)
open import Data.Maybe   using (Maybe; just; nothing; maybe′)
open import Data.Nat     using (ℕ; suc; _+_; _≤_; _>_; _≟_)
open import Data.Product using (∃; ∃-syntax; Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂; isInj₁; isInj₂)
open import Data.String  using ()
  renaming (length to lengthₛ)

open import Data.List using (List; []; _∷_; [_]; _++_; map; length)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Relation.Permutation.Inductive using (_↭_)

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋; True; False; toWitness; fromWitness)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary using (Decidable)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Category.Functor using (RawFunctor)
open import Data.List.Categorical renaming (functor to listFunctor)
open RawFunctor {0ℓ} listFunctor using (_<$>_)

module Semantics.Configurations.Helpers
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))
  where

open import Utilities.Lists
open import Types                          Participant _≟ₚ_ Honest
open import BitML.Types                    Participant _≟ₚ_ Honest
open import BitML.DecidableEquality        Participant _≟ₚ_ Honest
open import Semantics.Actions.Types        Participant _≟ₚ_ Honest
open import Semantics.Configurations.Types Participant _≟ₚ_ Honest

-------------------------------------------------------------------

infix  7 _auth[_]
infixl 5 _∣∣_

-- Implicit version of _auth[_]∶-_

pair≟ : ∀ {ℓ} {A : Set ℓ}
      → Decidable {A = A} _≡_
      → Decidable {A = A × A} _≡_
pair≟ _≟a_ (a , b) (a′ , b′)
  with a ≟a a′
... | no ¬p = no λ{refl → ¬p refl}
... | yes refl
  with b ≟a b′
... | no ¬p = no λ{refl → ¬p refl}
... | yes refl = yes refl

_auth[_] : ∀ {ads cs vs ds} {p₁ p₂ p₃}
        → (p : Participant)
        → Action p ads cs vs ds
        → .{pr₁ : True (pair≟ SETₐ._≟ₗ_ p₁ ([] , ads))}
        → .{pr₂ : True (pair≟ SETᶜ._≟ₗ_ p₂ ([] , cs))}
        → .{pr₃ : True (pair≟ SETₑ._≟ₗ_ p₃ (ds , ((p has_) <$> vs)))}
        → Configuration′ p₁ p₂ p₃
(p auth[ x ]) {pr₁} {pr₂} {pr₃} =
  p auth[ x ]∶- toWitness pr₁ & toWitness pr₂ & toWitness pr₃

-- Implicit version of _∣∣_∶-_

_∣∣_ : ∀ {adsˡ radsˡ adsʳ radsʳ ads rads : AdvertisedContracts}
         {csˡ rcsˡ csʳ rcsʳ cs rcs : ActiveContracts}
         {dsˡ rdsˡ dsʳ rdsʳ ds rds : Deposits}
     → Configuration′ (adsˡ , radsˡ) (csˡ , rcsˡ) (dsˡ , rdsˡ)
     → Configuration′ (adsʳ , radsʳ) (csʳ , rcsʳ) (dsʳ , rdsʳ)
     → {p₁ : True (ads SETₐ.≟ₗ adsˡ ++ adsʳ)}
     → {p₂ : True (rads SETₐ.≟ₗ radsˡ ++ (radsʳ SETₐ.\\ adsˡ))}
     → {p₃ : True (cs SETᶜ.≟ₗ csˡ ++ csʳ)}
     → {p₄ : True (rcs SETᶜ.≟ₗ rcsˡ ++ (rcsʳ SETᶜ.\\ csˡ))}
     → {p₅ : True (ds SETₑ.≟ₗ (dsˡ SETₑ.\\ rdsʳ) ++ dsʳ)}
     → {p₆ : True (rds SETₑ.≟ₗ rdsˡ ++ (rdsʳ SETₑ.\\ dsˡ))}
     → Configuration′ (ads , rads) (cs , rcs) (ds , rds)
(c₁ ∣∣ c₂) {p₁} {p₂} {p₃} {p₄} {p₅} {p₆} =
     c₁
  ∣∣ c₂
  ∶- toWitness p₁ & toWitness p₂ & toWitness p₃
   & toWitness p₄ & toWitness p₅ & toWitness p₆

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
committedParticipants {v} {vsᶜ} {vsᵍ}
                      (p auth[ (♯▷_ {v′} {vsᶜ′} {vsᵍ′} ad′) ]∶- _) ad
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
                    (p auth[ (_▷ˢ_ {v′} {vsᶜ′} {vsᵍ′} ad′ iᵍ) ]∶- _) ad
  with (v , vsᶜ , vsᵍ , ad) ∃≟ₐ (v′ , vsᶜ′ , vsᵍ′ , ad′)
... | yes _ = [ p , (vsᵍ′ ‼ iᵍ) ]
... | no  _ = []
spentForStipulation (l ∣∣ r ∶- _) ad = spentForStipulation l ad
                                    ++ spentForStipulation r ad
spentForStipulation _ _ = []

infixl 4 _∣∣ᶜˢ_
_∣∣ᶜˢ_ : ∀ {ads cs ds}
      → (cs′ : ActiveContracts)
      → Configuration ads cs ds
      → Configuration ads (cs′ ++ cs) ds
[]                  ∣∣ᶜˢ Γ = Γ
((v , vs , c) ∷ cs) ∣∣ᶜˢ Γ =
     ⟨ c , v ⟩ᶜ
  ∣∣ (cs ∣∣ᶜˢ Γ)
  ∶- refl & refl & refl & (SETᶜ.\\-left {[ v , vs , c ]}) & refl & refl

infixl 4 _∣∣ᵈˢ_
_∣∣ᵈˢ_ : ∀ {ads cs ds}
      → (ds′ : Deposits)
      → Configuration ads cs ds
      → Configuration ads cs (ds′ ++ ds)
[]       ∣∣ᵈˢ Γ = Γ
(d ∷ ds) ∣∣ᵈˢ Γ =
     ⟨ participant d , value d ⟩ᵈ
  ∣∣ (ds ∣∣ᵈˢ Γ)
  ∶- refl & refl & refl & refl & refl & SETₑ.\\-left {[ d ]}

ValidSecret : Set
ValidSecret = Participant × ∃[ s ] ∃[ n ] (lengthₛ s ≡ n)

infixl 4 _∣∣ˢˢ_
_∣∣ˢˢ_ : ∀ {ads cs ds}
      → (ss : List ValidSecret)
      → Configuration ads cs ds
      → Configuration ads cs ds
[]                      ∣∣ˢˢ Γ = Γ
((p , s , n , pr) ∷ ss) ∣∣ˢˢ Γ =
     (p ∶ s ♯ n) {fromWitness pr}
  ∣∣ (ss ∣∣ˢˢ Γ)
  ∶- refl & refl & refl & refl & refl & refl

infixl 4 _∣∣ᵇ_
_∣∣ᵇ_ : ∀ {ads cs ds}
      → Configuration ads cs ds
      → ( Σ[ x ∈ Index cs ] (Index ((proj₂ ∘ proj₂) (cs ‼ x)) × List Participant)
        )
      → Configuration ads cs ds
_∣∣ᵇ_ {ads} {cs} {ds} Γ (i , j , [])     = Γ
_∣∣ᵇ_ {ads} {cs} {ds} Γ (i , j , p ∷ ps) =
  (  Γ
  ∣∣ p auth[ ((proj₂ ∘ proj₂) (cs ‼ i)) ▷ᵇ j ]∶- refl & refl & refl
  ∶- ++-idʳ & SETₐ.\\-left {ads}
   & ++-idʳ & SETᶜ.\\-‼ {cs} {i}
   & ++-idʳ & SETₑ.\\-left {ds}
  )
  ∣∣ᵇ (i , j , ps)

CommittedSecret : Set
CommittedSecret = Participant × (Σ[ s ∈ Secret ] ((Σ[ n ∈ ℕ ] (lengthₛ s ≡ n)) ⊎ ⊥))

infixl 4 _∣∅_
_∣∅_ : ∀ {ads cs ds}
     → Configuration ads cs ds
     → List (Configuration [] [] [])
     → Configuration ads cs ds
_∣∅_ {ads} {cs} {ds} Γ []       = Γ
_∣∅_ {ads} {cs} {ds} Γ (s ∷ ss) =
     Γ
  ∣∣ s
  ∶- ++-idʳ & (SETₐ.\\-left {ads})
   & ++-idʳ & (SETᶜ.\\-left {cs})
   & ++-idʳ & (SETₑ.\\-left {ds})
  ∣∅ ss

length→isValidSecret : ∀ {s n} → lengthₛ s ≡ n → isValidSecret s (inj₁ n)
length→isValidSecret {s} {n} eq with lengthₛ s ≟ n
... | no ¬p = ⊥-elim (¬p eq)
... | yes p = tt

fromSecrets : List CommittedSecret → List (Configuration [] [] [])
fromSecrets [] = []
fromSecrets ((p , s , inj₂ ()) ∷ ss)
fromSecrets ((p , s , inj₁ (n , n≡)) ∷ ss) =
  (⟨ p ∶ s ♯ inj₁ n ⟩ {length→isValidSecret n≡}) ∷ fromSecrets ss

casesToContracts : ContractCases → ActiveContracts
casesToContracts = map (λ{ (v , vs , c) → v , vs , [ c ] })

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

cfgToList : ∀ {p₁ p₂ p₃}
          → Configuration′ p₁ p₂ p₃
          → List (∃[ p₁ ] ∃[ p₂ ] ∃[ p₃ ] Configuration′ p₁ p₂ p₃)
cfgToList ∅ᶜ               = []
cfgToList (l ∣∣ r ∶- _)    = cfgToList l ++ cfgToList r
cfgToList {p₁} {p₂} {p₃} c = [ p₁ , p₂ , p₃ , c ]

is∅ : Configuration [] [] [] → Set
is∅ ∅ᶜ = ⊤
is∅ c  = ⊥

remove∅ : ∀ {p₁ p₂ p₃}
        → Configuration′ p₁ p₂ p₃
        → Configuration′ p₁ p₂ p₃
remove∅ ∅ᶜ = ∅ᶜ
remove∅ {ads , rads} {cs , rcs} {ds , rds}
  (_∣∣_∶-_ {adsˡ} {radsˡ} {.[]} {.[]} {.ads} {.rads}
           {csˡ} {rcsˡ} {.[]} {.[]} {.cs} {.rcs}
           {dsˡ} {rdsˡ} {.[]} {.[]} {.ds} {.rds}
           l ∅ᶜ _)
  = {!l!}
remove∅ c = c

infix -2 _≈_
_≈_ : ∀ {ads cs ds} → Configuration ads cs ds → Configuration ads cs ds → Set
c ≈ c′ = (cfgToList ∘ remove∅) c ↭ (cfgToList ∘ remove∅) c′
