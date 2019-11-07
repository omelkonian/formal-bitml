------------------------------------------------------------------------
-- Utilities for constructing configurations.
------------------------------------------------------------------------

open import Level        using (0ℓ)
open import Function     using (_∘_)
open import Data.Empty   using (⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Bool    using (T; Bool; true; false; _∧_; if_then_else_)
open import Data.Maybe   using (Maybe; just; nothing; maybe′)
open import Data.Nat     using (ℕ; suc; _+_; _≤_; _>_; _≟_)
open import Data.Product using (∃; ∃-syntax; Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
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

open import Prelude.Lists

open import BitML.BasicTypes

module BitML.Semantics.Configurations.Helpers
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))
  where
    
open import BitML.Contracts.Types                Participant _≟ₚ_ Honest
open import BitML.Contracts.DecidableEquality    Participant _≟ₚ_ Honest
open import BitML.Semantics.Actions.Types        Participant _≟ₚ_ Honest
open import BitML.Semantics.Configurations.Types Participant _≟ₚ_ Honest

-------------------------------------------------------------------

casesToContracts : ∀ {vs : Values} → ContractCases vs → ActiveContracts
casesToContracts {vs} = map (λ{ (v , c) → Iᶜ[ v , vs ] , [ c ] })

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

-- Implicit version of _auth[_]∶-_
_auth[_] : ∀ {p₁₁ p₁₂ p₂₁ p₂₂ p₃₁ p₃₂}
         → (p : Participant)
         → Action p Iᵃᶜ[ ads , cs , vs , ds ]
         → .{pr₁₁ : True (p₁₁ SETₐ.≟ₗ [])}
         → .{pr₁₂ : True (p₁₂ SETₐ.≟ₗ ads)}
         → .{pr₂₁ : True (p₂₁ SETᶜ.≟ₗ [])}
         → .{pr₂₂ : True (p₂₂ SETᶜ.≟ₗ cs)}
         → .{pr₃₁ : True (p₃₁ SETₑ.≟ₗ  ds)}
         → .{pr₃₂ : True (p₃₂ SETₑ.≟ₗ ((p has_) <$> vs))}
         → Configuration′ Iᶜᶠ[ p₁₁ & p₁₂ , p₂₁ & p₂₂ , p₃₁ & p₃₂ ]
(p auth[ x ]) {pr₁₁} {pr₁₂} {pr₂₁} {pr₂₂} {pr₃₁} {pr₃₂} =
  p auth[ x ]∶- toWitness pr₁₁ & toWitness pr₁₂
              & toWitness pr₂₁ & toWitness pr₂₂
              & toWitness pr₃₁ & toWitness pr₃₂

-- Implicit version of _∣∣_∶-_
_∣∣_ : Configuration′ Iᶜᶠ[ adsˡ & radsˡ , csˡ & rcsˡ , dsˡ & rdsˡ ]
     → Configuration′ Iᶜᶠ[ adsʳ & radsʳ , csʳ & rcsʳ , dsʳ & rdsʳ ]
     → .{pr₁₁ : True (ads  SETₐ.≟ₗ adsˡ ++ adsʳ)}
     → .{pr₁₂ : True (rads SETₐ.≟ₗ radsˡ ++ (radsʳ SETₐ.\\ adsˡ))}
     → .{pr₂₁ : True (cs   SETᶜ.≟ₗ csˡ  ++ csʳ)}
     → .{pr₂₂ : True (rcs  SETᶜ.≟ₗ rcsˡ ++ (rcsʳ SETᶜ.\\ csˡ))}
     → .{pr₃₁ : True (ds   SETₑ.≟ₗ (dsˡ SETₑ.\\ rdsʳ) ++ dsʳ)}
     → .{pr₃₂ : True (rds  SETₑ.≟ₗ rdsˡ ++ (rdsʳ SETₑ.\\ dsˡ))}
     → Configuration′ Iᶜᶠ[ ads & rads , cs & rcs , ds & rds ]
(c₁ ∣∣ c₂) {pr₁₁} {pr₁₂} {pr₂₁} {pr₂₂} {pr₃₁} {pr₃₂} =
     c₁ ∣∣ c₂ ∶- toWitness pr₁₁ & toWitness pr₁₂
               & toWitness pr₂₁ & toWitness pr₂₂
               & toWitness pr₃₁ & toWitness pr₃₂

isInitial : Configuration′ cf′i → Bool
isInitial (⟨ _ , _ ⟩ᵈ)    = true
isInitial (c₁ ∣∣ c₂ ∶- _) = isInitial c₁ ∧ isInitial c₂
isInitial _               = false

Initial : Configuration′ cf′i → Set
Initial = T ∘ isInitial

depositsᶜ : Configuration′ cf′i → List Deposit
depositsᶜ {cf′i = cf′i} _ = proj₁ (deposits cf′i)

committedSecrets : Configuration′ cf′i → List (Participant × Secret × Maybe ℕ)
committedSecrets ⟨ x ∶ s ♯ n ⟩ =  [  x , s , n ]
committedSecrets (l ∣∣ r ∶- _) = committedSecrets l ++ committedSecrets r
committedSecrets _ = []

committedParticipants : Configuration′ cf′i → Advertisement ci pi → List Participant
committedParticipants {ci = ci} {pi = pi} (p auth[ (♯▷_ {ci = ci′} {pi = pi′} ad′) ]∶- _) ad
  with (ci , pi , ad) ∃≟ₐ (ci′ , pi′ , ad′)
... | yes _ = [ p ]
... | no  _ = []
committedParticipants (l ∣∣ r ∶- _) ad = committedParticipants l ad
                                      ++ committedParticipants r ad
committedParticipants _ _ = []

spentForStipulation : Configuration′ cf′i → Advertisement ci pi → List (Participant × Value)
spentForStipulation {ci = ci} {pi = pi} (p auth[ (_▷ˢ_ {ci = ci′} {vsᵛ = vsᵛ} {vsᵖ = vsᵖ} ad′ iᵖ) ]∶- _) ad
  with (ci , pi , ad) ∃≟ₐ (ci′ , Iᵖ[ vsᵛ , vsᵖ ] , ad′)
... | yes _ = [ p , (vsᵖ ‼ iᵖ) ]
... | no  _ = []
spentForStipulation (l ∣∣ r ∶- _) ad = spentForStipulation l ad
                                    ++ spentForStipulation r ad
spentForStipulation _ _ = []

infixl 4 _∣∣ᶜˢ_
_∣∣ᶜˢ_ : (cs′ : ActiveContracts) → Configuration Iᶜᶠ[ ads , cs , ds ] → Configuration Iᶜᶠ[ ads , cs′ ++ cs , ds ]
[]                  ∣∣ᶜˢ Γ = Γ
((Iᶜ[ v , vs ] , c) ∷ cs) ∣∣ᶜˢ Γ =
     ⟨ c ⟩ᶜ
  ∣∣ (cs ∣∣ᶜˢ Γ)
  ∶- refl & refl & refl & (SETᶜ.\\-left {[ Iᶜ[ v , vs ] , c ]}) & refl & refl

infixl 4 _∣∣ᵈˢ_
_∣∣ᵈˢ_ : (ds′ : Deposits) → Configuration Iᶜᶠ[ ads , cs , ds ] → Configuration Iᶜᶠ[ ads , cs , ds′ ++ ds ]
[]       ∣∣ᵈˢ Γ = Γ
(d ∷ ds) ∣∣ᵈˢ Γ =
     ⟨ participant d , value d ⟩ᵈ
  ∣∣ (ds ∣∣ᵈˢ Γ)
  ∶- refl & refl & refl & refl & refl & SETₑ.\\-left {[ d ]}

ValidSecret : Set
ValidSecret = Participant × ∃[ s ] ∃[ n ] (lengthₛ s ≡ n)

infixl 4 _∣∣ˢˢ_
_∣∣ˢˢ_ : (ss : List ValidSecret) → Configuration cfi → Configuration cfi
[]                      ∣∣ˢˢ Γ = Γ
((p , s , n , pr) ∷ ss) ∣∣ˢˢ Γ =
     (p ∶ s ♯ n) {fromWitness pr}
  ∣∣ (ss ∣∣ˢˢ Γ)
  ∶- refl & refl & refl & refl & refl & refl

infixl 4 _∣∣ᵇ_
_∣∣ᵇ_ : Configuration Iᶜᶠ[ ads , cs , ds ]
      → Σ[ i ∈ Index cs ] (Index (proj₂ (cs ‼ i)) × List Participant)
      → Configuration Iᶜᶠ[ ads , cs , ds ]
_∣∣ᵇ_ {ads} {cs} {ds} Γ (i , j , [])     = Γ
_∣∣ᵇ_ {ads} {cs} {ds} Γ (i , j , p ∷ ps) =
  (  Γ
  ∣∣ p auth[ proj₂ (cs ‼ i) ▷ᵇ j ]∶- refl & refl & refl & refl & refl & refl
  ∶- ++-idʳ & SETₐ.\\-left {ads}
   & ++-idʳ & SETᶜ.\\-‼ {cs} {i}
   & ++-idʳ & SETₑ.\\-left {ds}
  )
  ∣∣ᵇ (i , j , ps)

CommittedSecret : Set
CommittedSecret = Σ[ s ∈ Secret ] Maybe (Σ[ n ∈ ℕ ] (lengthₛ s ≡ n))

length→isValidSecret : ∀ {s n} → lengthₛ s ≡ n → isValidSecret s (just n)
length→isValidSecret {s} {n} eq with lengthₛ s ≟ n
... | no ¬p = ⊥-elim (¬p eq)
... | yes p = tt

infixl 4 _∣∅_
_∣∅_ : Configuration Iᶜᶠ[ ads , cs , ds ]
     → List (Participant × CommittedSecret)
     → Configuration Iᶜᶠ[ ads , cs , ds ]
_∣∅_ {ads} {cs} {ds} Γ []       = Γ
_∣∅_ {ads} {cs} {ds} Γ ((p , s , nothing) ∷ ss) =
     Γ
  ∣∣ ⟨ p ∶ s ♯ nothing ⟩
  ∶- ++-idʳ & (SETₐ.\\-left {ads})
   & ++-idʳ & (SETᶜ.\\-left {cs})
   & ++-idʳ & (SETₑ.\\-left {ds})
  ∣∅ ss
_∣∅_ {ads} {cs} {ds} Γ ((p , s , just (n , n≡)) ∷ ss) =
     Γ
  ∣∣ (⟨ p ∶ s ♯ just n ⟩ {length→isValidSecret n≡})
  ∶- ++-idʳ & (SETₐ.\\-left {ads})
   & ++-idʳ & (SETᶜ.\\-left {cs})
   & ++-idʳ & (SETₑ.\\-left {ds})
  ∣∅ ss

authDecorations : Contract ci → List Participant
authDecorations (x       ∶ c) = x ∷ authDecorations c
authDecorations (after _ ∶ c) = authDecorations c
authDecorations _             = []

timeDecorations : Contract ci → List Time
timeDecorations (_       ∶ c) = timeDecorations c
timeDecorations (after t ∶ c) = t ∷ timeDecorations c
timeDecorations _             = []

removeTopDecorations : Contract ci → Contract ci
removeTopDecorations (_       ∶ c) = removeTopDecorations c
removeTopDecorations (after _ ∶ c) = removeTopDecorations c
removeTopDecorations c             = c

cfgToList : Configuration′ cf′i → List ∃Configuration′
cfgToList ∅ᶜ            = []
cfgToList (l ∣∣ r ∶- _) = cfgToList l ++ cfgToList r
cfgToList {cf′i} c      = [ cf′i , c ]

infix -2 _≈_
_≈_ : Configuration cfi → Configuration cfi → Set
c ≈ c′ = cfgToList c ↭ cfgToList c′
