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

open import BitML.Contracts.Types                            Participant _≟ₚ_ Honest
open import BitML.Contracts.Helpers                          Participant _≟ₚ_ Honest
open import BitML.Contracts.DecidableEquality                Participant _≟ₚ_ Honest
open import BitML.Semantics.Actions.Types                    Participant _≟ₚ_ Honest
open import BitML.Semantics.Configurations.Types             Participant _≟ₚ_ Honest
open import BitML.Semantics.Configurations.DecidableEquality Participant _≟ₚ_ Honest

-------------------------------------------------------------------

-- Re-ordering configurations
cfgToList : Configuration → List Configuration
cfgToList ∅ᶜ       = []
cfgToList (l ∣ r) = cfgToList l ++ cfgToList r
cfgToList c        = [ c ]

infix 3 _≈_
_≈_ : Configuration → Configuration → Set
c ≈ c′ = cfgToList c ↭ cfgToList c′

infix 3 _≈?_
_≈?_ : Decidable {A = Configuration} _≈_
-- _≈?_ : Configuration → Configuration → Set
c ≈? c′ = cfgToList c SETᶜᶠ.↭? cfgToList c′

depositsᶜ : Configuration → List DepositRef
depositsᶜ = SETₑ.nub ∘ go
  where
    go : Configuration → List DepositRef
    go (⟨ A has v ⟩at x) = [ A , v , x ]
    go (l ∣ r)           = depositsᶜ l ++ depositsᶜ r
    go _                 = []

secretsᶜ : Participant → Configuration → Secrets
secretsᶜ A = SETₛ.nub ∘ go
  where
    go : Configuration → Secrets
    go (⟨ B ∶ a ♯ _ ⟩) with A ≟ₚ B
    ... | yes _ = [ a ]
    ... | no  _ = []
    go (l ∣ r)       = secretsᶜ A l ++ secretsᶜ A r
    go _             = []

committedParticipants : Configuration → Advertisement → List Participant
committedParticipants (p auth[ (♯▷ ad′) ]) ad
  with ad ≟ₐ ad′
... | yes _ = [ p ]
... | no  _ = []
committedParticipants (l ∣ r) ad = committedParticipants l ad ++ committedParticipants r ad
committedParticipants _       _  = []

{-
casesToContracts : ∀ {vs : Values} → ContractCases vs → ActiveContracts
casesToContracts {vs} = map (λ{ (v , c) → Iᶜ[ v , vs ] , [ c ] })

isInitial : Configuration′ cf′i → Bool
isInitial (⟨ _ , _ ⟩ᵈ)    = true
isInitial (c₁ ∣ c₂ ∶- _) = isInitial c₁ ∧ isInitial c₂
isInitial _               = false

Initial : Configuration′ cf′i → Set
Initial = T ∘ isInitial

committedSecrets : Configuration′ cf′i → List (Participant × Secret × Maybe ℕ)
committedSecrets ⟨ x ∶ s ♯ n ⟩ =  [  x , s , n ]
committedSecrets (l ∣ r ∶- _) = committedSecrets l ++ committedSecrets r
committedSecrets _ = []

spentForStipulation : Configuration′ cf′i → Advertisement ci pi → List (Participant × Value)
spentForStipulation {ci = ci} {pi = pi} (p auth[ (_▷ˢ_ {ci = ci′} {vsᵛ = vsᵛ} {vsᵖ = vsᵖ} ad′ iᵖ) ]∶- _) ad
  with (ci , pi , ad) ∃≟ₐ (ci′ , Iᵖ[ vsᵛ , vsᵖ ] , ad′)
... | yes _ = [ p , (vsᵖ ‼ iᵖ) ]
... | no  _ = []
spentForStipulation (l ∣ r ∶- _) ad = spentForStipulation l ad
                                    ++ spentForStipulation r ad
spentForStipulation _ _ = []

ValidSecret : Set
ValidSecret = Participant × ∃[ s ] ∃[ n ] (lengthₛ s ≡ n)

infixl 4 _∣ˢˢ_
_∣ˢˢ_ : (ss : List ValidSecret) → Configuration cfi → Configuration cfi
[]                      ∣ˢˢ Γ = Γ
((p , s , n , pr) ∷ ss) ∣ˢˢ Γ =
     (p ∶ s ♯ n) {fromWitness pr}
  ∣ (ss ∣ˢˢ Γ)
  ∶- refl & refl & refl & refl & refl & refl

infixl 4 _∣ᵇ_
_∣ᵇ_ : Configuration Iᶜᶠ[ ads , cs , ds ]
      → Σ[ i ∈ Index cs ] (Index (proj₂ (cs ‼ i)) × List Participant)
      → Configuration Iᶜᶠ[ ads , cs , ds ]
_∣ᵇ_ {ads} {cs} {ds} Γ (i , j , [])     = Γ
_∣ᵇ_ {ads} {cs} {ds} Γ (i , j , p ∷ ps) =
  (  Γ
  ∣ p auth[ proj₂ (cs ‼ i) ▷ᵇ j ]∶- refl & refl & refl & refl & refl & refl
  ∶- ++-idʳ & SETₐ.\\-left {ads}
   & ++-idʳ & SETᶜ.\\-‼ {cs} {i}
   & ++-idʳ & SETₑ.\\-left {ds}
  )
  ∣ᵇ (i , j , ps)

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
  ∣ ⟨ p ∶ s ♯ nothing ⟩
  ∶- ++-idʳ & (SETₐ.\\-left {ads})
   & ++-idʳ & (SETᶜ.\\-left {cs})
   & ++-idʳ & (SETₑ.\\-left {ds})
  ∣∅ ss
_∣∅_ {ads} {cs} {ds} Γ ((p , s , just (n , n≡)) ∷ ss) =
     Γ
  ∣ (⟨ p ∶ s ♯ just n ⟩ {length→isValidSecret n≡})
  ∶- ++-idʳ & (SETₐ.\\-left {ads})
   & ++-idʳ & (SETᶜ.\\-left {cs})
   & ++-idʳ & (SETₑ.\\-left {ds})
  ∣∅ ss

-}
