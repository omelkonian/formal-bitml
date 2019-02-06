------------------------------------------------------------------------
-- Decidable equality for contracts and advertisements
------------------------------------------------------------------------

open import Level        using (0ℓ)
open import Function     using (_∘_)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (tt; ⊤)
open import Data.Bool    using (T; true; false)
  renaming (_≟_ to _≟ᵇ_)
open import Data.List    using ( List; []; _∷_; [_]; _++_
                               ; map; concatMap; length; filter
                               )
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃₂; ∃-syntax; Σ; Σ-syntax)

open import Data.List.Any using (Any; any; here; there)
open import Data.List.Any.Properties using (any⁺)

open import Data.Nat using ( ℕ; zero; suc; _<_; _>_; _+_; _∸_
                           ; _≤_; z≤n; s≤s; _≤?_; _≥?_; _≟_
                           )

open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; toWitness; fromWitness; True)
open import Relation.Binary  using (Decidable)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂)

open import Category.Functor using (RawFunctor)
open import Data.List.Categorical renaming (functor to listFunctor)
open RawFunctor {0ℓ} listFunctor using (_<$>_)

module BitML.DecidableEquality
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))
  where

import Data.Set' as SET
open import Utilities.Lists

open import Types       Participant _≟ₚ_ Honest
open import BitML.Types Participant _≟ₚ_ Honest

------------------------------------------------------------------------

-- Contracts.
_≟ᶜˢ_ : ∀ {v vs} → Decidable {A = Contracts v vs} _≡_
_∃≟ᶜˢ_ : Decidable {A = ∃[ v ] ∃[ vs ] Contracts v vs} _≡_

-- NB: mutual recursion needed  here to satisfy the termination checker
_≟ᶜ_ : ∀ {v vs} → Decidable {A = Contract v vs} _≡_
_∃s≟ᶜ_ : Decidable {A = List (∃[ v ] ∃[ vs ] Contract v vs)} _≡_

[]                  ∃s≟ᶜ []                      = yes refl
[]                  ∃s≟ᶜ (_ ∷ _)                 = no λ ()
(_ ∷ _)             ∃s≟ᶜ []                      = no λ ()
((v , vs , c) ∷ cs) ∃s≟ᶜ ((v′ , vs′ , c′) ∷ cs′) with v ≟ v′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with vs SETₙ.≟ₗ vs′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with c ≟ᶜ c′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with cs ∃s≟ᶜ cs′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl

put_&reveal_if_⇒_∶-_ {_} {v} {vss} {s′ = sᵖ} vs s p c _ ≟ᶜ
 put_&reveal_if_⇒_∶-_ {_} {v′} {vss′} {s′ = sᵖ′} vs′ s′ p′ c′ _
               with vs SETₙ.≟ₗ vs′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with s SETₛ.≟ₗ s′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with sᵖ SETₛ.≟ₗ sᵖ′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with p ≟ₚᵣₑ p′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with v ≟ v′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with vss SETₙ.≟ₗ vss′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with c ≟ᶜ c′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl
(put vs &reveal s if x ⇒ c ∶- x₁) ≟ᶜ withdraw _     = no λ ()
(put vs &reveal s if x ⇒ c ∶- x₁) ≟ᶜ (split _ ∶- _) = no λ ()
(put vs &reveal s if x ⇒ c ∶- x₁) ≟ᶜ (_ ∶ _)        = no λ ()
(put vs &reveal s if x ⇒ c ∶- x₁) ≟ᶜ (after _ ∶ _)  = no λ ()

withdraw x ≟ᶜ withdraw x′ with x ≟ₚ x′
... | no ¬p = no λ{refl → ¬p refl}
... | yes refl = yes refl
withdraw x ≟ᶜ (put _ &reveal _ if _ ⇒ _ ∶- _)       = no λ ()
withdraw x ≟ᶜ (split _ ∶- _)                        = no λ ()
withdraw x ≟ᶜ (_ ∶ _)                               = no λ ()
withdraw x ≟ᶜ (after _ ∶ _)                         = no λ ()

(split cs ∶- _) ≟ᶜ (split cs′ ∶- _) with cs ∃s≟ᶜ cs′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl
(split cs ∶- x) ≟ᶜ (put _ &reveal _ if _ ⇒ _ ∶- _)  = no λ ()
(split cs ∶- x) ≟ᶜ withdraw _                       = no λ ()
(split cs ∶- x) ≟ᶜ (_ ∶ _)                          = no λ ()
(split cs ∶- x) ≟ᶜ (after _ ∶ _)                    = no λ ()

(p ∶ c) ≟ᶜ (p′ ∶ c′) with p ≟ₚ p′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with c ≟ᶜ c′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl
(_ ∶ _) ≟ᶜ (put _ &reveal _  if _ ⇒ _ ∶- _)         = no λ ()
(_ ∶ _) ≟ᶜ withdraw _                               = no λ ()
(_ ∶ _) ≟ᶜ (split _ ∶- _)                           = no λ ()
(_ ∶ _) ≟ᶜ (after _ ∶ _)                            = no λ ()

(after t ∶ c) ≟ᶜ (after t′ ∶ c′) with t ≟ t′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with c ≟ᶜ c′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl
(after t ∶ c) ≟ᶜ (put _ &reveal _ if _ ⇒ _ ∶- _)    = no λ ()
(after _ ∶ _) ≟ᶜ withdraw _                         = no λ ()
(after _ ∶ _) ≟ᶜ (split _ ∶- _)                     = no λ ()
(after _ ∶ _) ≟ᶜ (_ ∶ _)                            = no λ ()

_∃≟ᶜ_ : Decidable {A = ∃[ v ] ∃[ vs ] Contract v vs} _≡_
c ∃≟ᶜ c′ with [ c ] ∃s≟ᶜ [ c′ ]
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl

[] ≟ᶜˢ [] = yes refl
[] ≟ᶜˢ (_ ∷ _) = no λ ()
(_ ∷ _) ≟ᶜˢ [] = no λ ()
(x ∷ xs) ≟ᶜˢ (y ∷ ys) with x ≟ᶜ y
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with xs ≟ᶜˢ ys
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl

(v , vs , cs) ∃≟ᶜˢ (v′ , vs′ , cs′) with v ≟ v′
... | no ¬p = no λ{refl → ¬p refl}
... | yes refl with vs SETₙ.≟ₗ vs′
... | no ¬p = no λ{refl → ¬p refl}
... | yes refl with cs ≟ᶜˢ cs′
... | no ¬p = no λ{refl → ¬p refl}
... | yes refl = yes refl

module SETᶜ = SET _∃≟ᶜˢ_

Set⟨Contracts⟩ : Set
Set⟨Contracts⟩ = Set'
  where open SETᶜ

-- Advertisements.
_≟ₐ_ : ∀ {v vsᶜ vsᵍ} → Decidable {A = Advertisement v vsᶜ vsᵍ} _≡_
(⟨ G₁ ⟩ C₁ ∶- _) ≟ₐ (⟨ G₂ ⟩ C₂ ∶- _) with G₁ ≟ₚᵣ G₂
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with C₁ ≟ᶜˢ C₂
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl

_∃≟ₐ_ : Decidable {A = ∃[ v ] ∃[ vsᶜ ] ∃[ vsᵍ ] Advertisement v vsᶜ vsᵍ} _≡_
(v , vsᶜ , vsᵍ , ad) ∃≟ₐ (v′ , vsᶜ′ , vsᵍ′ , ad′) with v ≟ v′
... | no ¬p = no λ{refl → ¬p refl}
... | yes refl with vsᶜ SETₙ.≟ₗ vsᶜ′
... | no ¬p = no λ{refl → ¬p refl}
... | yes refl with vsᵍ SETₙ.≟ₗ vsᵍ′
... | no ¬p = no λ{refl → ¬p refl}
... | yes refl with ad ≟ₐ ad′
... | no ¬p = no λ{refl → ¬p refl}
... | yes refl = yes refl

module SETₐ = SET _∃≟ₐ_

Set⟨Advertisement⟩ : Set
Set⟨Advertisement⟩ = Set'
  where open SETₐ
