------------------------------------------------------------------------
-- Decidable equality for configurations.
------------------------------------------------------------------------

open import Data.Unit    using (⊤; tt)
open import Data.Maybe   using (just)
open import Data.Nat     using (ℕ; suc; _+_; _≤_; _>_; _≟_)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Product using (∃; ∃-syntax; Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.List    using (List; []; _∷_; [_]; _++_; length)
open import Data.Fin     using ()
  renaming (zero to 0ᶠ; suc to sucᶠ)
open import Data.String  using ()
  renaming (length to lengthₛ)

open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (True; fromWitness; toWitness)
open import Relation.Binary using (Decidable)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

import Prelude.Set' as SET
open import Prelude.Lists

open import BitML.BasicTypes

module BitML.Semantics.Configurations.DecidableEquality
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))
  where

open import BitML.Contracts.Types                     Participant _≟ₚ_ Honest
open import BitML.Contracts.DecidableEquality         Participant _≟ₚ_ Honest
open import BitML.Semantics.Actions.Types             Participant _≟ₚ_ Honest
open import BitML.Semantics.Actions.DecidableEquality Participant _≟ₚ_ Honest
open import BitML.Semantics.Configurations.Types      Participant _≟ₚ_ Honest

-------------------------------------------------------------------

-- Secret lengths.
_≟ₛₗ_ : Decidable {A = Maybe ℕ} _≡_
just x  ≟ₛₗ just y  with x ≟ y
... | no ¬p    = no λ{ refl → ¬p refl }
... | yes refl = yes refl
just _  ≟ₛₗ nothing = no λ ()
nothing ≟ₛₗ just _  = no λ ()
nothing ≟ₛₗ nothing = yes refl

-- Configurations.
_≟ᶜᶠ_ : Decidable {A = Configuration′ cf′i} _≡_
_∃≟ᶜᶠ_ : Decidable {A = ∃[ cf′i ] Configuration′ cf′i} _≡_

∅ᶜ ≟ᶜᶠ ∅ᶜ            = yes refl
∅ᶜ ≟ᶜᶠ (_ auth[ _ ]∶- _) = no λ ()
∅ᶜ ≟ᶜᶠ ⟨ _ ∶ _ ♯ _ ⟩ = no λ ()
∅ᶜ ≟ᶜᶠ (_ ∶ _ ♯ _)   = no λ ()
∅ᶜ ≟ᶜᶠ (_ ∣∣ _ ∶- _) = no λ ()

(` ad) ≟ᶜᶠ (` .ad)          = yes refl
(` ad) ≟ᶜᶠ (p auth[ x ]∶- _)    = no λ ()
(` ad) ≟ᶜᶠ (c′ ∣∣ c′₁ ∶- x) = no λ ()

⟨ c ⟩ᶜ ≟ᶜᶠ ⟨ .c ⟩ᶜ = yes refl
⟨ c ⟩ᶜ ≟ᶜᶠ (p auth[ x ]∶- _)    = no λ ()
⟨ c ⟩ᶜ ≟ᶜᶠ (c′ ∣∣ c′₁ ∶- x) = no λ ()

⟨ p , v ⟩ᵈ ≟ᶜᶠ ⟨ .p , .v ⟩ᵈ = yes refl
⟨ p , v ⟩ᵈ ≟ᶜᶠ (p₁ auth[ x ]∶- _) = no λ ()
⟨ p , v ⟩ᵈ ≟ᶜᶠ (c′ ∣∣ c′₁ ∶- x) = no λ ()

(_auth[_]∶-_ {ads} {cs} {vs} {ds} p a _) ≟ᶜᶠ
  (_auth[_]∶-_ {ads′} {cs′} {vs′} {ds′} p′ a′ _)
  with ads SETₐ.≟ₗ ads′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl
  with cs SETᶜ.≟ₗ cs′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl
  with vs SETₙ.≟ₗ vs′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl
  with ds SETₑ.≟ₗ ds′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl
  with p SETₚ.≣ p′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl
  with a ≟ᵃᶜ a′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl = yes refl
(p auth[ x ]∶- _) ≟ᶜᶠ ∅ᶜ = no λ ()
(p auth[ x ]∶- _) ≟ᶜᶠ (` ad) = no λ ()
(p auth[ x ]∶- _) ≟ᶜᶠ ⟨ c ⟩ᶜ = no λ ()
(p auth[ x ]∶- _) ≟ᶜᶠ ⟨ p₁ , v ⟩ᵈ = no λ ()
(p auth[ x ]∶- _) ≟ᶜᶠ ⟨ x₁ ∶ s ♯ n ⟩ = no λ ()
(p auth[ x ]∶- _) ≟ᶜᶠ (x₁ ∶ s ♯ n) = no λ ()
(p auth[ x ]∶- _) ≟ᶜᶠ (c′ ∣∣ c′₁ ∶- x₁) = no λ ()

⟨ p ∶ s ♯ n ⟩ ≟ᶜᶠ ⟨ p′ ∶ s′ ♯ n′ ⟩
  with p SETₚ.≣ p′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl
  with s SETₛ.≣ s′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl
  with n ≟ₛₗ n′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl = yes refl
⟨ x ∶ s ♯ n ⟩ ≟ᶜᶠ ∅ᶜ = no λ ()
⟨ x ∶ s ♯ n ⟩ ≟ᶜᶠ (p auth[ x₁ ]∶- _) = no λ ()
⟨ x ∶ s ♯ n ⟩ ≟ᶜᶠ (x₁ ∶ s₁ ♯ n₁) = no λ ()
⟨ x ∶ s ♯ n ⟩ ≟ᶜᶠ (c′ ∣∣ c′₁ ∶- x₁) = no λ ()

(p ∶ s ♯ n) ≟ᶜᶠ (p′ ∶ s′ ♯ n′)
  with p SETₚ.≣ p′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl
  with s SETₛ.≣ s′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl
  with n ≟ n′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl = yes refl
(x ∶ s ♯ n) ≟ᶜᶠ ∅ᶜ = no λ ()
(x ∶ s ♯ n) ≟ᶜᶠ (p auth[ x₁ ]∶- _) = no λ ()
(x ∶ s ♯ n) ≟ᶜᶠ ⟨ x₁ ∶ s₁ ♯ n₁ ⟩ = no λ ()
(x ∶ s ♯ n) ≟ᶜᶠ (c′ ∣∣ c′₁ ∶- x₁) = no λ ()

(_∣∣_∶-_ {adsˡ} {radsˡ}
         {csˡ} {rcsˡ}
         {dsˡ} {rdsˡ}
         {adsʳ} {radsʳ}
         {csʳ} {rcsʳ}
         {dsʳ} {rdsʳ}
         {ads} {rads}
         {cs} {rcs}
         {ds} {rds}
         l r _)
  ≟ᶜᶠ
  (_∣∣_∶-_ {adsˡ′} {radsˡ′}
           {csˡ′} {rcsˡ′}
           {dsˡ′} {rdsˡ′}
           {adsʳ′} {radsʳ′}
           {csʳ′} {rcsʳ′}
           {dsʳ′} {rdsʳ′}
           {ads′} {rads′}
           {cs′} {rcs′}
           {ds′} {rds′}
         l′ r′ _)
  with ads SETₐ.≟ₗ ads′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl
  with adsˡ SETₐ.≟ₗ adsˡ′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl
  with adsʳ SETₐ.≟ₗ adsʳ′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl
  with rads SETₐ.≟ₗ rads′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl
  with radsˡ SETₐ.≟ₗ radsˡ′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl
  with radsʳ SETₐ.≟ₗ radsʳ′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl
  with cs SETᶜ.≟ₗ cs′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl
  with csˡ SETᶜ.≟ₗ csˡ′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl
  with csʳ SETᶜ.≟ₗ csʳ′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl
  with rcs SETᶜ.≟ₗ rcs′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl
  with rcsˡ SETᶜ.≟ₗ rcsˡ′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl
  with rcsʳ SETᶜ.≟ₗ rcsʳ′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl
  with ds SETₑ.≟ₗ ds′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl
  with dsˡ SETₑ.≟ₗ dsˡ′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl
  with dsʳ SETₑ.≟ₗ dsʳ′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl
  with rds SETₑ.≟ₗ rds′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl
  with rdsˡ SETₑ.≟ₗ rdsˡ′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl
  with rdsʳ SETₑ.≟ₗ rdsʳ′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl
  with l ≟ᶜᶠ l′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl
  with r ≟ᶜᶠ r′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl = yes refl
(c ∣∣ c₁ ∶- x) ≟ᶜᶠ ∅ᶜ = no λ ()
(c ∣∣ c₁ ∶- x) ≟ᶜᶠ (` ad) = no λ ()
(c ∣∣ c₁ ∶- x) ≟ᶜᶠ ⟨ c₂ ⟩ᶜ = no λ ()
(c ∣∣ c₁ ∶- x) ≟ᶜᶠ ⟨ p , v ⟩ᵈ = no λ ()
(c ∣∣ c₁ ∶- x) ≟ᶜᶠ (p auth[ x₁ ]∶- _) = no λ ()
(c ∣∣ c₁ ∶- x) ≟ᶜᶠ ⟨ x₁ ∶ s ♯ n ⟩ = no λ ()
(c ∣∣ c₁ ∶- x) ≟ᶜᶠ (x₁ ∶ s ♯ n) = no λ ()

(Iᶜᶠ[ (ads , rads) , (cs , rcs) , (ds , rds) ] , c) ∃≟ᶜᶠ
  (Iᶜᶠ[ (ads′ , rads′) , (cs′ , rcs′) , (ds′ , rds′) ] , c′)
  with ads SETₐ.≟ₗ ads′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl
  with rads SETₐ.≟ₗ rads′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl
  with cs SETᶜ.≟ₗ cs′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl
  with rcs SETᶜ.≟ₗ rcs′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl
  with ds SETₑ.≟ₗ ds′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl
  with rds SETₑ.≟ₗ rds′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl
  with c ≟ᶜᶠ c′
... | no ¬p    = no λ{refl →  ¬p refl}
... | yes refl = yes refl

module SETᶜᶠ = SET _∃≟ᶜᶠ_
Set⟨Configuration⟩ : Set
Set⟨Configuration⟩ = Set' where open SETᶜᶠ
