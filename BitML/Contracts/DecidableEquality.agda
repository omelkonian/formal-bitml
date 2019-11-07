------------------------------------------------------------------------
-- Decidable equality for contracts and advertisements
------------------------------------------------------------------------

open import Level        using (0ℓ)
open import Function     using (_∘_)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (tt; ⊤)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃₂; ∃-syntax; Σ; Σ-syntax)
open import Data.Bool    using (T; true; false)
  renaming (_≟_ to _≟ᵇ_)
open import Data.Nat     using (ℕ; zero; suc; _<_; _>_; _+_; _∸_; _≤_; z≤n; s≤s; _≤?_; _≥?_; _≟_)
open import Data.List    using (List; []; _∷_; [_]; _++_; map; concatMap; length; filter)

open import Data.String.Properties using ()
  renaming (_≟_ to _≟ₛₜᵣ_)

open import Data.List.Any            using (Any; any; here; there)
open import Data.List.Any.Properties using (any⁺)

open import Data.Vec.Relation.Binary.Equality.DecPropositional using (_≋?_; ≋⇒≡; ≡⇒≋)


open import Relation.Nullary           using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; toWitness; fromWitness; True; map′)
open import Relation.Binary            using (Decidable)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂)

open import Category.Functor using (RawFunctor)
open import Data.List.Categorical renaming (functor to listFunctor)
open RawFunctor {0ℓ} listFunctor using (_<$>_)

import Prelude.Set' as SET
open import Prelude.Lists

open import BitML.BasicTypes
open import BitML.Predicate.DecidableEquality

module BitML.Contracts.DecidableEquality
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))
  where

open import BitML.Contracts.Types Participant _≟ₚ_ Honest

------------------------------------------------------------------------

import Prelude.Set' as SET

-- Sets of deposits
_≟ₑ_ : Decidable {A = Deposit} _≡_
x ≟ₑ y with participant x ≟ₚ participant y
          | value       x ≟  value       y
... | no ¬p    | _        = no λ{refl → ¬p refl}
... | _        | no ¬p    = no λ{refl → ¬p refl}
... | yes refl | yes refl = yes refl

module SETₑ = SET {A = Deposit} _≟ₑ_

Set⟨Deposit⟩ : Set
Set⟨Deposit⟩ = Set'
  where open SETₑ

-- Sets of deposit references
_≟ₑᵣ_ : Decidable {A = DepositRef} _≡_
x ≟ₑᵣ y with deposit    x ≟ₑ deposit    y
           | persistent x ≟ᵇ persistent y
... | no ¬p    | _        = no λ{refl → ¬p refl}
... | _        | no ¬p    = no λ{refl → ¬p refl}
... | yes refl | yes refl = yes refl

module SETₑᵣ = SET {A = DepositRef} _≟ₑᵣ_

Set⟨DepositRef⟩ : Set
Set⟨DepositRef⟩ = Set'
  where open SETₑᵣ

-- Contracts.
_≟ᶜˢ_ : Decidable {A = Contracts ci} _≡_
_∃≟ᶜˢ_ : Decidable {A = ∃Contracts} _≡_

-- NB: mutual recursion needed  here to satisfy the termination checker
_≟ᶜ_ : Decidable {A = Contract ci} _≡_
_∃s≟ᶜ′_ : Decidable {A = List (∃[ v ] Contract Iᶜ[ v , vs ])} _≡_
_∃s≟ᶜ_ : Decidable {A = List ∃Contract} _≡_

[]                  ∃s≟ᶜ []                      = yes refl
[]                  ∃s≟ᶜ (_ ∷ _)                 = no λ ()
(_ ∷ _)             ∃s≟ᶜ []                      = no λ ()
((Iᶜ[ v , vs ] , c) ∷ cs) ∃s≟ᶜ ((Iᶜ[ v′ , vs′ ] , c′) ∷ cs′) with v ≟ v′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with vs SETₙ.≟ₗ vs′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with c ≟ᶜ c′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with cs ∃s≟ᶜ cs′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl

[]             ∃s≟ᶜ′ []                = yes refl
[]             ∃s≟ᶜ′ (_ ∷ _)           = no λ ()
(_ ∷ _)        ∃s≟ᶜ′ []                = no λ ()
((v , c) ∷ cs) ∃s≟ᶜ′ ((v′ , c′) ∷ cs′) with v ≟ v′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with c ≟ᶜ c′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with cs ∃s≟ᶜ′ cs′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl

put_&reveal_if_⇒_∶-_ {n = n} {v′ = v} {vs′ = vss} vs ss p c _ ≟ᶜ
 put_&reveal_if_⇒_∶-_ {n = n′} {v′ = v′} {vs′ = vss′} vs′ ss′ p′ c′ _
               with n ≟ n′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with vs SETₙ.≟ₗ vs′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with map′ ≋⇒≡ ≡⇒≋ (_≋?_ _≟ₛₜᵣ_ ss ss′)
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with p ≟ᵖʳ p′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with v ≟ v′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with vss SETₙ.≟ₗ vss′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with c ≟ᶜˢ c′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl
(put _ &reveal _ if _ ⇒ _ ∶- _) ≟ᶜ withdraw _     = no λ ()
(put _ &reveal _ if _ ⇒ _ ∶- _) ≟ᶜ (split _ ∶- _) = no λ ()
(put _ &reveal _ if _ ⇒ _ ∶- _) ≟ᶜ (_ ∶ _)        = no λ ()
(put _ &reveal _ if _ ⇒ _ ∶- _) ≟ᶜ (after _ ∶ _)  = no λ ()

withdraw x ≟ᶜ withdraw x′ with x ≟ₚ x′
... | no ¬p = no λ{refl → ¬p refl}
... | yes refl = yes refl
withdraw x ≟ᶜ (put _ &reveal _ if _ ⇒ _ ∶- _)       = no λ ()
withdraw x ≟ᶜ (split _ ∶- _)                        = no λ ()
withdraw x ≟ᶜ (_ ∶ _)                               = no λ ()
withdraw x ≟ᶜ (after _ ∶ _)                         = no λ ()

(split cs ∶- _) ≟ᶜ (split cs′ ∶- _) with cs ∃s≟ᶜ′ cs′
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

_∃≟ᶜ_ : Decidable {A = ∃[ ci ] Contract ci} _≡_
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

(Iᶜ[ v , vs ] , cs) ∃≟ᶜˢ (Iᶜ[ v′ , vs′ ] , cs′) with v ≟ v′
... | no ¬p = no λ{refl → ¬p refl}
... | yes refl with vs SETₙ.≟ₗ vs′
... | no ¬p = no λ{refl → ¬p refl}
... | yes refl with cs ≟ᶜˢ cs′
... | no ¬p = no λ{refl → ¬p refl}
... | yes refl = yes refl

module SETᶜ = SET _∃≟ᶜˢ_
Set⟨Contracts⟩ : Set
Set⟨Contracts⟩ = Set' where open SETᶜ

-- Sets of preconditions.
_≟ₚᵣ_ : Decidable {A = Precondition pi} _≡_
(x :? v)      ≟ₚᵣ (x′ :? v′)      with x ≟ₚ x′
... | no x≢x′                     = no λ{refl → x≢x′ refl}
... | yes refl                    with v ≟ v′
... | no v≢v′                     = no λ{refl → v≢v′ refl}
... | yes refl                    = yes refl
(_ :? _)      ≟ₚᵣ (_ ∣ _ ∶- _)    = no λ ()

(x :! v)      ≟ₚᵣ (x′ :! v′)      with x ≟ₚ x′
... | no x≢x′                     = no λ{refl → x≢x′ refl}
... | yes refl                    with v ≟ v′
... | no v≢v′                     = no λ{refl → v≢v′ refl}
... | yes refl                    = yes refl
(_ :! _)      ≟ₚᵣ (_ ∣ _ ∶- _)         = no λ ()

(x :secret s) ≟ₚᵣ (x′ :secret s′) with x ≟ₚ x′
... | no x≢x′                     = no λ{refl → x≢x′ refl}
... | yes refl                    with s ≟ₛ s′
... | no s≢s′                     = no λ{refl → s≢s′ refl}
... | yes refl                    = yes refl
(_ :secret _) ≟ₚᵣ (_ ∣ _ ∶- _)         = no λ ()

(_∣_∶-_ {vsᵛₗ = vsᵛₗ} {vsᵖₗ = vsᵖₗ} {vsᵛᵣ = vsᵛᵣ} {vsᵖᵣ = vsᵖᵣ} p₁ p₂ _) ≟ₚᵣ
  (_∣_∶-_ {vsᵛₗ = vsᵛₗ′} {vsᵖₗ = vsᵖₗ′} {vsᵛᵣ = vsᵛᵣ′} {vsᵖᵣ = vsᵖᵣ′} p₁′ p₂′ _)
                                  with vsᵛₗ SETₙ.≟ₗ vsᵛₗ′
... | no ¬p                       = no λ{refl → ¬p refl}
... | yes refl                    with vsᵛᵣ SETₙ.≟ₗ vsᵛᵣ′
... | no ¬p                       = no λ{refl → ¬p refl}
... | yes refl                    with vsᵖₗ SETₙ.≟ₗ vsᵖₗ′
... | no ¬p                       = no λ{refl → ¬p refl}
... | yes refl                    with vsᵖᵣ SETₙ.≟ₗ vsᵖᵣ′
... | no ¬p                       = no λ{refl → ¬p refl}
... | yes refl                    with p₁ ≟ₚᵣ p₁′
... | no ¬p                       = no λ{refl → ¬p refl}
... | yes refl                    with p₂ ≟ₚᵣ p₂′
... | no ¬p                       = no λ{refl → ¬p refl}
... | yes refl                    = yes refl
(_ ∣ _ ∶- _)  ≟ₚᵣ (_ :? _)        = no λ ()
(_ ∣ _ ∶- _)  ≟ₚᵣ (_ :! _)        = no λ ()
(_ ∣ _ ∶- _)  ≟ₚᵣ (_ :secret _)   = no λ ()

-- Advertisements.
_≟ₐ_ : Decidable {A = Advertisement ci pi} _≡_
(⟨ G₁ ⟩ C₁ ∶- _) ≟ₐ (⟨ G₂ ⟩ C₂ ∶- _) with G₁ ≟ₚᵣ G₂
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with C₁ ≟ᶜˢ C₂
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl

_∃≟ₐ_ : Decidable {A = ∃Advertisement} _≡_
(Iᶜ[ v , vsᶜ ] , Iᵖ[ vsᵛ , vsᵖ ] , ad) ∃≟ₐ (Iᶜ[ v′ , vsᶜ′ ] , Iᵖ[ vsᵛ′ , vsᵖ′ ] , ad′) with v ≟ v′
... | no ¬p = no λ{refl → ¬p refl}
... | yes refl with vsᶜ SETₙ.≟ₗ vsᶜ′
... | no ¬p = no λ{refl → ¬p refl}
... | yes refl with vsᵛ SETₙ.≟ₗ vsᵛ′
... | no ¬p = no λ{refl → ¬p refl}
... | yes refl with vsᵖ SETₙ.≟ₗ vsᵖ′
... | no ¬p = no λ{refl → ¬p refl}
... | yes refl with ad ≟ₐ ad′
... | no ¬p = no λ{refl → ¬p refl}
... | yes refl = yes refl

module SETₐ = SET _∃≟ₐ_
Set⟨Advertisement⟩ : Set
Set⟨Advertisement⟩ = Set' where open SETₐ
