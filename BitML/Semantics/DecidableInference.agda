------------------------------------------------------------------------
-- Decision procedure for BitML's small-step semantics.
------------------------------------------------------------------------

open import Function using (_∘_)

open import Data.Empty   using (⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Bool    using (true)
  renaming (_≟_ to _≟ᵇ_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Nat     using (ℕ; _>_; _+_; _≤_)
open import Data.Maybe   using (Maybe; Is-just; just; nothing)
open import Data.List    using (List; []; _∷_; [_]; _++_; map; length; zip; unzip)

open import Data.Maybe.Properties         using (≡-dec)
open import Data.Maybe.Relation.Unary.Any using ()
  renaming (dec to anyₘ)

open import Data.List.Membership.Propositional       using (_∈_; _∉_)
open import Data.List.Relation.Unary.All             using (All; all)
open import Data.List.Relation.Unary.Any             using (Any; any)
open import Data.List.Relation.Permutation.Inductive using (_↭_)

open import Relation.Nullary                      using (Dec; yes; no)
open import Relation.Nullary.Decidable            using (True; toWitness)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Prelude.Lists

open import BitML.BasicTypes
open import BitML.Predicate.Base hiding (`; ∣_∣)

module BitML.Semantics.DecidableInference
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))
  where

open import BitML.Contracts.Types                  Participant _≟ₚ_ Honest
open import BitML.Contracts.Helpers                Participant _≟ₚ_ Honest
open import BitML.Contracts.Validity               Participant _≟ₚ_ Honest
open import BitML.Contracts.DecidableEquality      Participant _≟ₚ_ Honest
open import BitML.Semantics.Actions.Types          Participant _≟ₚ_ Honest
open import BitML.Semantics.Configurations.Types   Participant _≟ₚ_ Honest
open import BitML.Semantics.Configurations.Helpers Participant _≟ₚ_ Honest
open import BitML.Semantics.Labels.Types           Participant _≟ₚ_ Honest
open import BitML.Semantics.Predicate              Participant _≟ₚ_ Honest
open import BitML.Semantics.InferenceRules         Participant _≟ₚ_ Honest

C-Advertise :
  ∀ {p₁ : True (validAd? ad)}
    {p₂ : True (any (SETₚ._∈? Hon) (participantsᵖ (G ad)))}
    {p₃ : True (all (SETₑ._∈? depositsᶜ Γ) (depositsᵃ ad))}
  → Γ —→[ advertise[ ad ] ] ` ad ∣ Γ
C-Advertise {p₁ = p₁} {p₂} {p₃} = [C-Advertise] (toWitness p₁) (toWitness p₂) (toWitness p₃)

C-AuthInit :
  ∀ {p₁ : True (all (SETₚ._∈? committedParticipants Γ ad) (participantsᵖ (G ad)))}
    {p₂ : True ((A , v , x) SETₑ.∈? persistentDepositsᵖ (G ad))}
  → ` ad ∣ Γ —→[ auth-init[ A , ad , x ] ] ` ad ∣ Γ ∣ A auth[ x ▷ˢ ad ]
C-AuthInit {p₁ = p₁} {p₂} = [C-AuthInit] (toWitness p₁) (toWitness p₂)

C-PutRev :
  ∀ {ds : List (Participant × Value × Id)}
    {ss : List (Participant × Secret × ℕ)}
  → let (_ , vs , xs) = unzip₃ ds
        (_ , as , _)  = unzip₃ ss
        Γ = || map (λ{ (Ai , vi , xi) → ⟨ Ai has vi ⟩at xi}) ds
        Δ = || map (λ{ (Bi , ai , Ni) → Bi ∶ ai ♯ Ni}) ss
    in
    {p₁ : True (≡-dec _≟ᵇ_ (⟦ p ⟧ Δ) (just true))}
  → ⟨ [ put xs &reveal as if p ⇒ c ] , v ⟩at y ∣ Γ ∣ Δ ∣ Γ′ —→[ put[ xs , as , y ] ] ⟨ c , v + sum vs ⟩at z ∣ Δ ∣ Γ′
C-PutRev {ds = ds} {ss = ss} {p₁ = p₁} = [C-PutRev] {ds = ds} {ss = ss} (toWitness p₁)

C-AuthControl :
  ∀ {i : Index c}
  → let d = c ‼ i in
    {p₁ : True (A SETₚ.∈? authDecorations d)}
  → ⟨ c , v ⟩at x ∣ Γ —→[ auth-control[ A , x ▷ d ] ] ⟨ c , v ⟩at x ∣ A auth[ x ▷ d ] ∣ Γ
C-AuthControl {p₁ = p₁} = [C-AuthControl] (toWitness p₁)

_→?_ : ∀ {P Q : Set} → Dec P → Dec Q → Dec (P → Q)
P? →? Q?    with P?
... | no ¬P = yes λ P → ⊥-elim (¬P P)
... | yes P with Q?
... | no ¬Q = no  λ P→Q → ⊥-elim (¬Q (P→Q P))
... | yes Q = yes λ _ → Q

C-AuthCommit :
  ∀ {secrets : List (Secret × Maybe ℕ)}
  → let (as , ms) = unzip secrets
        Δ         = || map (λ{ (ai , Ni) → ⟨ A ∶ ai ♯ Ni ⟩}) secrets
    in
    {p₁ : True (as SETₛ.≟ₗ secretsᵖ A (G ad))}
  → {p₂ : True (all (SETₛ._∉? secretsᶜ A Γ) as)}
  → {p₃ : True ((A SETₚ.∈? Hon) →? all (anyₘ λ _ → yes tt) ms)}
  → ` ad ∣ Γ —→[ auth-commit[ A , ad , secrets ] ] ` ad ∣ Γ ∣ Δ ∣ A auth[ ♯▷ ad ]
C-AuthCommit {p₁ = p₁} {p₂} {p₃} = [C-AuthCommit] (toWitness p₁) (toWitness p₂) (toWitness p₃)

-- T0D0 can we decide which transition to choose?
-- _—→?[_]_ : (Γ : Configuration) → (α : Label) → (Γ′ : Configuration) → Dec (Γ —→[ α ] Γ′)
-- Γ —→?[ α ] Γ′ = ?

C-Control :
  ∀ {i : Index c}
  → let d  = c ‼ i
        d′ = removeTopDecorations d
        As = authDecorations d
    in

    {p₁ : True (⟨ [ d′ ] , v ⟩at x ∣ Γ ≈? L)}
  → L —→[ α ] Γ′
  → {p₂ : True (≡-dec _≟ₛ_ (cv α) (just x))}
  → ⟨ c , v ⟩at x ∣ || map _auth[ x ▷ d ] As ∣ Γ —→[ α ] Γ′
C-Control {p₁ = p₁} L—→Γ′ {p₂} = [C-Control] (toWitness p₁) L—→Γ′ (toWitness p₂)
