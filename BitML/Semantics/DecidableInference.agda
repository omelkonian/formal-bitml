------------------------------------------------------------------------
-- Decision procedure for BitML's small-step semantics.
------------------------------------------------------------------------
open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Sets

open import BitML.BasicTypes
open import BitML.Predicate hiding (`; ∣_∣)

module BitML.Semantics.DecidableInference
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import BitML.Contracts.Types Participant Honest
open import BitML.Contracts.Helpers Participant Honest
open import BitML.Contracts.Validity Participant Honest
open import BitML.Semantics.Action Participant Honest
open import BitML.Semantics.Configurations.Types Participant Honest
open import BitML.Semantics.Configurations.Helpers Participant Honest
open import BitML.Semantics.Label Participant Honest
open import BitML.Semantics.Predicate Participant Honest
open import BitML.Semantics.InferenceRules Participant Honest

C-Advertise :
  ∀ {p₁ : True (validAd? ad)}
    {p₂ : True (any? (_∈? Hon) (participants (G ad)))}
    {p₃ : True (deposits ad ⊆? deposits Γ)}
  → Γ —→[ advertise[ ad ] ] ` ad ∣ Γ
C-Advertise {p₁ = p₁} {p₂} {p₃} = [C-Advertise] (toWitness p₁) (toWitness p₂) (toWitness p₃)

C-AuthInit :
  ∀ {p₁ : True (all? (_∈? committedParticipants Γ ad) (nub-participants $ G ad))}
    {p₂ : True ((A , v , x) ∈? persistentDeposits (G ad))}
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
    {p₁ : True (⟦ p ⟧ Δ ≟ just true)}
  → ⟨ [ put xs &reveal as if p ⇒ c ] , v ⟩at y ∣ Γ ∣ Δ ∣ Γ′ —→[ put[ xs , as , y ] ] ⟨ c , v + sum vs ⟩at z ∣ Δ ∣ Γ′
C-PutRev {ds = ds} {ss = ss} {p₁ = p₁} = [C-PutRev] {ds = ds} {ss = ss} (toWitness p₁)

C-AuthControl :
  ∀ {i : Index c}
  → let d = c ‼ i in
    {p₁ : True (A ∈? authDecorations d)}
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
    {p₁ : True (as ≟ secretsOfᵖ A (G ad))}
  → {p₂ : True (all? (_∉? secretsOfᶜᶠ A Γ) as)}
  → {p₃ : True ((A ∈? Hon) →? all? (M.Any.dec λ _ → yes tt) ms)}
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
  → {p₂ : True (cv α ≟ just x)}
  → ⟨ c , v ⟩at x ∣ || map _auth[ x ▷ d ] (nub (authDecorations d)) ∣ Γ —→[ α ] Γ′
C-Control {p₁ = p₁} L—→Γ′ {p₂} = [C-Control] (toWitness p₁) L—→Γ′ (toWitness p₂)
