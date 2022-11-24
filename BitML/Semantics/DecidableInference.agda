------------------------------------------------------------------------
-- Decision procedure for BitML's small-step semantics.
------------------------------------------------------------------------
open import Prelude.Init
open import Prelude.General
open import Prelude.Lists.Core using (unzip₃)
open import Prelude.Lists.Indexed using (Index)
open import Prelude.DecLists
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Membership
open import Prelude.Sets
open import Prelude.Setoid
open import Prelude.Validity
open import Prelude.Ord
open import Prelude.Nary hiding (⟦_⟧)
open import Prelude.InferenceRules
open import Prelude.Indexable
open import Prelude.Null

open import BitML.BasicTypes
open import BitML.Predicate hiding (`; ∣_∣)

module BitML.Semantics.DecidableInference
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import BitML.Contracts.Types Participant Honest hiding (d)
open import BitML.Contracts.Helpers Participant Honest
open import BitML.Contracts.Validity Participant Honest
open import BitML.Semantics.Action Participant Honest
open import BitML.Semantics.Configurations.Types Participant Honest
open import BitML.Semantics.Configurations.Helpers Participant Honest
open import BitML.Semantics.Label Participant Honest
open import BitML.Semantics.Predicate Participant Honest
open import BitML.Semantics.InferenceRules Participant Honest

DEP-Join :
  ∀ {p : auto∶ z ∉ˢ x ∷ˢ y ∷ˢ ids Γ} →
  ────────────────────────────────────────────────────────────────────────
  ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at y ∣ A auth[ x ↔ y ▷⟨ A , v + v′ ⟩ ] ∣ Γ
    —[ join⦅ x ↔ y ⦆ ]→
  ⟨ A has (v + v′) ⟩at z ∣ Γ
DEP-Join {p = p} = [DEP-Join] (toWitness p)

DEP-Divide :
  ∀ {p : auto∶ All (_∉ˢ x ∷ˢ ids Γ) (y ∷ y′ ∷ [])} →
  ────────────────────────────────────────────────────────
  ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ] ∣ Γ
    —[ divide⦅ x ▷ v , v′ ⦆ ]→
  ⟨ A has v ⟩at y ∣ ⟨ A has v′ ⟩at y′ ∣ Γ
DEP-Divide {p = p} = [DEP-Divide] (toWitness p)

DEP-Donate :
  ∀ {p : auto∶ y ∉ˢ x ∷ˢ ids Γ} →
  ──────────────────────────────────────
  ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B ] ∣ Γ
    —[ donate⦅ x ▷ᵈ B ⦆ ]→
  ⟨ B has v ⟩at y ∣ Γ
DEP-Donate {p = p} = [DEP-Donate] (toWitness p)

DEP-AuthDestroy :
  ∀ {xs : Ids} {get-ds : Ix xs → Participant × Value} {j : Ix xs} →
  let Aⱼ = get-ds j .proj₁
      ds = mapWithIxˢ xs λ x i → let A , v = get-ds i in  A , v , x
      Δ  = || map (uncurry₃ ⟨_has_⟩at_) ds
  in
  ∀ {p : auto∶ y ∉ˢ ids Γ} →
  ──────────────────────────────────────────────────────────────
  Δ ∣ Γ
    —[ auth-destroy⦅ Aⱼ , xs , j ⦆ ]→
  Δ ∣ Aⱼ auth[ xs , j ▷ᵈˢ y ] ∣ Γ
DEP-AuthDestroy {p = p} = [DEP-AuthDestroy] (toWitness p)

C-Advertise : let ⟨ G ⟩ _ = ad; partG = participants G in
  ∀ {p₁ : auto∶ ValidAdvertisement ad} -- [BUG] Valid ad (order matters!)
    {p₂ : auto∶ Anyˢ (_∈ Hon) partG}
    {p₃ : auto∶ deposits ad ⊆ˢ deposits Γ} →
  ────────────────────────────────────────────────────────────
  Γ —[ advertise⦅ ad ⦆ ]→ ` ad ∣ Γ
C-Advertise {p₁ = p₁} {p₂} {p₃} = [C-Advertise] (toWitness p₁) (toWitness p₂) (toWitness p₃)

C-AuthCommit : let ⟨ G ⟩ _ = ad; as = secretsOfᵖ A G in
  ∀ {get-n : Ix as → Maybe ℕ} →
  let secrets  = mapWithIxˢ as λ a i → a , get-n i
      Δ        = || map (uncurry ⟨ A ∶_♯_⟩) secrets
      (_ , ms) = unzip secrets
  in
  {p₁ : auto∶ Allˢ (_∉ˢ secretsOfᶜᶠ A Γ) as}
  {p₂ : auto∶ (A ∈ Hon → All Is-just ms)} →
  ` ad ∣ Γ —[ auth-commit⦅ A , ad , secrets ⦆ ]→ ` ad ∣ Γ ∣ Δ ∣ A auth[ ♯▷ ad ]
C-AuthCommit {p₁ = p₁} {p₂} = [C-AuthCommit] (toWitness p₁) (toWitness p₂)

C-AuthInit : let ⟨ G ⟩ _ = ad; partG = participants G in
  ∀ {p₁ : auto∶ partG ⊆ˢ committedParticipants ad Γ}
    {p₂ : auto∶ (A , v , x) ∈ˢ persistentDeposits G}
  → ` ad ∣ Γ —[ auth-init⦅ A , ad , x ⦆ ]→ ` ad ∣ Γ ∣ A auth[ x ▷ˢ ad ]
C-AuthInit {p₁ = p₁} {p₂} = [C-AuthInit] (toWitness p₁) (toWitness p₂)

C-Init : let ⟨ G ⟩ C = ad; partG = participants G in
  let toSpend = persistentDeposits G
      vs      = mapˢ select₂ toSpend
      xs      = mapˢ select₃ toSpend
  in
  ∀ {p : auto∶ x ∉ˢ xs ∪ ids Γ } →
  ` ad
  ∣ Γ
  ∣ ||ˢ mapˢ (λ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ ad ]) toSpend
  ∣ ||ˢ mapˢ _auth[ ♯▷ ad ] partG
    —[ init⦅ G , C ⦆ ]→
  ⟨ C , sumˢ vs ⟩at x ∣ Γ
C-Init {p = p} = [C-Init] (toWitness p)

C-Split :
  ∀ {vcis : List (Value × Contracts × Id)} →
  let (vs , cs , ys) = unzip₃ vcis in
  ∀ {p : auto∶ All (_∉ˢ y ∷ˢ ids Γ) ys} →
  ──────────────────────────────────────────
  ⟨ [ split (zip vs cs) ] , sum vs ⟩at y ∣ Γ
    —[ split⦅ y ⦆ ]→
  || map (uncurry₃ $ flip ⟨_,_⟩at_) vcis ∣ Γ
C-Split {vcis = vcis} {p = p} = [C-Split] {vcis = vcis} (toWitness p)

C-PutRev :
  ∀ {xs : Ids} {as : Secrets}
    {get-ds : Ix xs → Participant × Value} {get-ss : Ix as → Participant × ℕ} →
  let ds = mapWithIxˢ xs λ x i → let A , v = get-ds i in A , v , x
      ss = mapWithIxˢ as λ a i → let A , n = get-ss i in A , a , n
      (_ , vs , _) = unzip₃ ds
      Γ = || map (uncurry₃ ⟨_has_⟩at_) ds
      Δ = || map (uncurry₃ _∶_♯_) ss
      ΔΓ′ = Δ ∣ Γ′
  in
  {p₀ : auto∶ z ∉ˢ y ∷ˢ ids (Γ ∣ ΔΓ′)}
  {p₁ : auto∶ ⟦ p ⟧ Δ ≡ just true} →
  ⟨ [ put xs &reveal as if p ⇒ c ] , v ⟩at y ∣ (Γ ∣ ΔΓ′)
    —[ put⦅ xs , as , y ⦆ ]→
  ⟨ c , v + sum vs ⟩at z ∣ ΔΓ′
C-PutRev {get-ds = get-ds}{get-ss}{p₀}{p₁} =
  [C-PutRev] {get-ds = get-ds} {get-ss = get-ss} (toWitness p₀) (toWitness p₁)

C-Withdraw :
  ∀ {p : auto∶ x ∉ˢ y ∷ˢ ids Γ} →
  ⟨ [ withdraw A ] , v ⟩at y ∣ Γ
    —[ withdraw⦅ A , v , y ⦆ ]→
  ⟨ A has v ⟩at x ∣ Γ
C-Withdraw {p = p} = [C-Withdraw] (toWitness p)

C-AuthControl :
  ∀ {i : Ix c}
  → let d = c ‼ i in
    {p₁ : auto∶ A ∈ˢ authDecorations d}
  → ⟨ c , v ⟩at x ∣ Γ —[ auth-control⦅ A , x ▷ d ⦆ ]→ ⟨ c , v ⟩at x ∣ A auth[ x ▷ d ] ∣ Γ
C-AuthControl {p₁ = p₁} = [C-AuthControl] (toWitness p₁)

-- T0D0 can we decide which transition to choose?
-- _—→?[_]_ : (Γ : Configuration) → (α : Label) → (Γ′ : Configuration) → Dec (Γ —→[ α ] Γ′)
-- Γ —→?[ α ] Γ′ = ?

C-Control :
  ∀ {i : Index c} → let open ∣SELECT c i; As = authDecorations d in

    {p₀ : auto∶ ¬Null (authDecorations d) ⊎ (length c > 1)}
  → {p₁ : auto∶ Γ ≈ L}
  → ⟨ [ d∗ ] , v ⟩at x ∣ L —[ α ]→ Γ′
  → {p₂ : auto∶ cv α ≡ just x}
  → ⟨ c , v ⟩at x ∣ ||ˢ mapˢ _auth[ x ▷ d ] (authDecorations d) ∣ Γ —[ α ]→ Γ′
C-Control {p₀ = p₀}{p₁} L—→Γ′ {p₂} = [C-Control] (toWitness p₀) (toWitness p₁) L—→Γ′ (toWitness p₂)

Act :
  ∀ {p : auto∶ cv α ≡ nothing} →
  ∙ Γ —[ α ]→ Γ′
    ───────────────────────
    Γ at t —[ α ]→ₜ Γ′ at t
Act {p = p} = flip [Action] (toWitness p)

Delay :
  ∀ {p : True $ δ >? 0} →
  ─────────────────────────────────────
  Γ at t —[ delay⦅ δ ⦆ ]→ₜ Γ at (t + δ)
Delay {p = p} = [Delay] (toWitness p)

Timeout :
  ∀ {i : Index c} → let open ∣SELECT c i; As , ts = decorations d in

  ∀ {p₁ : auto∶ As ≈ˢ ∅} -- Null As
    {p₂ : auto∶ Allˢ (_≤ t) ts}
    {p₃ : auto∶ cv α ≡ just x} →

  ⟨ [ d∗ ] , v ⟩at x ∣ Γ —[ α ]→ Γ′
  ──────────────────────────────────────────────────────────────────────────────
  (⟨ c , v ⟩at x ∣ Γ) at t —[ α ]→ₜ Γ′ at t
Timeout {p₁ = p₁}{p₂}{p₃} Γ→ =
  [Timeout] (toWitness p₁) (toWitness p₂) Γ→ (toWitness p₃)
