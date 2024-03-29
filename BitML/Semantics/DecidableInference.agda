------------------------------------------------------------------------
-- Decision procedure for BitML's small-step semantics.
------------------------------------------------------------------------
open import Prelude.Init; open SetAsType
open L.Mem
open import Prelude.Lists.Core
open import Prelude.Lists.Dec
open import Prelude.Lists.Indexed
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Setoid
open import Prelude.Ord
open import Prelude.Nary
open import Prelude.InferenceRules
open import Prelude.Null

open import BitML.BasicTypes
open import BitML.Predicate

module BitML.Semantics.DecidableInference (⋯ : ⋯) (let open ⋯ ⋯) where

open import BitML.Contracts ⋯ hiding (d)
open import BitML.Semantics.Action ⋯
open import BitML.Semantics.Configurations.Types ⋯
open import BitML.Semantics.Configurations.Helpers ⋯
open import BitML.Semantics.Label ⋯
open import BitML.Semantics.Predicate ⋯
open import BitML.Semantics.InferenceRules ⋯

DEP-Join :
  ∀ {p : auto∶ z ∉ x ∷ y ∷ ids Γ} →
  ────────────────────────────────────────────────────────────────────────
  ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at y ∣ A auth[ x ↔ y ▷⟨ A , v + v′ ⟩ ] ∣ Γ
    —[ join⦅ x ↔ y ⦆ ]→
  ⟨ A has (v + v′) ⟩at z ∣ Γ
DEP-Join {p = p} = [DEP-Join] (toWitness p)

DEP-Divide :
  ∀ {p : auto∶ All (_∉ x ∷ ids Γ) [ y ⨾ y′ ]} →
  ────────────────────────────────────────────────────────
  ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ] ∣ Γ
    —[ divide⦅ x ▷ v , v′ ⦆ ]→
  ⟨ A has v ⟩at y ∣ ⟨ A has v′ ⟩at y′ ∣ Γ
DEP-Divide {p = p} = [DEP-Divide] (toWitness p)

DEP-Donate :
  ∀ {p : auto∶ y ∉ x ∷ ids Γ} →
  ──────────────────────────────────────
  ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B ] ∣ Γ
    —[ donate⦅ x ▷ᵈ B ⦆ ]→
  ⟨ B has v ⟩at y ∣ Γ
DEP-Donate {p = p} = [DEP-Donate] (toWitness p)

DEP-AuthDestroy :
  ∀ {ds : DepositRefs} {j : Index ds} →
  let xs = map select₃ ds
      Aⱼ = (ds ‼ j) .proj₁
      j′ = ‼-map {xs = ds} j
      Δ  = || map (uncurry₃ ⟨_has_⟩at_) ds
  in
  ∀ {p : auto∶ y ∉ ids Γ} →
  ──────────────────────────────────────────────────────────────
  Δ ∣ Γ
    —[ auth-destroy⦅ Aⱼ , xs , j′ ⦆ ]→
  Δ ∣ Aⱼ auth[ xs , j′ ▷ᵈˢ y ] ∣ Γ
DEP-AuthDestroy {p = p} = [DEP-AuthDestroy] (toWitness p)

C-Advertise : let ⟨ G ⟩ _ = ad; partG = nub-participants G in
  ∀ {p₁ : auto∶ ValidAd ad} -- [BUG] Valid ad (order matters!)
    {p₂ : auto∶ Any (_∈ Hon) partG}
    {p₃ : auto∶ deposits ad ⊆ deposits Γ} →
  ────────────────────────────────────────────────────────────
  Γ —[ advertise⦅ ad ⦆ ]→ ` ad ∣ Γ
C-Advertise {p₁ = p₁} {p₂} {p₃} = [C-Advertise] (toWitness p₁) (toWitness p₂) (toWitness p₃)

C-AuthCommit :
  ∀ {secrets : List (Secret × Maybe ℕ)}
  → let (as , ms) = unzip secrets
        Δ         = || map (λ{ (ai , Ni) → ⟨ A ∶ ai ♯ Ni ⟩}) secrets
    in
    {p₁ : auto∶ as ≡ secretsOfᵖ A (ad .G)}
  → {p₂ : auto∶ All (_∉ secretsOfᶜᶠ A Γ) as}
  → {p₃ : auto∶ (A ∈ Hon → All Is-just ms)}
  → ` ad ∣ Γ —[ auth-commit⦅ A , ad , secrets ⦆ ]→ ` ad ∣ Γ ∣ Δ ∣ A auth[ ♯▷ ad ]
C-AuthCommit {p₁ = p₁} {p₂} {p₃} = [C-AuthCommit] (toWitness p₁) (toWitness p₂) (toWitness p₃)

C-AuthInit :
  ∀ {p₁ : auto∶ nub-participants (ad .G) ⊆ committedParticipants ad Γ}
    {p₂ : auto∶ (A , v , x) ∈ persistentDeposits (ad .G)}
  → ` ad ∣ Γ —[ auth-init⦅ A , ad , x ⦆ ]→ ` ad ∣ Γ ∣ A auth[ x ▷ˢ ad ]
C-AuthInit {p₁ = p₁} {p₂} = [C-AuthInit] (toWitness p₁) (toWitness p₂)

C-Init : let ⟨ G ⟩ C = ad; partG = nub-participants G in
  let toSpend = persistentDeposits G
      vs      = map select₂ toSpend
      xs      = map select₃ toSpend
  in
  ∀ {p : auto∶ x ∉ xs ++ ids Γ } →
  ` ad
  ∣ Γ
  ∣ || map (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ ad ] }) toSpend
  ∣ || map _auth[ ♯▷ ad ] partG
    —[ init⦅ G , C ⦆ ]→
  ⟨ C , sum vs ⟩at x ∣ Γ
C-Init {p = p} = [C-Init] (toWitness p)

C-Split :
  ∀ {vcis : VIContracts} →
  let (vs , cs , ys) = unzip₃ vcis in
  ∀ {p : auto∶ All (_∉ y ∷ ids Γ) ys} →
  ──────────────────────────────────────────
  ⟨ [ split (zip vs cs) ] , sum vs ⟩at y ∣ Γ
    —[ split⦅ y ⦆ ]→
  || map (uncurry₃ $ flip ⟨_,_⟩at_) vcis ∣ Γ
C-Split {vcis = vcis} {p = p} = [C-Split] {vcis = vcis} (toWitness p)

C-PutRev :
  ∀ {ds : DepositRefs}
    {ss : List (Participant × Secret × ℕ)}
  → let (_ , vs , xs) = unzip₃ ds
        (_ , as , _)  = unzip₃ ss
        Γ = || map (λ{ (Ai , vi , xi) → ⟨ Ai has vi ⟩at xi}) ds
        Δ = || map (λ{ (Bi , ai , Ni) → Bi ∶ ai ♯ Ni}) ss
        ΔΓ′ = Δ ∣ Γ′
    in
    {p₀ : auto∶ z ∉ y ∷ ids (Γ ∣ ΔΓ′)}
    {p₁ : auto∶ ⟦ p ⟧ᵖ Δ ≡ just true}
  → ⟨ [ put xs &reveal as if p ⇒ c ] , v ⟩at y ∣ (Γ ∣ ΔΓ′)
      —[ put⦅ xs , as , y ⦆ ]→
    ⟨ c , v + sum vs ⟩at z ∣ ΔΓ′
C-PutRev {ds = ds}{ss}{p₀}{p₁} = [C-PutRev] {ds = ds} {ss = ss} (toWitness p₀) (toWitness p₁)

C-Withdraw :
  ∀ {p : auto∶ x ∉ y ∷ ids Γ} →
  ⟨ [ withdraw A ] , v ⟩at y ∣ Γ
    —[ withdraw⦅ A , v , y ⦆ ]→
  ⟨ A has v ⟩at x ∣ Γ
C-Withdraw {p = p} = [C-Withdraw] (toWitness p)

C-AuthControl :
  ∀ {i : Index c}
  → let d = c ‼ i in
    {p₁ : auto∶ A L.Mem.∈ authDecorations d}
  → ⟨ c , v ⟩at x ∣ Γ —[ auth-control⦅ A , x ▷ d ⦆ ]→ ⟨ c , v ⟩at x ∣ A auth[ x ▷ d ] ∣ Γ
C-AuthControl {p₁ = p₁} = [C-AuthControl] (toWitness p₁)

-- T0D0 can we decide which transition to choose?
-- _—→?[_]_ : (Γ : Cfg) → (α : Label) → (Γ′ : Cfg) → Dec (Γ —→[ α ] Γ′)
-- Γ —→?[ α ] Γ′ = ?

C-Control :
  ∀ {i : Index c} → let open ∣SELECT c i; As = authDecorations d in

    {p₀ : auto∶ ¬Null (authDecorations d) ⊎ (length c > 1)}
  → {p₁ : auto∶ Γ ≈ L}
  → ⟨ [ d∗ ] , v ⟩at x ∣ L —[ α ]→ Γ′
  → {p₂ : auto∶ cv α ≡ just x}
  → ⟨ c , v ⟩at x ∣ || map _auth[ x ▷ d ] (nub (authDecorations d)) ∣ Γ —[ α ]→ Γ′
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

  ∀ {p₁ : True $ Null? As}
    {p₂ : auto∶ All (_≤ t) ts}
    {p₃ : auto∶ cv α ≡ just x} →

  ⟨ [ d∗ ] , v ⟩at x ∣ Γ —[ α ]→ Γ′
  ──────────────────────────────────────────────────────────────────────────────
  (⟨ c , v ⟩at x ∣ Γ) at t —[ α ]→ₜ Γ′ at t
Timeout {p₁ = p₁}{p₂}{p₃} Γ→ =
  [Timeout] (toWitness p₁) (toWitness p₂) Γ→ (toWitness p₃)
