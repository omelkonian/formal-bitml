------------------------------------------------------------------------
-- Properties of the symbolic model.
------------------------------------------------------------------------

open import Function using (_∋_; _∘_; case_of_)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Product using (∃; ∃-syntax; Σ; Σ-syntax; _×_; _,_; proj₁; proj₂; map₁; map₂)
open import Data.Sum     using (_⊎_)
open import Data.Nat     using (_>_; _≥_)
open import Data.Fin     using (Fin; fromℕ; toℕ)
  renaming (zero to 0ᶠ; suc to sucᶠ; _≟_ to _≟ᶠ_)
open import Data.String  using (String)
  renaming (length to lengthₛ)

open import Data.List using (List; []; _∷_; [_]; length; map; concatMap; _++_; zip)
open import Data.List.Membership.Propositional using (_∈_; _∉_; mapWith∈)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.List.Relation.Unary.Any using (Any)

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Relation.Unary.All using () renaming (All to Allₘ)

open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; inspect)

module SymbolicModel.Properties
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))
  where

open import Utilities.Lists
import Data.Set' as SET

open import Types                            Participant _≟ₚ_ Honest
open import BitML.Types                      Participant _≟ₚ_ Honest
open import BitML.DecidableEquality          Participant _≟ₚ_ Honest
open import Semantics.Actions.Types          Participant _≟ₚ_ Honest
open import Semantics.Configurations.Types   Participant _≟ₚ_ Honest
open import Semantics.Configurations.Helpers Participant _≟ₚ_ Honest
open import Semantics.InferenceRules         Participant _≟ₚ_ Honest
open import Semantics.Labels.Types           Participant _≟ₚ_ Honest
open import SymbolicModel.Strategy           Participant _≟ₚ_ Honest as SM

variable
  ads′ rads : AdvertisedContracts
  cs′ : ActiveContracts
  ds′ : Deposits
  Γ′ : Configuration ads′ cs′ ds′
  Δ : Configuration′ ([] , rads) ([] , []) ([] , [])
  Γp : Configuration′ p₁ p₂ p₃
  Γp′ : Configuration′ p₁ p₂ p₃
  Δs : List (Configuration [] [] [])

  R R′ R″ : Run
  α : Label
  t t′ : Time

  v : Value
  vs vsᶜ vsᵛ vsᵖ : Values
  c : Contracts v vs
  ad : Advertisement v vsᶜ vsᵛ vsᵖ

  ps : List Participant
  ss : List ValidSecret

  A : Participant
  secrets : List CommittedSecret

----------------------------------------
-- Helpers.

strip-cases-helper : stripSecrets ((v , vs , c) ∷ cs′ ∣∣ᶜˢ Γ)
                   ≡ (  ⟨ c , v ⟩ᶜ
                     ∣∣ stripSecrets (cs′ ∣∣ᶜˢ Γ)
                     ∶- refl & refl & refl & (SETᶜ.\\-left {[ v , vs , c ]}) & refl & refl )
strip-cases-helper = refl

strip-cases : stripSecrets (cs′ ∣∣ᶜˢ Γ) ≡ (cs′ ∣∣ᶜˢ stripSecrets Γ)
strip-cases {cs′ = []} = refl
strip-cases {cs′ = (v , vs , c) ∷ cs′} {ads} {cs} {ds} {Γ}
  rewrite strip-cases-helper {v} {vs} {c} {cs′} {ads} {cs} {ds} {Γ}
        | strip-cases {cs′} {ads} {cs} {ds} {Γ}
        = refl

strip-ds : stripSecrets (ds′ ∣∣ᵈˢ Γ) ≡ (ds′ ∣∣ᵈˢ stripSecrets Γ)
strip-ds {ds′ = []} = refl
strip-ds {ds′ = d ∷ ds′} {Γ = Γ}
  rewrite strip-ds {ds′} {Γ = Γ} = refl

strip-ss : stripSecrets (ss ∣∣ˢˢ Γ) ≡ (ss ∣∣ˢˢ stripSecrets Γ)
strip-ss {ss = []} = refl
strip-ss {ss = s ∷ ss} {Γ = Γ}
  rewrite strip-ss {ss = ss} {Γ = Γ} = refl

strip-b : ∀ {i j} →
  stripSecrets (Γ ∣∣ᵇ (i , j , ps)) ≡ (stripSecrets Γ ∣∣ᵇ (i , j , ps))
strip-b {ps = []} = refl
strip-b {ps = p ∷ ps} = strip-b {ps = ps}

strip-committedParticipants : committedParticipants (stripSecrets Γp) ad
                            ≡ committedParticipants Γp ad
strip-committedParticipants {Γp = ∅ᶜ}              = refl
strip-committedParticipants {Γp = ` _}             = refl
strip-committedParticipants {Γp = ⟨ _ , _ ⟩ᶜ}      = refl
strip-committedParticipants {Γp = ⟨ _ , _ ⟩ᵈ}      = refl
strip-committedParticipants {Γp = _ auth[ _ ]∶- _} = refl
strip-committedParticipants {Γp = ⟨ _ ∶ _ ♯ _ ⟩}   = refl
strip-committedParticipants {Γp = _ ∶ _ ♯ _}       = refl
strip-committedParticipants {ad = ad} {Γp = l ∣∣ r ∶- _}
  rewrite strip-committedParticipants {ad = ad} {Γp = l}
        | strip-committedParticipants {ad = ad} {Γp = r}
        = refl

strip-committedParticipants₂ :
    All (λ p → p SETₚ.∈ committedParticipants Γp ad)                ps
  → All (λ p → p SETₚ.∈ committedParticipants (stripSecrets Γp) ad) ps
strip-committedParticipants₂ {ad = ad} {Γp = Γp} p
  rewrite strip-committedParticipants {ad = ad} {Γp = Γp} = p

strip-spentForStipulation : spentForStipulation (stripSecrets Γp) ad
                          ≡ spentForStipulation Γp ad
strip-spentForStipulation {Γp = ∅ᶜ}              = refl
strip-spentForStipulation {Γp = ` _}             = refl
strip-spentForStipulation {Γp = ⟨ _ , _ ⟩ᶜ}      = refl
strip-spentForStipulation {Γp = ⟨ _ , _ ⟩ᵈ}      = refl
strip-spentForStipulation {Γp = _ auth[ _ ]∶- _} = refl
strip-spentForStipulation {Γp = ⟨ _ ∶ _ ♯ _ ⟩}   = refl
strip-spentForStipulation {Γp = _ ∶ _ ♯ _}       = refl
strip-spentForStipulation {ad = ad} {Γp = l ∣∣ r ∶- _}
  rewrite strip-spentForStipulation {ad = ad} {Γp = l}
        | strip-spentForStipulation {ad = ad} {Γp = r}
        = refl

strip-spentForStipulation₂ : toStipulate (G ad) ≡ spentForStipulation Δ ad
                           → toStipulate (G ad) ≡ spentForStipulation (stripSecrets Δ) ad
strip-spentForStipulation₂ {ad = ad} {Δ = Δ} p
  rewrite strip-spentForStipulation {ad = ad} {Γp = Δ}  = p


open import Data.List.Properties using (map-++-commute)
strip-cfgToList :
  cfgToList (stripSecrets Γp) ≡ map (map₂ (map₂ (map₂ stripSecrets))) (cfgToList Γp)
strip-cfgToList {Γp = ∅ᶜ} = refl
strip-cfgToList {Γp = ` _} = refl
strip-cfgToList {Γp = ⟨ _ , _ ⟩ᶜ} = refl
strip-cfgToList {Γp = ⟨ _ , _ ⟩ᵈ} = refl
strip-cfgToList {Γp = _ auth[ _ ]∶- _} = refl
strip-cfgToList {Γp = ⟨ _ ∶ _ ♯ _ ⟩} = refl
strip-cfgToList {Γp = _ ∶ _ ♯ _} = refl
strip-cfgToList {Γp = l ∣∣ r ∶- _}
  rewrite strip-cfgToList {Γp = l}
        | strip-cfgToList {Γp = r}
        = sym (map-++-commute (map₂ (map₂ (map₂ stripSecrets))) (cfgToList l) (cfgToList r))

open import Data.List.Relation.Binary.Permutation.Inductive.Properties using (map⁺)
strip-≈ : Γp              ≈ Γp′
        → stripSecrets Γp ≈ stripSecrets Γp′
strip-≈ {Γp = Γp} {Γp′ = Γp′} Γp≈
  rewrite strip-cfgToList {Γp = Γp}
        | strip-cfgToList {Γp = Γp′}
        = map⁺ (map₂ (map₂ (map₂ stripSecrets))) Γp≈

strip-lastCfg : lastCfg (R ∗) ≡ stripSecretsₜ (lastCfg R)
strip-lastCfg {_ ∙ˢ}        = refl
strip-lastCfg {_ ∷ˢ⟦ _ ⟧ _} = refl

----------------------------------------
-- Lemma I.

infix -1 _——→[_]_
_——→[_]_ : Run → Label → Run → Set
R ——→[ α ] R′ = proj₂ (proj₂ (proj₂ (lastCfg R))) —→ₜ[ α ] proj₂ (proj₂ (proj₂ (lastCfg R′)))

module _ (α≢₁ : ∀ A s      → α ≢ auth-rev[ A , s ])
         (α≢₂ : ∀ A ⟨G⟩C Δ → α ≢ auth-commit[ A , ⟨G⟩C , Δ ]) where

  strip-preserves-semantics :
      ( ∀ R′ → R   ——→ₜ[ α ] R′
               --------------------
             → R ∗ ——→ₜ[ α ] R′ ∗ )

    × ( ∀ R″ → R ∗ ——→ₜ[ α ] R″
               --------------------------
             → ∃[ R′ ] ( (R ——→ₜ[ α ] R′)
                       × R′ ∗ ≡ R″ ∗ ))

  strip-preserves-semantics {R = R} = pr₁ , pr₂
    where
      strip-→ : Γ —→[ α ] Γ′
            ------------------------------------------------
          → stripSecrets Γ —→[ α ] stripSecrets Γ′
      strip-→ ([C-AuthRev] {A = A} {s = s} _)
        = ⊥-elim (α≢₁ A s refl)
      strip-→ ([C-AuthCommit] {A = A} {secrets = secrets} {v = v} {vsᶜ = vsᶜ} {vsᵛ = vsᵛ} {vsᵖ = vsᵖ} {ad = ad} _ _ )
        = ⊥-elim (α≢₂ A (v , vsᶜ , vsᵛ , vsᵖ , ad) secrets refl)

      strip-→ ([C-Withdraw] x)      = [C-Withdraw] x
      strip-→ ([C-AuthControl] x)   = [C-AuthControl] x
      strip-→ [DEP-AuthJoin]        = [DEP-AuthJoin]
      strip-→ [DEP-Join]            = [DEP-Join]
      strip-→ [DEP-AuthDivide]      = [DEP-AuthDivide]
      strip-→ [DEP-Divide]          = [DEP-Divide]
      strip-→ [DEP-AuthDonate]      = [DEP-AuthDonate]
      strip-→ [DEP-Donate]          = [DEP-Donate]
      strip-→ [DEP-AuthDestroy]     = [DEP-AuthDestroy]
      strip-→ [DEP-Destroy]         = [DEP-Destroy]
      strip-→ ([C-Advertise] x x₁)  = [C-Advertise] x x₁

      strip-→ ([C-AuthInit] {ad = ad} {dsˡ = dsˡ} {dsʳ = dsʳ} {Γ = Γ} {p = refl} x x₁) =
        [C-AuthInit] {dsˡ = dsˡ} {dsʳ = dsʳ} {p = refl} x (strip-committedParticipants₂ {ad = ad} {Γp = Γ} x₁)

      strip-→ ([C-Init] {ad = ad} {Δ = Δ} x x₁ x₂) =
        [C-Init] x (strip-committedParticipants₂ {ad = ad} {Γp = Δ} x₁)
                   (strip-spentForStipulation₂ {ad = ad} {Δ = Δ} x₂)

      strip-→ ([C-Split] {ads} {cs} {ds} {Γ} {vs = vs} {cases = cases} refl refl)
        rewrite strip-cases {casesToContracts cases} {ads} {cs} {ds} {Γ}
              = [C-Split] refl refl

      strip-→ ([C-PutRev] {Γ = Γ} {ds′ = ds′} {ss = ss} pr x x₁ x₂ x₃)
        rewrite strip-ds {ds′ = ds′} {Γ = ss ∣∣ˢˢ Γ}
              | strip-ss {ss = ss} {Γ = Γ}
              = [C-PutRev] {Γ = stripSecrets Γ} {ds′ = ds′} {ss = ss} pr x x₁ x₂ x₃

      strip-→ ([C-Control] {v = v} {contract = c} {i = i})
        rewrite strip-b {Γ = ⟨ c , v ⟩ᶜ} {ps = authDecorations (c ‼ i)} {i = 0ᶠ} {j = i}
              = [C-Control]

      strip-→ₜ : Γ at t —→ₜ[ α ] Γ′ at t′
          → stripSecrets Γ at t —→ₜ[ α ] stripSecrets Γ′ at t′
      strip-→ₜ ([Action] Γ→) = [Action] (strip-→ Γ→)
      strip-→ₜ [Delay]      = [Delay]
      strip-→ₜ {t = t} {t′ = t′} ([Timeout] {Γ = Γ} {Γ″ = Γ″} {v = v} {contract = c} {Γ′ = Γ′ at t}
                                       (refl , Γ≈)
                                       ∀≤t
                                       c‼i→)
          = [Timeout] {Γ = stripSecrets Γ} {Γ″ = stripSecrets Γ″} {Γ′ = stripSecrets Γ′ at t}
                      (refl , strip-≈ {Γp = Γ′}
                                      {Γp′ = ⟨ c , v ⟩ᶜ ∣∣ Γ ∶- refl & refl & refl & refl & refl & refl} Γ≈)
                      ∀≤t
                      (strip-→ c‼i→)

      pr₁ : ∀ R′
        → R   ——→[ α ] R′
          -----------------
        → R ∗ ——→[ α ] R′ ∗
      pr₁ R′ R→ rewrite strip-lastCfg {R}
                      | strip-lastCfg {R′}
                      = strip-→ₜ R→

      pr₂ : ∀ R″
        → R ∗ ——→ₜ[ α ] R″
          --------------------------
        → ∃[ R′ ] ( (R ——→ₜ[ α ] R′)
                  × R′ ∗ ≡ R″ ∗ )
      pr₂ t = {!!}

{-
module _ (Adv : Participant) (Adv∉ : Adv ∉ Hon) where
  open SM.AdvM Adv Adv∉

  adversarial-move-is-semantic :
      (SS : Strategies)
    → ∃[ R′ ] ( R ——→ₜ[ runAdversary SS R ] R′)
  adversarial-move-is-semantic = {!!}


-- T0D0 induction on list of honest strategies
-- T0D0 induction on the run itself

-}
