------------------------------------------------------------------------
-- Helpers for stripping.
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

module SymbolicModel.Helpers
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
  Δ : Configuration′ ([] , rads) ([] , []) ([] , [])
  Δs : List (Configuration [] [] [])

  R R′ R″ : Run
  T T′ T″ : ∃TimedConfiguration
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

strip-cases-helper : ((v , vs , c) ∷ cs′ ∣∣ᶜˢ Γ) ∗ᶜ
                   ≡ (  ⟨ c , v ⟩ᶜ
                     ∣∣ (cs′ ∣∣ᶜˢ Γ) ∗ᶜ
                     ∶- refl & refl & refl & (SETᶜ.\\-left {[ v , vs , c ]}) & refl & refl )
strip-cases-helper = refl

strip-cases : (cs′ ∣∣ᶜˢ Γ) ∗ᶜ ≡ (cs′ ∣∣ᶜˢ (Γ ∗ᶜ))
strip-cases {cs′ = []} = refl
strip-cases {cs′ = (v , vs , c) ∷ cs′} {ads} {cs} {ds} {Γ}
  rewrite strip-cases-helper {v} {vs} {c} {cs′} {ads} {cs} {ds} {Γ}
        | strip-cases {cs′} {ads} {cs} {ds} {Γ}
        = refl

strip-ds : (ds′ ∣∣ᵈˢ Γ) ∗ᶜ ≡ (ds′ ∣∣ᵈˢ Γ ∗ᶜ)
strip-ds {ds′ = []} = refl
strip-ds {ds′ = d ∷ ds′} {Γ = Γ}
  rewrite strip-ds {ds′} {Γ = Γ} = refl

strip-ss : (ss ∣∣ˢˢ Γ) ∗ᶜ ≡ (ss ∣∣ˢˢ Γ ∗ᶜ)
strip-ss {ss = []} = refl
strip-ss {ss = s ∷ ss} {Γ = Γ}
  rewrite strip-ss {ss = ss} {Γ = Γ} = refl

strip-b : ∀ {i j} →
  (Γ ∣∣ᵇ (i , j , ps)) ∗ᶜ ≡ (Γ ∗ᶜ ∣∣ᵇ (i , j , ps))
strip-b {ps = []} = refl
strip-b {ps = p ∷ ps} = strip-b {ps = ps}

strip-committedParticipants : committedParticipants (Γp ∗ᶜ) ad
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
  → All (λ p → p SETₚ.∈ committedParticipants (Γp ∗ᶜ) ad) ps
strip-committedParticipants₂ {ad = ad} {Γp = Γp} p
  rewrite strip-committedParticipants {ad = ad} {Γp = Γp} = p

strip-spentForStipulation : spentForStipulation (Γp ∗ᶜ) ad
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
                           → toStipulate (G ad) ≡ spentForStipulation (Δ ∗ᶜ) ad
strip-spentForStipulation₂ {ad = ad} {Δ = Δ} p
  rewrite strip-spentForStipulation {ad = ad} {Γp = Δ}  = p


open import Data.List.Properties using (map-++-commute)
strip-cfgToList :
  cfgToList (Γp ∗ᶜ) ≡ map (map₂ (map₂ (map₂ _∗ᶜ))) (cfgToList Γp)
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
        = sym (map-++-commute (map₂ (map₂ (map₂ _∗ᶜ))) (cfgToList l) (cfgToList r))

open import Data.List.Relation.Binary.Permutation.Inductive.Properties using (map⁺)
strip-≈ : Γp    ≈ Γp′
        → Γp ∗ᶜ ≈ Γp′ ∗ᶜ
strip-≈ {Γp = Γp} {Γp′ = Γp′} Γp≈
  rewrite strip-cfgToList {Γp = Γp}
        | strip-cfgToList {Γp = Γp′}
        = map⁺ (map₂ (map₂ (map₂ _∗ᶜ))) Γp≈

strip-lastCfg : lastCfg (R ∗) ≡ (lastCfg R) ∗ᵗ
strip-lastCfg {_ ∙ˢ}        = refl
strip-lastCfg {_ ∷ˢ⟦ _ ⟧ _} = refl

strip-idempotent : ∀ (γ : Configuration′ p₁ p₂ p₃) →
  (γ ∗ᶜ) ∗ᶜ ≡ γ ∗ᶜ
strip-idempotent ∅ᶜ                = refl
strip-idempotent (` _)             = refl
strip-idempotent ⟨ _ , _ ⟩ᶜ        = refl
strip-idempotent ⟨ _ , _ ⟩ᵈ        = refl
strip-idempotent (_ auth[ _ ]∶- _) = refl
strip-idempotent ⟨ _ ∶ _ ♯ _ ⟩     = refl
strip-idempotent (_ ∶ _ ♯ _)       = refl
strip-idempotent (l ∣∣ r ∶- _)     rewrite strip-idempotent l
                                        | strip-idempotent r
                                        = refl

strip-strip-rewrite : ∀ {l : Configuration ads cs ds} {γ : Configuration ads′ cs′ ds′} {pr}
  → (_∣∣_∶-_ {ads = ads ++ ads′} {rads = []}
             {cs = cs  ++ cs′} {rcs = []}
             {ds = ds ++ ds′} {rds = []}
             l ((γ ∗ᶜ) ∗ᶜ) pr)
  ≡ (l ∣∣ γ ∗ᶜ ∶- pr)
strip-strip-rewrite {γ = γ}
  rewrite strip-idempotent γ
        = refl
