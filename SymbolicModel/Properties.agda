------------------------------------------------------------------------
-- Properties of the symbolic model.
------------------------------------------------------------------------
{-# OPTIONS --allow-unsolved-metas #-}

open import Function using (_∋_; _∘_; case_of_)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Product using (∃; ∃-syntax; Σ; Σ-syntax; _×_; _,_; proj₁; proj₂; map₁; map₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
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
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans) -- ; inspect)

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
open import SymbolicModel.Helpers            Participant _≟ₚ_ Honest

----------------------------------------
-- Lemma I.

help : R ∗ ——→[ α ] T′
     → proj₂ (proj₂ (proj₂ ((lastCfg R) ∗ᵗ))) —→ₜ[ α ] proj₂ (proj₂ (proj₂ T′))
help {R = _ ∙ˢ}        R→ = R→
help {R = _ ∷ˢ⟦ _ ⟧ _} R→ = R→

destruct-γ∗ : ∀ {Γ Γ₀ : Configuration′ (ads , rads) (cs , rcs) (ds , rds)}
                {l    : Configuration ads′ cs′ ds′}
                {γ∗   : Configuration′ (adsʳ , radsʳ) (csʳ , rcsʳ) (dsʳ , rdsʳ)}
                {pr   : ads  ≡ ads′ ++ adsʳ
                      × rads ≡ [] ++ (radsʳ SETₐ.\\ ads′)
                      × cs   ≡ cs′  ++ csʳ
                      × rcs  ≡ [] ++ (rcsʳ SETᶜ.\\ cs′)
                      × ds   ≡ (ds′ SETₑ.\\ rdsʳ) ++ dsʳ
                      × rds  ≡ [] ++ (rdsʳ SETₑ.\\ ds′) }
  → Γ₀ ≡ Γ ∗ᶜ
  → Γ₀ ≡ (l ∗ᶜ ∣∣ γ∗ ∶- pr)
  → ∃[ γ ] ( (γ∗ ≡ γ ∗ᶜ)
           × (Γ ≡ (l ∣∣ γ ∶- pr)) )
destruct-γ∗ {Γ = ∅ᶜ}             refl ()
destruct-γ∗ {Γ = ` _}             refl ()
destruct-γ∗ {Γ = ⟨ _ , _ ⟩ᶜ}      refl ()
destruct-γ∗ {Γ = ⟨ _ , _ ⟩ᵈ}      refl ()
destruct-γ∗ {Γ = _ auth[ _ ]∶- _} refl ()
destruct-γ∗ {Γ = ⟨ _ ∶ _ ♯ _ ⟩}   refl ()
destruct-γ∗ {Γ = _ ∶ _ ♯ _}       refl ()
destruct-γ∗ {Γ = l′ ∣∣ γ ∶- pr₂} {Γ₀ = Γ₀} {l = l} {γ∗ = γ∗} {pr = pr₁} p0 p
  with pr₁
... | (refl , refl , refl , refl , refl , refl)
    = {! γ , refl , refl !}

data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect x = x with≡ refl

module _ (α≢₁ : ∀ A s      → α ≢ auth-rev[ A , s ])
         (α≢₂ : ∀ A ⟨G⟩C Δ → α ≢ auth-commit[ A , ⟨G⟩C , Δ ]) where

  strip-preserves-semantics :
      ( ∀ T′ → R   ——→[ α ] T′
               --------------------
             → R ∗ ——→[ α ] T′ ∗ᵗ )

    × ( ∀ T′ → R ∗ ——→[ α ] T′
               --------------------------
             → ∃[ T″ ] ( (R ——→[ α ] T″)
                       × T′ ∗ᵗ ≡ T″ ∗ᵗ ))

  strip-preserves-semantics {R = R} = pr₁ , pr₂
    where
      strip-→ : Γ —→[ α ] Γ′
            ------------------------------------------------
          → Γ ∗ᶜ —→[ α ] Γ′ ∗ᶜ
      strip-→ ([C-AuthRev] {A = A} {s = s} _)
        = ⊥-elim (α≢₁ A s refl)
      strip-→ ([C-AuthCommit] {A = A} {secrets = secrets} {v = v} {vsᶜ = vsᶜ} {vsᵛ = vsᵛ} {vsᵖ = vsᵖ} {ad = ad} _ _ )
        = ⊥-elim (α≢₂ A (v , vsᶜ , vsᵛ , vsᵖ , ad) secrets refl)

      strip-→ [C-Withdraw]          = [C-Withdraw]
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
              = [C-PutRev] {Γ = Γ ∗ᶜ} {ds′ = ds′} {ss = ss} pr x x₁ x₂ x₃

      strip-→ ([C-Control] {v = v} {contract = c} {i = i})
        rewrite strip-b {Γ = ⟨ c , v ⟩ᶜ} {ps = authDecorations (c ‼ i)} {i = 0ᶠ} {j = i}
              = [C-Control]

      strip-→ₜ : Γ      at t —→ₜ[ α ] Γ′      at t′
               → (Γ ∗ᶜ) at t —→ₜ[ α ] (Γ′ ∗ᶜ) at t′
      strip-→ₜ ([Action] Γ→) = [Action] (strip-→ Γ→)
      strip-→ₜ [Delay]      = [Delay]
      strip-→ₜ {t = t} {t′ = t′} ([Timeout] {Γ = Γ} {Γ″ = Γ″} {v = v} {contract = c} ∀≤t c‼i→)
          = [Timeout] {Γ = Γ ∗ᶜ} {Γ″ = Γ″ ∗ᶜ} ∀≤t (strip-→ c‼i→)

      pr₁ : ∀ T′
        → R   ——→[ α ] T′
          -----------------
        → R ∗ ——→[ α ] T′ ∗ᵗ
      pr₁ T′ R→ rewrite strip-lastCfg {R}
                      = strip-→ₜ R→

      pr0 : ∀ (Γ₀ : Configuration ads cs ds)
        → Γ₀ —→[ α ] Γ′
        → Γ₀ ≡ Γ ∗ᶜ
          ---------------------------------
        → ∃[ Γ″ ] ( (Γ —→[ α ] Γ″)
                  × Γ′ ∗ᶜ ≡ Γ″ ∗ᶜ )
      pr0 {Γ′ = Γ′} {Γ = Γ} Γ₀ Γ→ Γ₀≡
        with Γ→
      ... | def = {!!}
      -- etc...
  {-
  ... | [C-AuthRev] {A = A} {s = s} _
      = ⊥-elim (α≢₁ A s refl)
  ... | [C-AuthCommit] {A = A} {secrets = secrets} {v = v} {vsᶜ = vsᶜ} {vsᵛ = vsᵛ} {vsᵖ = vsᵖ} {ad = ad} _ _
      = ⊥-elim (α≢₂ A (v , vsᶜ , vsᵛ , vsᵖ , ad) secrets refl)
  ... | [C-Withdraw] {Γ = γ∗} {A = A} {v = v}
      = let l = ⟨ A , v ⟩ᵈ
        in case destruct-γ∗ {Γ = Γ} {Γ₀ = Γ₀} {l = ⟨ [ withdraw A ] , v ⟩ᶜ} {γ∗ = γ∗}
                            {pr = refl & refl & refl & refl & refl & refl}
                            Γ₀≡ refl
        of λ { (γ , refl , refl) →
               (l ∣∣ γ ∶- refl & refl & refl & refl & refl & refl)
             , [C-Withdraw] {Γ = γ} {A = A} {v = v}
             , strip-strip-rewrite {l = l} {γ = γ} {pr = refl & refl & refl & refl & refl & refl} }
  ... | [C-AuthControl] {Γ = γ∗} {A = A} {v = v} {vs = vs} {contract = c} {i = i} p
      = let l = ⟨ c , v ⟩ᶜ ∣∣ A auth[ c ▷ᵇ i ]∶- refl & refl & refl
                ∶- refl & refl & refl & SETᶜ.\\-same {[ v , vs , c ]} & refl & refl
        in case destruct-γ∗ {Γ = Γ} {Γ₀ = Γ₀} {l = ⟨ c , v ⟩ᶜ} {γ∗ = γ∗}
                            {pr = refl & refl & refl & refl & refl & refl}
                            Γ₀≡ refl
           of λ { (γ , refl , refl) →
                  (l ∣∣ γ ∶- refl & refl & refl & refl & refl & refl)
                , [C-AuthControl] {Γ = γ} {A = A} {v = v} {contract = c} {i = i} p
                , strip-strip-rewrite {l = l} {γ = γ} {pr = refl & refl & refl & refl & refl & refl} }
  -}

      pr1 : ∀ {Γ₀ : Configuration ads cs ds}
        → Γ₀ at t —→ₜ[ α ] Γ′ at t′
        → Γ₀ ≡ Γ ∗ᶜ
          ------------------------------------
        → ∃[ Γ″ ] ( (Γ at t —→ₜ[ α ] Γ″ at t′)
                  × (Γ′ ∗ᶜ ≡ Γ″ ∗ᶜ) )
      pr1 {Γ′ = Γ′} {Γ = Γ} {Γ₀ = Γ₀} Γ→ₜ Γ₀≡
        with Γ→ₜ
      ... | [Action] Γ→
          = case pr0 {Γ′ = Γ′} {Γ = Γ} Γ₀ Γ→ Γ₀≡
            of λ { (Γ″ , Γ→Γ″ , Γ≡) → Γ″ , [Action] Γ→Γ″ , Γ≡ }
      ... | [Delay] {δ = δ} = case Γ₀≡ of λ { refl → Γ , [Delay] {δ = δ} , strip-idempotent Γ }
      ... | [Timeout] {Γ = γ∗} {Γ″ = .Γ′} {v = v} {vs = vs} {contract = c} {i = i} ∀t Γ→
        with destruct-γ∗ {Γ = Γ} {Γ₀ = Γ₀} {l = ⟨ c , v ⟩ᶜ} {γ∗ = γ∗}
                         {pr = refl & refl & refl & refl & refl & refl}
                         Γ₀≡ refl
      ... | γ , refl , refl
        with pr0 {Γ′ = Γ′}
                 {Γ = ⟨ [ c ‼ i ] , v ⟩ᶜ ∣∣ γ ∶- refl & refl & refl & refl & refl & refl}
                 (⟨ [ c ‼ i ] , v ⟩ᶜ ∣∣ γ∗ ∶- refl & refl & refl & refl & refl & refl)
                 Γ→ refl
      ... | Γ″ , Γ→Γ″ , Γ≡
          = Γ″ , [Timeout] {Γ = γ} {Γ″ = Γ″} {v = v} {vs = vs} {contract = c} {i = i} ∀t Γ→Γ″ , Γ≡

      pr₂ : ∀ T′
        → R ∗ ——→[ α ] T′
          --------------------------
        → ∃[ T″ ] ( (R ——→[ α ] T″)
                  × T′ ∗ᵗ ≡ T″ ∗ᵗ )
      pr₂ T′ R→
        with inspect (lastCfg R)
      ... | (ads , cs , ds , tc) with≡ eq
        with inspect T′
      ... | (ads′ , cs′ , ds′ , tc′) with≡ eq′
        with inspect tc
      ... | (Γ at t) with≡ eqt
        with inspect tc′
      ... | (Γ′ at t′) with≡ eqt′
        with (eq , eq′ , eqt , eqt′)
      ... | refl , refl , refl , refl
        with pr1 {t = t} {Γ′ = Γ′} {t′ = t′} {Γ = Γ} {Γ₀ = Γ ∗ᶜ} (help {R = R} {T′ = T′} R→) refl
      ... | Γ″ , Γ→ , Γ≡ = (ads′ , cs′ , ds′ , Γ″ at t′) , Γ→ , cong (λ g → (ads′ , cs′ , ds′ , g at t′)) Γ≡


module _ (Adv : Participant) (Adv∉ : Adv ∉ Hon) where
  open SM.AdvM Adv Adv∉

  variable
    S† : AdversarialStrategy
    S  : HonestStrategies

  valid-hon-move : ∀ {A} (A∈ : A ∈ Hon)
    → runAdversary (S† , S) R ∈ concatMap proj₂ (runHonestAll (R ∗) S)
    → runAdversary (S† , S) R ∈ strategy (S A∈) (R ∗)
  valid-hon-move = {!!}

  adversarial-move-is-semantic :
    ∃[ T′ ] ( R ——→[ runAdversary (S† , S) R ] T′)
  adversarial-move-is-semantic {R = R} {S† = S†} {S = S} =
    let
      moves = runHonestAll (R ∗) S
      (cases , v) = valid S† {R = R} {moves = moves}
    in case cases of
    λ { (inj₁ (A , A∈ , eq , α∈ ))
      → let (_ , R→ , _) = valid (S A∈)
        in R→ {R} {runAdversary (S† , S) R} (valid-hon-move {S† = S†} {S = S} {R = R} {A = A} A∈ α∈)
      ; c → {!!}
      }


-- T0D0 induction on list of honest strategies
-- T0D0 induction on the run itself
