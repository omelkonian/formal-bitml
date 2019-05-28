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

toNothing : CommittedSecret → CommittedSecret
toNothing (x , _) = x , nothing

proj₁∘toNothing : map proj₁ (map toNothing secrets) ≡ map proj₁ secrets
proj₁∘toNothing {secrets = []}          = refl
proj₁∘toNothing {secrets = _ ∷ secrets} rewrite proj₁∘toNothing {secrets = secrets} = refl

strip-ad₂ :
    stripSecrets (Γp ∣∅ map (A ,_) secrets)
  ≡ (stripSecrets Γp ∣∅ map (A ,_) (map toNothing secrets))
strip-ad₂ {secrets = []} = refl
strip-ad₂ {A = A} {secrets = (_ , nothing) ∷ secrets } {Γp = Γp}
  rewrite strip-ad₂ {A = A} {secrets = secrets} {Γp = Γp} = {!refl!}
strip-ad₂ {A = A} {secrets = (_ , just x) ∷ secrets } {Γp = Γp}
  rewrite strip-ad₂ {A = A} {secrets = secrets} {Γp = Γp} = {!refl!}

p₁′ :
    (∀ A s → α ≢ auth-rev[ A , s ])
  → Γ —→[ α ] Γ′
    ------------------------------------------------
  → stripSecrets Γ —→[ stripLabel α ] stripSecrets Γ′

p₁′ α≢ ([C-AuthRev] {A = A} {s = s} _) = ⊥-elim (α≢ A s refl)
p₁′ _ ([C-Withdraw] x) = [C-Withdraw] x
p₁′ _ ([C-AuthControl] x) = [C-AuthControl] x
p₁′ _ [DEP-AuthJoin] = [DEP-AuthJoin]
p₁′ _ [DEP-Join] = [DEP-Join]
p₁′ _ [DEP-AuthDivide] = [DEP-AuthDivide]
p₁′ _ [DEP-Divide] = [DEP-Divide]
p₁′ _ [DEP-AuthDonate] = [DEP-AuthDonate]
p₁′ _ [DEP-Donate] = [DEP-Donate]
p₁′ _ [DEP-AuthDestroy] = [DEP-AuthDestroy]
p₁′ _ [DEP-Destroy] = [DEP-Destroy]
p₁′ _ ([C-Advertise] x x₁) = [C-Advertise] x x₁

p₁′ _ ([C-AuthInit] {ad = ad} {dsˡ = dsˡ} {dsʳ = dsʳ} {Γ = Γ} {p = refl} x x₁) =
  [C-AuthInit] {dsˡ = dsˡ} {dsʳ = dsʳ} {p = refl} x (strip-committedParticipants₂ {ad = ad} {Γp = Γ} x₁)

p₁′ _ ([C-Init] {ad = ad} {Δ = Δ} x x₁ x₂) =
  [C-Init] x (strip-committedParticipants₂ {ad = ad} {Γp = Δ} x₁)
             (strip-spentForStipulation₂ {ad = ad} {Δ = Δ} x₂)

p₁′ _ ([C-Split] {ads} {cs} {ds} {Γ} {vs = vs} {cases = cases} refl refl)
  rewrite strip-cases {casesToContracts cases} {ads} {cs} {ds} {Γ}
        = [C-Split] refl refl

p₁′ _ ([C-PutRev] {Γ = Γ} {ds′ = ds′} {ss = ss} pr x x₁ x₂ x₃)
  rewrite strip-ds {ds′ = ds′} {Γ = ss ∣∣ˢˢ Γ}
        | strip-ss {ss = ss} {Γ = Γ}
        = [C-PutRev] {Γ = stripSecrets Γ} {ds′ = ds′} {ss = ss} pr x x₁ x₂ x₃

p₁′ _ ([C-Control] {v = v} {contract = c} {i = i})
  rewrite strip-b {Γ = ⟨ c , v ⟩ᶜ} {ps = authDecorations (c ‼ i)} {i = 0ᶠ} {j = i}
        = [C-Control]

p₁′ _ ([C-AuthCommit] {A = A} {secrets = secrets} {v = v}
                      {vsᶜ = vsᶜ} {vsᵛ = vsᵛ} {vsᵖ = vsᵖ} {ad = ad}
                      {ads = ads} {rads = rads} {cs = cs} {ds = ds} {Γ = Γ}
                      {pr = pr}
                      x p)
  rewrite strip-ad₂ {A = A} {secrets = secrets}
                    {Γp = ` ad ∣∣ Γ ∶- refl & {!!} & refl & refl & refl & refl}
   = [C-AuthCommit] {A = A} {secrets = map toNothing secrets}
                            {v = v} {vsᶜ = vsᶜ} {vsᵛ = vsᵛ} {vsᵖ = vsᵖ} {ad = ad}
                            {ads = ads} {rads = rads} {cs = cs} {ds = ds} {Γ = stripSecrets Γ}
                            {pr = trans proj₁∘toNothing pr}
                            x λ A∈Hon → {!!}

{-
p₁T :
    (∀ A s → α ≢ auth-rev[ A , s ])
  → Γ at t —→ₜ[ α ] Γ′ at t′
  → stripSecrets Γ at t —→ₜ[ α ] stripSecrets Γ′ at t′
p₁T α≢ ([Action] x) = [Action] (p₁′ α≢ x)
p₁T [Delay] = [Delay]
p₁T ([Timeout] x x₁ x₂) = {!!}


infix -1 _——→[_]_
_——→[_]_ : Run → Label → Run → Set
R ——→[ α ] R′ =
  let (_ , _ , _ , c at _)  = lastCfg R
      (_ , _ , _ , c′ at _) = lastCfg R′
  in c —→[ α ] c′

h : (∀ A s → α ≢ auth-rev[ A , s ])
  → R ——→[ α ] R′
    -------------------
  → R ✴ ——→[ α ] R′ ✴
h {α} {R} {R′} eq t = {!t!}

strip-preserves-semantics :

    (∀ A s → α ≢ auth-rev[ A , s ])

  → ( ∀ R′
    → R   ——→ₜ[ α ] R′
      --------------------
    → R ✴ ——→ₜ[ α ] R′ ✴ )

  × ( ∀ R″
    → R ✴ ——→ₜ[ α ] R″
      --------------------------
    → ∃[ R′ ] ( (R ——→ₜ[ α ] R′)
              × R′ ✴ ≡ R″ ✴ ))

strip-preserves-semantics {R = R} eq = p₁ , p₂
  where

    p₁ : ∀ R′
      → R   ——→ₜ[ α ] R′
        --------------------
      → R ✴ ——→ₜ[ α ] R′ ✴
    p₁ R′ t =
      let (ads  , cs  , ds  , tc)  = lastCfg R
          (ads′ , cs′ , ds′ , tc′) = lastCfg R′
      in {!p₁T t !}

    p₂ : ∀ R″
      → R ✴ ——→ₜ[ α ] R″
        --------------------------
      → ∃[ R′ ] ( (R ——→ₜ[ α ] R′)
                × R′ ✴ ≡ R″ ✴ )
    p₂ t = {!!}

module _ (Adv : Participant) (Adv∉ : Adv ∉ Hon) where
  open SM.AdvM Adv Adv∉

  adversarial-move-is-semantic :
      (SS : Strategies)
    → ∃[ R′ ] ( R ——→ₜ[ runAdversary SS R ] R′)
  adversarial-move-is-semantic = {!!}


-- T0D0 induction on list of honest strategies
-- T0D0 induction on the run itself

-}
