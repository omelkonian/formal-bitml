------------------------------------------------------------------------
-- Symbolic strategies.
------------------------------------------------------------------------

open import Data.Empty   using (⊥)
open import Data.Product using (∃; ∃-syntax; Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_)
open import Data.Nat     using (_>_; _≥_)

open import Data.List    using (List; []; _∷_; [_]; length; map; concatMap; _++_)
open import Data.List.Membership.Propositional using (_∈_; _∉_; mapWith∈)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.Any using (Any)

open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Maybe.Relation.Unary.All using () renaming (All to Allₘ)

open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

module SymbolicModel.Strategy
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

variable
  ads ads′ ads″ rads adsʳ radsʳ adsˡ radsˡ : AdvertisedContracts
  cs  cs′  cs″  rcs  csʳ  rcsʳ  csˡ  rcsˡ  : ActiveContracts
  ds  ds′  ds″  rds  dsʳ  rdsʳ  dsˡ  rdsˡ  : Deposits
  Γ Γ₀ : Configuration ads  cs  ds
  Γ′   : Configuration ads′ cs′ ds′
  Γ″   : Configuration ads″ cs″ ds″

  p₁ p₁′ : AdvertisedContracts × AdvertisedContracts
  p₂ p₂′ : ActiveContracts     × ActiveContracts
  p₃ p₃′ : Deposits            × Deposits
  Γp  : Configuration′ p₁  p₂  p₃
  Γp′ : Configuration′ p₁′ p₂′ p₃′

----------------------------------
-- Symbolic runs.

{- Version 1: New list-like, labelled datatype with existential elements. -}

data Run : Set where
  _∙ˢ     : ∃TimedConfiguration → Run

  _∷ˢ⟦_⟧_ : ∃TimedConfiguration → Label → Run → Run


mapRun : (∃TimedConfiguration → ∃TimedConfiguration)
       → (Label → Label)
       → Run → Run
mapRun f _ (tc ∙ˢ)        = f tc ∙ˢ
mapRun f g (tc ∷ˢ⟦ a ⟧ s) = f tc ∷ˢ⟦ g a ⟧ mapRun f g s

lastCfg : Run → ∃TimedConfiguration
lastCfg (tc ∙ˢ)        = tc
lastCfg (tc ∷ˢ⟦ _ ⟧ _) = tc

prefixRuns : Run → List Run
prefixRuns (tc ∙ˢ)        = [ tc ∙ˢ ]
prefixRuns (tc ∷ˢ⟦ α ⟧ R) = let rs = prefixRuns R in rs ++ map (tc ∷ˢ⟦ α ⟧_) rs

--------------------------------------
-- Stripping.

_∗ᶜ : Configuration′ p₁ p₂ p₃ → Configuration′ p₁ p₂ p₃
⟨ p ∶ a ♯ _ ⟩ ∗ᶜ = ⟨ p ∶ a ♯ nothing ⟩
(l ∣∣ r ∶- p) ∗ᶜ = l ∗ᶜ ∣∣ r ∗ᶜ ∶- p
c             ∗ᶜ = c

_∗ᵗ : ∃TimedConfiguration → ∃TimedConfiguration
(ads , cs , ds , Γ at t) ∗ᵗ = ads , cs , ds , (Γ ∗ᶜ) at t

stripLabel : Label → Label
stripLabel auth-commit[ p , ad , _ ] = auth-commit[ p , ad , [] ]
stripLabel a = a

-- Hide all committed secrets in a symbolic run.
_∗ : Run → Run
_∗ = mapRun _∗ᵗ stripLabel

infix -1 _——→[_]_
_——→[_]_ : Run → Label → ∃TimedConfiguration → Set
R ——→[ α ] (_ , _ , _ , tc′)
  = proj₂ (proj₂ (proj₂ (lastCfg R))) —→ₜ[ α ] tc′

_∈ʳ_ : Configuration′ p₁ p₂ p₃ → Run → Set
_∈ʳ_ {p₁} {p₂} {p₃} c R =
  (p₁ , p₂ , p₃ , c) ∈ cfgToList (cfg (proj₂ (proj₂ (proj₂ (lastCfg (R ∗))))))

----------------------------------
-- Symbolic strategies.

record ParticipantStrategy (A : Participant) : Set where
  field
    strategy : Run → Labels

    valid    : -- participant is honest
               A ∈ Hon
               -- only moves enabled by the semantics
             × (∀ {R : Run} {α : Label} → α ∈ strategy (R ∗) →
                 ∃[ R′ ] (R ——→[ α ] R′))
               -- only self-authorizations
             × (∀ {R : Run} {α : Label} → α ∈ strategy (R ∗) →
                 Allₘ (_≡ A) (authDecoration α))
               -- coherent secret lengths
             × (∀ {R : Run} {Δ Δ′ : List CommittedSecret} {ad : ∃Advertisement} →
                  auth-commit[ A , ad , Δ  ] ∈ strategy (R ∗) →
                  auth-commit[ A , ad , Δ′ ] ∈ strategy (R ∗) →
                    Δ ≡ Δ′)
               -- persistence
             × (∀ {R : Run} {T′ : ∃TimedConfiguration} {α : Label} → α ∈ strategy (R ∗)
                 → ∃[ α′ ] (R ——→[ α′ ] T′)
                 → ∃[ R″ ] (T′ ∷ˢ⟦ α ⟧ R ——→[ α ] R″) →
                   α ∈ strategy ((T′ ∷ˢ⟦ α ⟧ R) ∗))

open ParticipantStrategy public

HonestStrategies : Set
HonestStrategies = ∀ {A} → A ∈ Hon → ParticipantStrategy A

HonestMoves : Set
HonestMoves = List (Participant × Labels)

module AdvM (Adv : Participant) (Adv∉ : Adv ∉ Hon) where

  record AdversarialStrategy : Set where
    field
      strategy : Run → HonestMoves → Label

      valid :
        ∀ {R : Run} {moves : HonestMoves} →
          let α = strategy (R ∗) moves in
          ( -- pick from honest moves
            ∃[ A ]
              ( A ∈ Hon
              × authDecoration α ≡ just A
              × α ∈ concatMap proj₂ moves )
            -- independent move
          ⊎  authDecoration α ≡ nothing
          × (∀ δ → α ≢ delay[ δ ])
          × ∃[ R′ ] (R ——→[ α ] R′)
            -- move from dishonest participant
          ⊎ (∃[ B ]
               ( (authDecoration α ≡ just B)
               × (B ∉ Hon)
               × (∀ s → α ≢ auth-rev[ B , s ])
               × ∃[ R′ ] (R ——→[ α ] R′) ))
            -- delay
          ⊎ ∃[ δ ]
              ( (α ≡ delay[ δ ])
              × All (λ{ (_ , Λ) → (Λ ≡ []) ⊎ Any (λ{ delay[ δ′ ] → δ′ ≥ δ ; _ → ⊥ }) Λ}) moves )
            -- dishonest participant reveals secret
          ⊎ ∃[ B ] ∃[ s ]
              ( α ≡ auth-rev[ B , s ]
              × B ∉ Hon
              × ⟨ B ∶ s ♯ nothing ⟩ ∈ʳ (R ∗)
              × ∃[ R∗′ ] ∃[ Δ ] ∃[ ad ]
                  ( R∗′ ∈ prefixRuns (R ∗)
                  × strategy R∗′ [] ≡ auth-commit[ B , ad , Δ ]
                  × (s , nothing) ∈ Δ
                  -- T0D0 why not valid?
                  )
              )
          )
          ×
          (∀ {B ad Δ}
            → B ∉ Hon
            → α ≡ auth-commit[ B , ad , Δ ]
              -----------------------------
            → α ≡ strategy (R ∗) [])

  open AdversarialStrategy public

  Strategies : Set
  Strategies = AdversarialStrategy -- ^ adversarial strategy
             × HonestStrategies    -- ^ participant strategies

  runAdversary : Strategies → Run → Label
  runAdversary (S† , S) R =
    let R∗ = R ∗
    in strategy S† R∗ (mapWith∈ Hon (λ {A} A∈ → A , strategy (S A∈) R∗))

  data _-conforms-to-_ : Run → Strategies → Set where

    base : ∀ {ads cs ds} {Γ : Configuration ads cs ds} {SS : Strategies}

      → Initial Γ
        ----------------------------------------------
      → ((ads , cs , ds , Γ at 0) ∙ˢ) -conforms-to- SS

    step : ∀ {R : Run} {T′ : ∃TimedConfiguration} {SS : Strategies}
      → R -conforms-to- SS
      → R ——→[ runAdversary SS R ] T′
        -----------------------------------------------
      → (T′ ∷ˢ⟦ runAdversary SS R ⟧ R) -conforms-to- SS
