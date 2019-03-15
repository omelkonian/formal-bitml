------------------------------------------------------------------------
-- Small-step semantics for the BitML calculus.
------------------------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas #-}

open import Level        using (0ℓ)
open import Function     using (_on_; const; _∘_; id; _∋_; _$_; case_of_)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Bool    using (T; Bool; true; false; _∧_)
open import Data.Maybe   using (Maybe; just; nothing; maybe′)
open import Data.Nat     using (ℕ; suc; _+_; _≤_; _>_; _≟_)
open import Data.Product using (∃; ∃-syntax; Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂; isInj₁; isInj₂)
open import Data.Fin     using (Fin; fromℕ)
  renaming (zero to 0ᶠ; suc to sucᶠ; _≟_ to _≟ᶠ_)
open import Data.String  using ()
  renaming (length to lengthₛ)

open import Data.List using ( List; []; _∷_; [_]; _++_; map
                            ; length; filter; boolFilter; zip )
open import Data.List.All using (All)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Relation.Permutation.Inductive using (_↭_)

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋; True; False; toWitness; fromWitness)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary using (Decidable)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; decSetoid; refl; cong; sym)

module Semantics.InferenceRules
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))
  where

open import Utilities.Lists

open import Types                            Participant _≟ₚ_ Honest
open import BitML.Types                      Participant _≟ₚ_ Honest
open import BitML.DecidableEquality          Participant _≟ₚ_ Honest
open import Semantics.Actions.Types          Participant _≟ₚ_ Honest
open import Semantics.Configurations.Types   Participant _≟ₚ_ Honest
open import Semantics.Configurations.Helpers Participant _≟ₚ_ Honest

--------------------------------------------------------------------------------
-- Semantic rules for untimed configurations.

-- T0D0 generalize all Γ to Configuration′
-- T0D0 Keep transition labels?

infix -1 _—→_
data _—→_ : ∀ {ads cs ds ads′ cs′ ds′}
          → Configuration ads cs ds
          → Configuration ads′ cs′ ds′
          → Set where

  ------------------------------
  -- i) Rules for deposits

  [DEP-AuthJoin] :
    ∀ {A : Participant}
      {v v′ : Value}
      {ads cs ds} {Γ : Configuration ads cs ds}

      -----------------------------------------------------------

    → Configuration ads cs (A has v ∷ A has v′ ∷ ds) ∋
      (   (A has v ∷ A has v′ ∷ [])
      ∣∣ᵈˢ Γ
      )
      —→
      Configuration ads cs (A has (v + v′) ∷ ds) ∋
      (  ⟨ A , v ⟩ᵈ
      ∣∣ ⟨ A , v′ ⟩ᵈ
      ∶- refl & refl & refl & refl & refl & refl
      ∣∣ A auth[ Action A [] [] (v ∷ v′ ∷ []) [ A has (v + v′) ] ∋
                 (0ᶠ ↔ sucᶠ 0ᶠ) {pr₂ = fromWitness refl}
               ]∶- refl & refl & refl
      ∶- refl & refl & refl & refl & refl & refl
      ∣∣ Γ
      ∶- refl & refl & refl & refl & {!!} & {!!}
      )


  [DEP-Join] :
    ∀ {A : Participant}
      {v v′ : Value}
      {ads cs ds} {Γ : Configuration ads cs ds}

      ------------------------------------------------------------

    → Configuration ads cs (A has v ∷ A has v′ ∷ ds) ∋
      (  ⟨ A , v ⟩ᵈ
      ∣∣ ⟨ A , v′ ⟩ᵈ
      ∶- refl & refl & refl & refl & refl & refl
      ∣∣ A auth[ Action A [] [] (v ∷ v′ ∷ []) [ A has (v + v′) ] ∋
                 (0ᶠ ↔ sucᶠ 0ᶠ) {pr₂ = fromWitness refl}
               ]∶- refl & refl & refl
      ∶- refl & refl & refl & refl & refl & refl
      ∣∣ Γ
      ∶- refl & refl & refl & refl & {!!} & {!!}
      )
      —→ ⟨ A , v + v′ ⟩ᵈ
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & refl


  [DEP-AuthDivide] :
    ∀ {A : Participant}
      {v v′ : Value}
      {ads cs ds} {Γ : Configuration ads cs ds}

      --------------------------------------------------------------------------

    → Configuration ads cs (A has (v + v′) ∷ ds) ∋
      (  ⟨ A , v + v′ ⟩ᵈ
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & refl
      )
      —→
      Configuration ads cs (A has v ∷ A has v′ ∷ ds) ∋
      (Configuration [] [] (A has v ∷ A has v′ ∷ []) ∋
         ⟨ A , v + v′ ⟩ᵈ
      ∣∣ A auth[ Action A [] [] [ v + v′ ] (A has v ∷ A has v′ ∷ []) ∋
                 (0ᶠ ▷ v , v′ ) {pr₁ = fromWitness refl} {pr₂ = fromWitness refl}
               ]∶- refl & refl & refl
      ∶- refl & refl & refl & refl & {!!} & {!!}
      )
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & refl


  [DEP-Divide] :
    ∀ {A : Participant}
      {v v′ : Value}
      {ads cs ds} {Γ : Configuration ads cs ds}

      -------------------------------------------------------------------------

    → Configuration ads cs (A has v ∷ A has v′ ∷ ds) ∋
      ((Configuration [] [] (A has v ∷ A has v′ ∷ []) ∋
         ⟨ A , v + v′ ⟩ᵈ
      ∣∣ A auth[ Action A [] [] [ v + v′ ] (A has v ∷ A has v′ ∷ []) ∋
                 (0ᶠ ▷ v , v′) {pr₁ = fromWitness refl} {pr₂ = fromWitness refl}
               ]∶- refl & refl & refl
      ∶- refl & refl & refl & refl & {!!} & {!!}
      )
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & refl
      )
      —→
      Configuration ads cs (A has v ∷ A has v′ ∷ ds) ∋
        (A has v ∷ A has v′ ∷ []) ∣∣ᵈˢ Γ


  [DEP-AuthDonate] :
    ∀ {A B : Participant}
      {v : Value}
      {ads cs ds} {Γ : Configuration ads cs ds}

      ----------------------------------------------

    → Configuration ads cs (A has v ∷ ds) ∋
      (  ⟨ A , v ⟩ᵈ
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & refl
      )
      —→
      Configuration ads cs (B has v ∷ ds) ∋
      (Configuration [] [] [ B has v ] ∋
         ⟨ A , v ⟩ᵈ
      ∣∣ A auth[ Action A [] [] [ v ] [ B has v ] ∋
                 (0ᶠ ▷ᵈ B) {pr = fromWitness refl}
               ]∶- refl & refl & refl
      ∶- refl & refl & refl & refl & {!!} & {!!}
      )
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & SETₑ.\\-left {[ B has v ]}


  [DEP-Donate] :
    ∀ {A B : Participant}
      {v : Value}
      {ads cs ds} {Γ : Configuration ads cs ds}

      ---------------------------------------------------------------

    → Configuration ads cs (B has v ∷ ds) ∋
      (( Configuration [] [] [ B has v ] ∋
         ⟨ A , v ⟩ᵈ
      ∣∣ A auth[ Action A [] [] [ v ] [ B has v ] ∋
                 (0ᶠ ▷ᵈ B) {pr = fromWitness refl}
               ]∶- refl & refl & refl
      ∶- refl & refl & refl & refl & {!!} & {!!}
      )
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & SETₑ.\\-left {[ B has v ]}
      )
      —→
      Configuration ads cs (B has v ∷ ds) ∋
      ( ⟨ B , v ⟩ᵈ
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & SETₑ.\\-left {[ B has v ]}
      )


  -- T0D0 more deposits, sychronized amongst participants
  [DEP-AuthDestroy] :
    ∀ {A : Participant}
      {ads cs ds} {Γ : Configuration ads cs ds}
      {v : Value}

     ----------------------------------------------------------------

    → Configuration ads cs (A has v ∷ ds) ∋
      (  ⟨ A , v ⟩ᵈ
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & SETₑ.\\-left {[ A has v ]}
      )
      —→
      Configuration ads cs ds ∋
      (Configuration [] [] [] ∋
         ⟨ A , v ⟩ᵈ
      ∣∣ A auth[ Action A [] [] [ v ] [] ∋
                 destroy 0ᶠ
               ]∶- refl & refl & refl
      ∶- refl & refl & refl & refl & {!!} & {!!}
      )
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & refl


  [DEP-Destroy] :
    ∀ {A : Participant}
      {ads cs ds} {Γ : Configuration ads cs ds}
      {v : Value}

      -----------------------------------------

    → Configuration ads cs ds ∋
      ((Configuration [] [] [] ∋
      (  ⟨ A , v ⟩ᵈ
      ∣∣ A auth[ Action A [] [] [ v ] [] ∋
                 destroy 0ᶠ
               ]∶- refl & refl & refl
      ∶- refl & refl & refl & refl & {!!} & {!!}
      ))
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & refl
      )
      —→
      Γ

  ------------------------------------------------------------
  -- ii) Rules for contract advertisements and stipulation

  [C-Advertise] :
    ∀ {v vsᶜ vsᵍ} {ad : Advertisement v vsᶜ vsᵍ}
      {ads cs ds} {Γ : Configuration ads cs ds}

    → ∃[ p ] (p SETₚ.∈ participantsᵍ (G ad) → p SETₚ.∈ Hon)
    → (∀ d → d SETₑ.∈ depositsᵃ ad → deposit d SETₑ.∈ depositsᶜ Γ)

      ------------------------------------------------------------------------

    → Γ
      —→ Configuration ((v , vsᶜ , vsᵍ , ad) ∷ ads) cs ds ∋
      (  ` ad
      ∣∣ Γ
      ∶- refl & SETₐ.\\-left {[ v , vsᶜ , vsᵍ , ad ]} & refl & refl & refl & refl
      )


  [C-AuthCommit] :
    ∀ {A : Participant} {bs : List (⊤ ⊎ ⊥)}
      {v vsᶜ vsᵍ} {ad : Advertisement v vsᶜ vsᵍ}
      {ads rads cs ds}
      {Γ : Configuration′ (ads , rads) (cs , []) (ds , [])}
      {Δ : List (Configuration [] [] [])}

      -- rads are all satisfied
    → rads SETₐ.⊆ [ v , vsᶜ , vsᵍ , ad ]

      -- commitment of secrets is proper
    → let
        secrets =
          map (A ,_)
            (map (λ { (inj₁ tt  , x) → x , inj₁ ((lengthₛ x) , refl)
                    ; (inj₂ bot , x) → x , inj₂ bot })
              (zip bs (secretsᵖ A (G ad))))

      in ( -- 1. Δ is well-formed
           Δ ≡ fromSecrets secrets
         × -- 2. only dishonest participants are allowed to commit to ⊥ values
           All (λ{ (p , _ , n) → (p SETₚ.∈ Hon → (isInj₂ n ≡ nothing))}) secrets
         )

      -----------------------------------------------------------------------

    → Configuration ((v , vsᶜ , vsᵍ , ad) ∷ ads) cs ds ∋
      (  ` ad
      ∣∣ Γ
      ∶- refl & {!!} & refl & refl & refl & refl
      )
      —→
      Configuration ((v , vsᶜ , vsᵍ , ad) ∷ ads) cs ds ∋
      ((Configuration ((v , vsᶜ , vsᵍ , ad) ∷ ads) cs ds ∋
      (  ` ad
      ∣∣ Γ
      ∶- refl & {!!} & refl & refl & refl & refl
      ∣∅ Δ
      ))
      ∣∣ A auth[ ♯▷ ad ]∶- refl & refl & refl
      ∶- sym (++-identityʳ ((v , vsᶜ , vsᵍ , ad) ∷ ads))
       & SETₐ.\\-head {v , vsᶜ , vsᵍ , ad} {ads}
       & sym (++-identityʳ cs)
       & SETᶜ.\\-left {cs}
       & {!!}
       & {!!}
      )


  [C-AuthInit] :
    ∀ {A : Participant}
      {v vsᶜ vsᵍ} {ad : Advertisement v vsᶜ vsᵍ}
      {iᵍ : Index vsᵍ}
      {ads rads cs dsˡ dsʳ ds}
      {Γ : Configuration′ (ads , rads) (cs , []) (ds , [])}
      {p : ds ≡ dsˡ ++ [ A has (vsᵍ ‼ iᵍ) ] ++ dsʳ}

      -- rads are all satisfied
    → rads SETₐ.⊆ [ v , vsᶜ , vsᵍ , ad ]

      -- all participants have committed their secrets
    → All (λ p → p SETₚ.∈ committedParticipants Γ ad) (participantsᵍ (G ad))

      -------------------------------------------------------------------

    → Configuration ((v , vsᶜ , vsᵍ , ad) ∷ ads) cs ds ∋
      (  ` ad
      ∣∣ Γ
      ∶- refl & {!!} & refl & refl & refl & refl
      )
      —→
      Configuration ((v , vsᶜ , vsᵍ , ad) ∷ ads) cs (dsˡ ++ dsʳ) ∋
      ((Configuration ((v , vsᶜ , vsᵍ , ad) ∷ ads) cs ds ∋
         ` ad
      ∣∣ Γ
      ∶- refl & {!!} & refl & refl & refl & refl
      )
      ∣∣ A auth[ Action A [ v , vsᶜ , vsᵍ , ad ] [] [ vsᵍ ‼ iᵍ ] [] ∋
                 (ad ▷ˢ iᵍ) {pr = fromWitness refl}
               ]∶- refl & refl & refl
      ∶- sym (++-identityʳ ((v , vsᶜ , vsᵍ , ad) ∷ ads))
       & SETₐ.\\-head {v , vsᶜ , vsᵍ , ad} {ads}
       & sym (++-identityʳ cs)
       & SETᶜ.\\-left {cs}
       & {!!}
       & {!!}
      )


  [C-Init] :
    ∀ {v vsᶜ vsᵍ} {ad : Advertisement v vsᶜ vsᵍ}
      {ads cs ds} {Γ : Configuration ads cs ds}
      {rads} {Δ : Configuration′ ([] , rads) ([] , []) ([] , [])}

      -- rads are all satisfied
    → rads SETₐ.⊆ [ v , vsᶜ , vsᵍ , ad ]

      -- all participants have committed their secrets
    → All (λ p → p SETₚ.∈ committedParticipants Δ ad) (participantsᵍ (G ad))

      -- all participants have spent the required (persistent) deposits for stipulation
    → toStipulate (G ad) ≡ spentForStipulation Δ ad

      ----------------------------------------------------------------------

    → Configuration ((v , vsᶜ , vsᵍ , ad) ∷ ads) cs ds ∋
      ((Configuration ((v , vsᶜ , vsᵍ , ad) ∷ ads) cs ds ∋
         ` ad
      ∣∣ Γ
      ∶- refl & SETₐ.\\-left {[ v , vsᶜ , vsᵍ , ad ]} & refl & refl & refl & refl
      )
      ∣∣ Δ
      ∶- sym (++-identityʳ ((v , vsᶜ , vsᵍ , ad) ∷ ads))
       & {!!}
       & sym (++-identityʳ cs)
       & SETᶜ.\\-left {cs}
       & sym (++-identityʳ ds)
       & SETₑ.\\-left {ds}
      )
      —→
      Configuration ads ((v , vsᶜ , C ad) ∷ cs) ds ∋
      (  ⟨ C ad , v ⟩ᶜ
      ∣∣ Γ
      ∶- refl & refl & refl & SETᶜ.\\-left {[ v , vsᶜ , C ad ]} & refl & refl
      )



  ---------------------------------------------------
  -- iii) Rules for executing active contracts

  [C-Split] :
    ∀ {ads cs ds} {Γ : Configuration ads cs ds}
      {v vs} {c : Contract v vs}
      {cases : ContractCases}

      -- `split` command
    → (pr : Split cases v)
    → c ≡ split cases ∶- pr

      ------------------------------------------------------------

    → Configuration ads ((v , vs , [ c ]) ∷ cs) ds ∋
      (  ⟨ [ c ] , v ⟩ᶜ
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & refl
      )
      —→  casesToContracts cases
      ∣∣ᶜˢ Γ

  [C-AuthRev] :
    ∀ {A : Participant} {s : Secret} {n : ℕ} {n′ : ℕ ⊎ ⊥}
      {p : n′ ≡ inj₁ n}
      {ads cs ds} {Γ : Configuration ads cs ds}

      -- only valid lengths
    → (len_s : lengthₛ s ≡ n)

      -------------------------------------------------------------

    → Configuration ads cs ds ∋
      (  (⟨ A ∶ s ♯ n′ ⟩ {case p of λ{ refl → length→isValidSecret len_s}})
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & refl
      )
      —→
      Configuration ads cs ds ∋
      (   [ A , s , n , len_s ]
      ∣∣ˢˢ Γ
      )


  [C-PutRev] :
    ∀ {ads cs ds} {Γ : Configuration ads cs ds}
      {v vs″} {c : Contract v vs″}
      {v′ vs′} {c′ : Contract v′ vs′}
      {s s′ : Secrets} {p : Predicate s′}
      {vs : Values} {ds′ : Deposits}
      {ss : List ValidSecret}

      -- `put` command
    → (pr : Put v vs v′
          × s′ SETₛ.⊆ s
          × vs″ ≡ vs′ ++ vs)
    → c ≡ (put vs &reveal s if p ⇒ c′ ∶- pr)

      -- revealed secrets
    → map (proj₁ ∘ proj₂) ss ≡ s

      -- put deposits
    → map value ds′ ≡ vs

      -- predicate is true
    → ⟦ p ⟧ᵇ ≡ true

      ------------------------------------------------------------

    → Configuration ads ((v , vs″ , [ c ]) ∷ cs) (ds′ ++ ds) ∋
      (  ⟨ [ c ] , v ⟩ᶜ
      ∣∣ (ds′ ∣∣ᵈˢ (ss ∣∣ˢˢ Γ))
      ∶- refl & refl & refl & refl & refl & refl
      )
      —→
      Configuration ads ((v′ , vs′ , [ c′ ]) ∷ cs) ds ∋
      (  ⟨ [ c′ ] , v′ ⟩ᶜ
      ∣∣ (ss ∣∣ˢˢ Γ)
      ∶- refl & refl & refl & refl & refl & refl
      )

  [C-Withdraw] :
    ∀ {ads cs ds} {Γ : Configuration ads cs ds}
      {A : Participant}
      {v} {c : Contract v []}

      -- `withdraw` command
    → c ≡ withdraw A

      -------------------------------------------------------

    → Configuration ads ((v , [] , [ c ]) ∷ cs) ds ∋
      (  ⟨ [ c ] , v ⟩ᶜ
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & refl
      )
      —→
      Configuration ads cs (A has v ∷ ds) ∋
      (  ⟨ A , v ⟩ᵈ
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & refl
      )



  [C-AuthControl] :
    ∀ {ads cs ds} {Γ : Configuration ads cs ds}
      {A : Participant}
      {v vs} {contract : Contracts v vs} {i : Index contract}

      -- `auth` decoration
    → A SETₚ.∈ authDecorations (contract ‼ i)

      ------------------------------------------------------------------

    → Configuration ads ((v , vs , contract) ∷ cs) ds ∋
      (  ⟨ contract , v ⟩ᶜ
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & refl
      )
      —→
      Configuration ads ((v , vs , contract) ∷ cs) ds ∋
      (Configuration [] [ (v , vs , contract) ] [] ∋
         ⟨ contract , v ⟩ᶜ
      ∣∣ A auth[ contract ▷ᵇ i  ]∶- refl & refl & refl
      ∶- refl & refl & refl & SETᶜ.\\-same {[ v , vs , contract ]} & refl & refl
      )
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & refl


  [C-Control] :
    ∀ {ads cs ds} {Γ : Configuration ads cs ds}
      {v vs} {contract : Contracts v vs} {i : Index contract}

      ------------------------------------------------------------------

    → Configuration ads ((v , vs , contract) ∷ cs) ds ∋
      ((Configuration [] [ v , vs , contract ] [] ∋
          ⟨ contract , v ⟩ᶜ
      ∣∣ᵇ (0ᶠ , i , authDecorations (contract ‼ i))
      )
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & refl
      )
      —→
      Configuration ads ((v , vs , [ contract ‼ i ]) ∷ cs) ds ∋
      (  ⟨ [ contract ‼ i ] , v ⟩ᶜ
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & refl
      )


infix -1 _—→′_
data _—→′_ : ∀ {ads cs ds ads′ cs′ ds′}
          → Configuration ads cs ds
          → Configuration ads′ cs′ ds′
          → Set where

  [REORDER] : ∀ {ads cs ds ads′ cs′ ds′}
                {Γ Γ′ : Configuration ads cs ds}
                {Δ Δ′ : Configuration ads′ cs′ ds′}

    → Γ′ ≈ Γ  -- reorder input
    → Γ —→ Δ  -- propagate to bottom layer
    → Δ  ≈ Δ′ -- reorder output
      -------------
    → Γ′ —→′ Δ′

-----------------------------------------------------------------------------------
-- Semantic rules for timed configurations.

record TimedConfiguration (ads : AdvertisedContracts)
                          (cs  : ActiveContracts)
                          (ds  : Deposits)
                          : Set where

  constructor _at_
  field
    cfg  : Configuration ads cs ds
    time : Time

open TimedConfiguration

infix 3 _≈ₜ_
_≈ₜ_ : ∀ {ads cs ds} → TimedConfiguration ads cs ds → TimedConfiguration ads cs ds → Set
c ≈ₜ c′ = (time c ≡ time c′)
        × (cfgToList (cfg c) ↭ cfgToList (cfg c′))

infix -1 _—→ₜ_
data _—→ₜ_ : ∀ {ads cs ds ads′ cs′ ds′}
           → TimedConfiguration ads cs ds
           → TimedConfiguration ads′ cs′ ds′
           → Set where

  -- iv) Rules for handling time
  [Action] :
    ∀ {ads cs ds} {Γ : Configuration ads cs ds}
      {ads′ cs′ ds′} {Γ′ : Configuration ads′ cs′ ds′}
      {t : Time}

    → Γ —→ Γ′
      ----------------------------------------
    → Γ at t —→ₜ Γ′ at t

  [Delay] :
    ∀ {ads cs ds} {Γ : Configuration ads cs ds}
      {t δ : Time}

      ----------------------------------------
    → Γ at t —→ₜ Γ at (t + δ)

  [Timeout] :
    ∀ {ads cs ds} {Γ : Configuration ads cs ds}
      {ads′ cs′ ds′} {Γ″ : Configuration ads′ cs′ ds′}
      {v vs} {contract : Contracts v vs} {i : Index contract}
      {t : Time}

      {Γ′ : TimedConfiguration ads ((v , vs , contract) ∷ cs) ds}
    → Γ′ ≈ₜ (  ⟨ contract , v ⟩ᶜ
            ∣∣ Γ
            ∶- refl & refl & refl & refl & refl & refl
            ) at t

      -- all time constraints are satisfied
    → All (_≤ t) (timeDecorations (contract ‼ i))

      -- resulting state if we pick branch `i`
    → Configuration ads ((v , vs , [ contract ‼ i ]) ∷ cs) ds ∋
         ⟨ [ contract ‼ i ] , v ⟩ᶜ
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & refl
      —→
      Γ″

      ----------------------------------------

    → Γ′ —→ₜ Γ″ at t

infix -1 _—→ₜ′_
data _—→ₜ′_ : ∀ {ads cs ds ads′ cs′ ds′}
          → TimedConfiguration ads cs ds
          → TimedConfiguration ads′ cs′ ds′
          → Set where

  [REORDERₜ] : ∀ {ads cs ds ads′ cs′ ds′}
                 {Γ Γ′ : TimedConfiguration ads cs ds}
                 {Δ Δ′ : TimedConfiguration ads′ cs′ ds′}

    → Γ′ ≈ₜ Γ  -- reorder input
    → Γ —→ₜ Δ  -- propagate to bottom layer
    → Δ ≈ₜ Δ′ -- reorder output
      -------------
    → Γ′ —→ₜ′ Δ′

-----------------------------------------------------------------------------------
-- Reflexive transitive closure for —→.

infix  -1 _—↠_
infix  -2 start_
infixr -1 _—→⟨_⟩_⊢_
infix  0 _∎∎

data _—↠_ : ∀ {ads cs ds ads′ cs′ ds′}
          → Configuration ads cs ds
          → Configuration ads′ cs′ ds′
          → Set where

  _∎∎ : ∀ {ads cs ds}
          (M : Configuration ads cs ds)

      ------
    → M —↠ M

  _—→⟨_⟩_⊢_ : ∀ {ads cs ds ads′ cs′ ds′ ads″ cs″ ds″}
                (L    : Configuration ads cs ds)
                {L′   : Configuration ads cs ds}
                {M M′ : Configuration ads′ cs′ ds′}
                {N    : Configuration ads″ cs″ ds″}

    → L′ —→ M′
    → (L ≈ L′) × (M ≈ M′)
    → M —↠ N
      ------------
    → L —↠ N

start_ : ∀ {ads cs ds ads′ cs′ ds′}
            {M : Configuration ads cs ds}
            {N : Configuration ads′ cs′ ds′}

  → M —↠ N
    ------
  → M —↠ N

start M—↠N = M—↠N

-----------------------------------------------------------------------------------
-- Reflexive transitive closure for —→ₜ.

infix  -1 _—↠ₜ_
infix  -2 startₜ_
infixr -1 _—→ₜ⟨_⟩_⊢_
infix  0 _∎∎ₜ

data _—↠ₜ_ : ∀ {ads cs ds ads′ cs′ ds′}
           → TimedConfiguration ads cs ds
           → TimedConfiguration ads′ cs′ ds′
           → Set where

  _∎∎ₜ : ∀ {ads cs ds}
           (M : TimedConfiguration ads cs ds)

      -------
    → M —↠ₜ M

  _—→ₜ⟨_⟩_⊢_ : ∀ {ads cs ds ads′ cs′ ds′ ads″ cs″ ds″}
                 (L    : TimedConfiguration ads cs ds)
                 {L′   : TimedConfiguration ads cs ds}
                 {M M′ : TimedConfiguration ads′ cs′ ds′}
                 {N    : TimedConfiguration ads″ cs″ ds″}

    → L′ —→ₜ M′
    → (L ≈ₜ L′) × (M ≈ₜ M′)
    → M —↠ₜ N
      -------
    → L —↠ₜ N

startₜ_ : ∀ {ads cs ds ads′ cs′ ds′}
            {M : TimedConfiguration ads cs ds}
            {N : TimedConfiguration ads′ cs′ ds′}

  → M —↠ₜ N
    -------
  → M —↠ₜ N

startₜ M—↠N = M—↠N
