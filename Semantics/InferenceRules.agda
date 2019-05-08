------------------------------------------------------------------------
-- Small-step semantics for the BitML calculus.
------------------------------------------------------------------------
{-# OPTIONS --allow-unsolved-metas #-}

open import Level        using (0ℓ)
open import Function     using (_on_; const; _∘_; id; _∋_; _$_; case_of_)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Bool    using (T; Bool; true; false; _∧_)
open import Data.Maybe   using (Maybe; just; nothing; maybe′; Is-just)
open import Data.Nat     using (ℕ; suc; _+_; _≤_; _>_; _≟_)
open import Data.Product using (∃; ∃-syntax; Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Fin     using (Fin; fromℕ; toℕ)
  renaming (zero to 0ᶠ; suc to sucᶠ; _≟_ to _≟ᶠ_)
open import Data.String  using ()
  renaming (length to lengthₛ)

open import Data.List using ( List; []; _∷_; [_]; _++_; map; sum
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
open import Semantics.Labels.Types           Participant _≟ₚ_ Honest

--------------------------------------------------------------------------------
-- Semantic rules for untimed configurations.

-- T0D0 generalize all Γ to Configuration′
-- T0D0 Keep transition labels?

infix -1 _—→[_]_
data _—→[_]_ : ∀ {ads cs ds ads′ cs′ ds′}
             → Configuration ads cs ds
             → Label
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
      —→[ auth-join[ A , 0 ↔ 1 ] ]
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
      —→[ join[ 0 ↔ 1 ] ]
        ⟨ A , v + v′ ⟩ᵈ
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
      —→[ auth-divide[ A , 0 ▷ v , v′ ] ]
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
      —→[ divide[ 0 ▷ v , v′ ] ]
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
      —→[ auth-donate[ A , 0 ▷ᵈ B ] ]
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
      —→[ donate[ 0 ▷ᵈ B ] ]
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
      —→[ auth-destroy[ A , 0 ] ]
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
      —→[ destroy[ 1 ] ]
      Γ

  ------------------------------------------------------------
  -- ii) Rules for contract advertisements and stipulation

  [C-Advertise] :
    ∀ {v vsᶜ vsᵛ vsᵖ} {ad : Advertisement v vsᶜ vsᵛ vsᵖ}
      {ads cs ds} {Γ : Configuration ads cs ds}

    → ∃[ p ] (p SETₚ.∈ participantsᵍ (G ad) → p SETₚ.∈ Hon)
    → (∀ d → d SETₑᵣ.∈ depositsᵃ ad → deposit d SETₑ.∈ depositsᶜ Γ)

      ------------------------------------------------------------------------

    → Γ
      —→[ advertise[ v , vsᶜ , vsᵛ , vsᵖ , ad ] ]
      Configuration ((v , vsᶜ , vsᵛ , vsᵖ , ad) ∷ ads) cs ds ∋
      (  ` ad
      ∣∣ Γ
      ∶- refl & SETₐ.\\-left {[ v , vsᶜ , vsᵛ , vsᵖ , ad ]} & refl & refl & refl & refl
      )


  [C-AuthCommit] :
    ∀ {A : Participant} {bs : List (Maybe ⊤)}
      {v vsᶜ vsᵛ vsᵖ} {ad : Advertisement v vsᶜ vsᵛ vsᵖ}
      {ads rads cs ds}
      {Γ : Configuration′ (ads , rads) (cs , []) (ds , [])}
      {Δ : List (Configuration [] [] [])}

      -- rads are all satisfied
    → rads SETₐ.⊆ [ v , vsᶜ , vsᵛ , vsᵖ , ad ]

      -- commitment of secrets is proper
    → let
        secrets =
          map (A ,_)
            (map (λ { (just tt , x) → x , just ((lengthₛ x) , refl)
                    ; (nothing , x) → x , nothing })
              (zip bs (secretsᵖ A (G ad))))

      in ( -- 1. Δ is well-formed
           Δ ≡ fromSecrets secrets
         × -- 2. only dishonest participants are allowed to commit to invalid lengths
           All (λ{ (p , _ , n) → (p SETₚ.∈ Hon → Is-just n)}) secrets
         )

      -----------------------------------------------------------------------

    → Configuration ((v , vsᶜ , vsᵛ , vsᵖ , ad) ∷ ads) cs ds ∋
      (  ` ad
      ∣∣ Γ
      ∶- refl & {!!} & refl & refl & refl & refl
      )
      —→[ auth-commit[ A , (v , vsᶜ , vsᵛ , vsᵖ , ad) , secrets ] ]
      Configuration ((v , vsᶜ , vsᵛ , vsᵖ , ad) ∷ ads) cs ds ∋
      ((Configuration ((v , vsᶜ , vsᵛ , vsᵖ , ad) ∷ ads) cs ds ∋
      (  ` ad
      ∣∣ Γ
      ∶- refl & {!!} & refl & refl & refl & refl
      ∣∅ Δ
      ))
      ∣∣ A auth[ ♯▷ ad ]∶- refl & refl & refl
      ∶- sym (++-identityʳ ((v , vsᶜ , vsᵛ , vsᵖ , ad) ∷ ads))
       & SETₐ.\\-head {v , vsᶜ , vsᵛ , vsᵖ , ad} {ads}
       & sym (++-identityʳ cs)
       & SETᶜ.\\-left {cs}
       & {!!}
       & {!!}
      )


  [C-AuthInit] :
    ∀ {A : Participant}
      {v vsᶜ vsᵛ vsᵖ} {ad : Advertisement v vsᶜ vsᵛ vsᵖ}
      {iᵖ : Index vsᵖ}
      {ads rads cs dsˡ dsʳ ds}
      {Γ : Configuration′ (ads , rads) (cs , []) (ds , [])}
      {p : ds ≡ dsˡ ++ [ A has (vsᵖ ‼ iᵖ) ] ++ dsʳ}

      -- rads are all satisfied
    → rads SETₐ.⊆ [ v , vsᶜ , vsᵛ , vsᵖ , ad ]

      -- all participants have committed their secrets
    → All (λ p → p SETₚ.∈ committedParticipants Γ ad) (participantsᵍ (G ad))

      -------------------------------------------------------------------

    → Configuration ((v , vsᶜ , vsᵛ , vsᵖ , ad) ∷ ads) cs ds ∋
      (  ` ad
      ∣∣ Γ
      ∶- refl & {!!} & refl & refl & refl & refl
      )
      —→[ auth-init[ A , (v , vsᶜ , vsᵛ , vsᵖ , ad) , toℕ iᵖ ] ]
      Configuration ((v , vsᶜ , vsᵛ , vsᵖ , ad) ∷ ads) cs (dsˡ ++ dsʳ) ∋
      ((Configuration ((v , vsᶜ , vsᵛ , vsᵖ , ad) ∷ ads) cs ds ∋
         ` ad
      ∣∣ Γ
      ∶- refl & {!!} & refl & refl & refl & refl
      )
      ∣∣ A auth[ Action A [ v , vsᶜ , vsᵛ , vsᵖ , ad ] [] [ vsᵖ ‼ iᵖ ] [] ∋
                 (ad ▷ˢ iᵖ) {pr = fromWitness refl}
               ]∶- refl & refl & refl
      ∶- sym (++-identityʳ ((v , vsᶜ , vsᵛ , vsᵖ , ad) ∷ ads))
       & SETₐ.\\-head {v , vsᶜ , vsᵛ , vsᵖ , ad} {ads}
       & sym (++-identityʳ cs)
       & SETᶜ.\\-left {cs}
       & {!!}
       & {!!}
      )


  [C-Init] :
    ∀ {v vsᶜ vsᵛ vsᵖ} {ad : Advertisement v vsᶜ vsᵛ vsᵖ}
      {ads cs ds} {Γ : Configuration ads cs ds}
      {rads} {Δ : Configuration′ ([] , rads) ([] , []) ([] , [])}

      -- rads are all satisfied
    → rads SETₐ.⊆ [ v , vsᶜ , vsᵛ , vsᵖ , ad ]

      -- all participants have committed their secrets
    → All (λ p → p SETₚ.∈ committedParticipants Δ ad) (participantsᵍ (G ad))

      -- all participants have spent the required (persistent) deposits for stipulation
    → toStipulate (G ad) ≡ spentForStipulation Δ ad

      ----------------------------------------------------------------------

    → Configuration ((v , vsᶜ , vsᵛ , vsᵖ , ad) ∷ ads) cs ds ∋
      ((Configuration ((v , vsᶜ , vsᵛ , vsᵖ , ad) ∷ ads) cs ds ∋
         ` ad
      ∣∣ Γ
      ∶- refl & SETₐ.\\-left {[ v , vsᶜ , vsᵛ , vsᵖ , ad ]} & refl & refl & refl & refl
      )
      ∣∣ Δ
      ∶- sym (++-identityʳ ((v , vsᶜ , vsᵛ , vsᵖ , ad) ∷ ads))
       & {!refl!}
       & sym (++-identityʳ cs)
       & SETᶜ.\\-left {cs}
       & sym (++-identityʳ ds)
       & SETₑ.\\-left {ds}
      )
      —→[ init[ v , vsᶜ , vsᵛ , vsᵖ , ad ] ]
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
      {cases : ContractCases vs}

      -- `split` command
    → (pr : v ≡ sum (map proj₁ cases))
    → c ≡ split cases ∶- pr

      ------------------------------------------------------------

    → Configuration ads ((v , vs , [ c ]) ∷ cs) ds ∋
      (  ⟨ [ c ] , v ⟩ᶜ
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & refl
      )
      —→[ split ]
        casesToContracts cases
      ∣∣ᶜˢ Γ

  [C-AuthRev] :
    ∀ {A : Participant} {s : Secret} {n : ℕ}
      {ads cs ds} {Γ : Configuration ads cs ds}

      -- only valid lengths
    → (len_s : lengthₛ s ≡ n)

      -------------------------------------------------------------

    → Configuration ads cs ds ∋
      (  (⟨ A ∶ s ♯ just n ⟩ {length→isValidSecret len_s})
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & refl
      )
      —→[ auth-rev[ A , s ] ]
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
    → (pr : Put vs vs′ vs″
          × v′ ≡ v + sum vs
          × s′ SETₛ.⊆ s)
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
      —→[ put[ vs , s ] ]
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
      —→[ withdraw[ A , v ] ]
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
      —→[ auth-control[ A , (v , vs , contract) ▷ᵇ i ] ]
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
      —→[ empty ]
      Configuration ads ((v , vs , [ contract ‼ i ]) ∷ cs) ds ∋
      (  ⟨ [ contract ‼ i ] , v ⟩ᶜ
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & refl
      )


-----------------------------------------------------------------------------------
-- Semantic rules for timed configurations.

infix 3 _≈ₜ_
_≈ₜ_ : ∀ {ads cs ds} → TimedConfiguration ads cs ds → TimedConfiguration ads cs ds → Set
c ≈ₜ c′ = (time c ≡ time c′)
        × (cfgToList (cfg c) ↭ cfgToList (cfg c′))

infix -1 _—→ₜ[_]_
data _—→ₜ[_]_ : ∀ {ads cs ds ads′ cs′ ds′}
              → TimedConfiguration ads cs ds
              → Label
              → TimedConfiguration ads′ cs′ ds′
              → Set where

  -- iv) Rules for handling time
  [Action] :
    ∀ {ads cs ds} {Γ : Configuration ads cs ds}
      {ads′ cs′ ds′} {Γ′ : Configuration ads′ cs′ ds′}
      {t : Time} {a : Label}


    → Γ —→[ a ] Γ′
      ----------------------------------------
    → Γ at t —→ₜ[ a ] Γ′ at t

  [Delay] :
    ∀ {ads cs ds} {Γ : Configuration ads cs ds}
      {t δ : Time}

      ----------------------------------------
    → Γ at t —→ₜ[ delay[ δ ] ] Γ at (t + δ)

  [Timeout] :
    ∀ {ads cs ds} {Γ : Configuration ads cs ds}
      {ads′ cs′ ds′} {Γ″ : Configuration ads′ cs′ ds′}
      {v vs} {contract : Contracts v vs} {i : Index contract}
      {t : Time} {a : Label}

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
      —→[ a ]
      Γ″

      ----------------------------------------

    → Γ′ —→ₜ[ a ] Γ″ at t

-----------------------------------------------------------------------------------
-- Reflexive transitive closure for —→.

infix  -1 _—↠[_]_
infix  -2 start_
infixr -1 _—→⟨_⟩_⊢_
infix  0 _∎∎

data _—↠[_]_ : ∀ {ads cs ds ads′ cs′ ds′}
             → Configuration ads cs ds
             → Labels
             → Configuration ads′ cs′ ds′
             → Set where

  _∎∎ : ∀ {ads cs ds}
          (M : Configuration ads cs ds)

      ------------
    → M —↠[ [] ] M

  _—→⟨_⟩_⊢_ : ∀ {ads cs ds ads′ cs′ ds′ ads″ cs″ ds″ a as}
                (L    : Configuration ads cs ds)
                {L′   : Configuration ads cs ds}
                {M M′ : Configuration ads′ cs′ ds′}
                {N    : Configuration ads″ cs″ ds″}

    → L′ —→[ a ] M′
    → (L ≈ L′) × (M ≈ M′)
    → M —↠[ as ]  N
      -------------------
    → L —↠[ a ∷ as ] N

start_ : ∀ {ads cs ds ads′ cs′ ds′ as}
            {M : Configuration ads cs ds}
            {N : Configuration ads′ cs′ ds′}

  → M —↠[ as ] N
    ------------
  → M —↠[ as ] N

start M—↠N = M—↠N

-----------------------------------------------------------------------------------
-- Reflexive transitive closure for —→ₜ.

infix  -1 _—↠ₜ[_]_
infix  -2 startₜ_
infixr -1 _—→ₜ⟨_⟩_⊢_
infix  0 _∎∎ₜ

data _—↠ₜ[_]_ : ∀ {ads cs ds ads′ cs′ ds′}
              → TimedConfiguration ads cs ds
              → Labels
              → TimedConfiguration ads′ cs′ ds′
              → Set where

  _∎∎ₜ : ∀ {ads cs ds}
           (M : TimedConfiguration ads cs ds)

      -------------
    → M —↠ₜ[ [] ] M

  _—→ₜ⟨_⟩_⊢_ : ∀ {ads cs ds ads′ cs′ ds′ ads″ cs″ ds″ a as}
                 (L    : TimedConfiguration ads cs ds)
                 {L′   : TimedConfiguration ads cs ds}
                 {M M′ : TimedConfiguration ads′ cs′ ds′}
                 {N    : TimedConfiguration ads″ cs″ ds″}

    → L′ —→ₜ[ a ] M′
    → (L ≈ₜ L′) × (M ≈ₜ M′)
    → M —↠ₜ[ as ] N
      ---------------------
    → L —↠ₜ[ a ∷ as ] N

startₜ_ : ∀ {ads cs ds ads′ cs′ ds′ as}
            {M : TimedConfiguration ads cs ds}
            {N : TimedConfiguration ads′ cs′ ds′}

  → M —↠ₜ[ as ] N
    -------------
  → M —↠ₜ[ as ] N

startₜ M—↠N = M—↠N
