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

open import Data.Vec as V using (Vec)

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋; True; False; toWitness; fromWitness)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary using (Decidable)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; decSetoid; refl; cong; sym)

open import Prelude.Lists

open import BitML.BasicTypes
open import BitML.Predicate.Base hiding (`)
open import BitML.Predicate.Semantics

module BitML.Semantics.InferenceRules
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))
  where

open import BitML.Contracts.Types                  Participant _≟ₚ_ Honest
open import BitML.Contracts.DecidableEquality      Participant _≟ₚ_ Honest
open import BitML.Semantics.Actions.Types          Participant _≟ₚ_ Honest
open import BitML.Semantics.Configurations.Types   Participant _≟ₚ_ Honest
open import BitML.Semantics.Configurations.Helpers Participant _≟ₚ_ Honest
open import BitML.Semantics.Labels.Types           Participant _≟ₚ_ Honest

--------------------------------------------------------------------------------
-- Semantic rules for untimed configurations.

-- T0D0 generalize all Γ to Configuration′

variable
  A B : Participant
  Γ Γ₀ : Configuration Iᶜᶠ[ ads , cs , ds ]
  Γ′ : Configuration Iᶜᶠ[ ads′ , cs′ , ds′ ]
  Γ″ : Configuration Iᶜᶠ[ ads″ , cs″ , ds″ ]
  t t′ δ : Time
  α : Label
  αs : Labels

infix -1 _—→[_]_
data _—→[_]_ : Configuration cfi
             → Label
             → Configuration cfi′
             → Set where

  ------------------------------
  -- i) Rules for deposits

  [DEP-AuthJoin] :

      -----------------------------------------------------------

      Configuration Iᶜᶠ[ ads , cs , A has v ∷ A has v′ ∷ ds ] ∋
      (   (A has v ∷ A has v′ ∷ [])
      ∣∣ᵈˢ Γ
      )
      —→[ auth-join[ A , 0 ↔ 1 ] ]
      Configuration Iᶜᶠ[ ads , cs , A has (v + v′) ∷ ds ] ∋
      (  ⟨ A , v ⟩ᵈ
      ∣∣ ⟨ A , v′ ⟩ᵈ
      ∶- refl & refl & refl & refl & refl & refl
      ∣∣ A auth[ Action A Iᵃᶜ[ [] , [] , v ∷ v′ ∷ [] , [ A has (v + v′) ] ] ∋
                 (0ᶠ ↔ sucᶠ 0ᶠ) {pr₂ = fromWitness refl}
               ]∶- refl & refl & refl & refl & refl & refl
      ∶- refl & refl & refl & refl & refl & refl
      ∣∣ Γ
      ∶- refl & refl & refl & refl & {!!} & {!!}
      )


  [DEP-Join] :

      ------------------------------------------------------------

      Configuration Iᶜᶠ[ ads , cs , A has v ∷ A has v′ ∷ ds ] ∋
      (  ⟨ A , v ⟩ᵈ
      ∣∣ ⟨ A , v′ ⟩ᵈ
      ∶- refl & refl & refl & refl & refl & refl
      ∣∣ A auth[ Action A Iᵃᶜ[ [] , [] , v ∷ v′ ∷ [] , [ A has (v + v′) ] ] ∋
                 (0ᶠ ↔ sucᶠ 0ᶠ) {pr₂ = fromWitness refl}
               ]∶- refl & refl & refl & refl & refl & refl
      ∶- refl & refl & refl & refl & refl & refl
      ∣∣ Γ
      ∶- refl & refl & refl & refl & {!!} & {!!}
      )
      —→[ join[ 0 ↔ 1 ] ]
        ⟨ A , v + v′ ⟩ᵈ
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & refl


  [DEP-AuthDivide] :

      --------------------------------------------------------------------------

      Configuration Iᶜᶠ[ ads , cs , A has (v + v′) ∷ ds ] ∋
      (  ⟨ A , v + v′ ⟩ᵈ
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & refl
      )
      —→[ auth-divide[ A , 0 ▷ v , v′ ] ]
      Configuration Iᶜᶠ[ ads , cs , A has v ∷ A has v′ ∷ ds ] ∋
      (Configuration Iᶜᶠ[ [] , [] , A has v ∷ A has v′ ∷ [] ] ∋
         ⟨ A , v + v′ ⟩ᵈ
      ∣∣ A auth[ Action A Iᵃᶜ[ [] , [] , [ v + v′ ] , A has v ∷ A has v′ ∷ [] ] ∋
                 (0ᶠ ▷ v , v′ ) {pr₁ = fromWitness refl} {pr₂ = fromWitness refl}
               ]∶- refl & refl & refl & refl & refl & refl
      ∶- refl & refl & refl & refl & {!!} & {!!}
      )
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & refl


  [DEP-Divide] :

      -------------------------------------------------------------------------

      Configuration Iᶜᶠ[ ads , cs , A has v ∷ A has v′ ∷ ds ] ∋
      ((Configuration Iᶜᶠ[ [] , [] , A has v ∷ A has v′ ∷ [] ] ∋
         ⟨ A , v + v′ ⟩ᵈ
      ∣∣ A auth[ Action A Iᵃᶜ[ [] , [] , [ v + v′ ] , A has v ∷ A has v′ ∷ [] ] ∋
                 (0ᶠ ▷ v , v′) {pr₁ = fromWitness refl} {pr₂ = fromWitness refl}
               ]∶- refl & refl & refl & refl & refl & refl
      ∶- refl & refl & refl & refl & {!!} & {!!}
      )
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & refl
      )
      —→[ divide[ 0 ▷ v , v′ ] ]
      Configuration Iᶜᶠ[ ads , cs , A has v ∷ A has v′ ∷ ds ] ∋
        (A has v ∷ A has v′ ∷ []) ∣∣ᵈˢ Γ


  [DEP-AuthDonate] :

      ------------------------------------------------------------

      Configuration Iᶜᶠ[ ads , cs , A has v ∷ ds ] ∋
      (  ⟨ A , v ⟩ᵈ
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & refl
      )
      —→[ auth-donate[ A , 0 ▷ᵈ B ] ]
      Configuration Iᶜᶠ[ ads , cs , B has v ∷ ds ] ∋
      (Configuration Iᶜᶠ[ [] , [] , [ B has v ] ] ∋
         ⟨ A , v ⟩ᵈ
      ∣∣ A auth[ Action A Iᵃᶜ[ [] , [] , [ v ] , [ B has v ] ] ∋
                 (0ᶠ ▷ᵈ B) {pr = fromWitness refl}
               ]∶- refl & refl & refl & refl & refl & refl
      ∶- refl & refl & refl & refl & {!!} & {!!}
      )
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & SETₑ.\\-left {[ B has v ]}


  [DEP-Donate] :

      ---------------------------------------------------------------

      Configuration Iᶜᶠ[ ads , cs , B has v ∷ ds ] ∋
      (( Configuration Iᶜᶠ[ [] , [] , [ B has v ] ] ∋
         ⟨ A , v ⟩ᵈ
      ∣∣ A auth[ Action A Iᵃᶜ[ [] , [] , [ v ] , [ B has v ] ] ∋
                 (0ᶠ ▷ᵈ B) {pr = fromWitness refl}
               ]∶- refl & refl & refl & refl & refl & refl
      ∶- refl & refl & refl & refl & {!!} & {!!}
      )
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & SETₑ.\\-left {[ B has v ]}
      )
      —→[ donate[ 0 ▷ᵈ B ] ]
      Configuration Iᶜᶠ[ ads , cs , B has v ∷ ds ] ∋
      ( ⟨ B , v ⟩ᵈ
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & SETₑ.\\-left {[ B has v ]}
      )


  -- T0D0 more deposits, sychronized amongst participants
  [DEP-AuthDestroy] :

      ----------------------------------------------------------------

      Configuration Iᶜᶠ[ ads , cs , A has v ∷ ds ] ∋
      (  ⟨ A , v ⟩ᵈ
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & SETₑ.\\-left {[ A has v ]}
      )
      —→[ auth-destroy[ A , 0 ] ]
      Configuration Iᶜᶠ[ ads , cs , ds ] ∋
      (Configuration Iᶜᶠ[ [] , [] , [] ] ∋
         ⟨ A , v ⟩ᵈ
      ∣∣ A auth[ Action A Iᵃᶜ[ [] , [] , [ v ] , [] ] ∋
                 destroy 0ᶠ
               ]∶- refl & refl & refl & refl & refl & refl
      ∶- refl & refl & refl & refl & {!!} & {!!}
      )
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & refl


  [DEP-Destroy] :

      -----------------------------------------

      Configuration Iᶜᶠ[ ads , cs , ds ] ∋
      ((Configuration Iᶜᶠ[ [] , [] , [] ] ∋
      (  ⟨ A , v ⟩ᵈ
      ∣∣ A auth[ Action A Iᵃᶜ[ [] , [] , [ v ] , [] ] ∋
                 destroy 0ᶠ
               ]∶- refl & refl & refl & refl & refl & refl
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

      ∃[ p ] (p SETₚ.∈ participantsᵍ (G ad) → p SETₚ.∈ Hon) -- T0D0 use Any
    → (∀ d → d SETₑᵣ.∈ depositsᵃ ad → deposit d SETₑ.∈ depositsᶜ Γ)

      ------------------------------------------------------------------------

    → Γ
      —→[ advertise[ ci , pi , ad ] ]
      Configuration Iᶜᶠ[ (ci , pi , ad) ∷ ads , cs , ds ] ∋
      (  ` ad
      ∣∣ Γ
      ∶- refl & SETₐ.\\-left {[ ci , pi , ad ]} & refl & refl & refl & refl
      )


  [C-AuthCommit] :
    ∀ {ci pi ad} {secrets : List CommittedSecret}
      {Γ : Configuration′ Iᶜᶠ[ ads & rads , cs & [] , ds & [] ]}
      {pr : map proj₁ secrets ≡ secretsᵖ A (G ad)}

      -- rads are all satisfied
    → rads SETₐ.⊆ [ ci , pi , ad ]

      -- only dishonest participants are allowed to commit to invalid lengths
    → (A SETₚ.∈ Hon → All (λ {(_ , m) → Is-just m }) secrets)

      -----------------------------------------------------------------------

    → Configuration Iᶜᶠ[ (ci , pi , ad) ∷ ads ,  cs , ds ]  ∋
      (  ` ad
      ∣∣ Γ
      ∶- refl & {!!} & refl & refl & refl & refl
      )
      —→[ auth-commit[ A , (ci , pi , ad) , secrets ] ]
      Configuration Iᶜᶠ[ (ci , pi , ad) ∷ ads , cs , ds ] ∋
      ((Configuration Iᶜᶠ[ (ci , pi , ad) ∷ ads , cs , ds ] ∋
      (  ` ad
      ∣∣ Γ
      ∶- refl & {!!} & refl & refl & refl & refl
      ∣∅ map (A ,_) secrets
      ))
      ∣∣ A auth[ ♯▷ ad ]∶- refl & refl & refl & refl & refl & refl
      ∶- sym (++-identityʳ ((ci , pi , ad) ∷ ads))
       & SETₐ.\\-head {ci , pi , ad} {ads}
       & sym (++-identityʳ cs)
       & SETᶜ.\\-left {cs}
       & {!!}
       & {!!}
      )


  [C-AuthInit] :
    ∀ {ci pi ad}
    → let vsᵖ = persistentDeposits pi in
      {iᵖ : Index vsᵖ}
      {Γ : Configuration′ Iᶜᶠ[ ads & rads , cs & [] , ds & [] ]}
      {p : ds ≡ dsˡ ++ [ A has (vsᵖ ‼ iᵖ) ] ++ dsʳ}

      -- rads are all satisfied
    → rads SETₐ.⊆ [ ci , pi , ad ]

      -- all participants have committed their secrets
    → All (λ p → p SETₚ.∈ committedParticipants Γ ad) (participantsᵍ (G ad))

      ----------------------------------------------------------------------

    → Configuration Iᶜᶠ[ (ci , pi , ad) ∷ ads , cs , ds ] ∋
      (  ` ad
      ∣∣ Γ
      ∶- refl & {!!} & refl & refl & refl & refl
      )
      —→[ auth-init[ A , (ci , pi , ad) , toℕ iᵖ ] ]
      Configuration Iᶜᶠ[ (ci , pi , ad) ∷ ads , cs , dsˡ ++ dsʳ ] ∋
      ((Configuration Iᶜᶠ[ (ci , pi , ad) ∷ ads , cs , ds ] ∋
         ` ad
      ∣∣ Γ
      ∶- refl & {!!} & refl & refl & refl & refl
      )
      ∣∣ A auth[ Action A Iᵃᶜ[ [ ci , pi , ad ] , [] , [ vsᵖ ‼ iᵖ ] , [] ] ∋
                 (ad ▷ˢ iᵖ) {pr = fromWitness refl}
               ]∶- refl & refl & refl & refl & refl & refl
      ∶- sym (++-identityʳ ((ci , pi , ad) ∷ ads))
       & SETₐ.\\-head {ci , pi , ad} {ads}
       & sym (++-identityʳ cs)
       & SETᶜ.\\-left {cs}
       & {!!}
       & {!!}
      )


  [C-Init] :
    ∀ {Δ : Configuration′ Iᶜᶠ[ [] & rads , [] & [] , [] & [] ]}

      -- rads are all satisfied
    → rads SETₐ.⊆ [ ci , pi , ad ]

      -- all participants have committed their secrets
    → All (λ p → p SETₚ.∈ committedParticipants Δ ad) (participantsᵍ (G ad))

      -- all participants have spent the required (persistent) deposits for stipulation
    → toStipulate (G ad) ≡ spentForStipulation Δ ad

      ----------------------------------------------------------------------

    → Configuration Iᶜᶠ[ (ci , pi , ad) ∷ ads , cs , ds ] ∋
      ((Configuration Iᶜᶠ[ (ci , pi , ad) ∷ ads , cs , ds ] ∋
         ` ad
      ∣∣ Γ
      ∶- refl & SETₐ.\\-left {[ ci , pi , ad ]} & refl & refl & refl & refl
      )
      ∣∣ Δ
      ∶- sym (++-identityʳ ((ci , pi , ad) ∷ ads))
       & {!refl!}
       & sym (++-identityʳ cs)
       & SETᶜ.\\-left {cs}
       & sym (++-identityʳ ds)
       & SETₑ.\\-left {ds}
      )
      —→[ init[ ci , pi , ad ] ]
      Configuration Iᶜᶠ[ ads , (ci , C ad) ∷ cs , ds ] ∋
      (  ⟨ C ad ⟩ᶜ
      ∣∣ Γ
      ∶- refl & refl & refl & SETᶜ.\\-left {[ ci , C ad ]} & refl & refl
      )



  ---------------------------------------------------
  -- iii) Rules for executing active contracts

  [C-Split] :
    ∀ {c : Contract Iᶜ[ v , vs ]}
      {cases : ContractCases vs}

      -- `split` command
    → (pr : v ≡ sum (map proj₁ cases))
    → c ≡ split cases ∶- pr

      ------------------------------------------------------------

    → Configuration Iᶜᶠ[ ads , (Iᶜ[ v , vs ] , [ c ]) ∷ cs , ds ] ∋
      (  ⟨ [ c ] ⟩ᶜ
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & refl
      )
      —→[ split ]
        casesToContracts cases
      ∣∣ᶜˢ Γ

  [C-AuthRev] :

      -- only valid lengths
      (len_s : lengthₛ s ≡ n)

      -------------------------------------------------------------

    → Configuration Iᶜᶠ[ ads , cs , ds ] ∋
      (  (⟨ A ∶ s ♯ just n ⟩ {length→isValidSecret len_s})
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & refl
      )
      —→[ auth-rev[ A , s ] ]
      Configuration Iᶜᶠ[ ads , cs , ds ] ∋
      (   [ A , s , n , len_s ]
      ∣∣ˢˢ Γ
      )


  [C-PutRev] :
    ∀ {v vs″} {c : Contract Iᶜ[ v , vs″ ]}
      {v′ vs′} {c′ : Contracts Iᶜ[ v′ , vs′ ]}
      {n : ℕ} {p : Predicate (Ctx n)}
      {vs : Values} {ds′ : Deposits}
      {Δ : Vec ValidSecret n}

    → let ss = V.map (proj₁ ∘ proj₂) Δ in

      -- `put` command
      (pr : Put vs vs′ vs″
          × v′ ≡ v + sum vs)
    → c ≡ (put vs &reveal ss if p ⇒ c′ ∶- pr)

      -- put deposits
    → map value ds′ ≡ vs

      -- predicate is true
    → ⟦ p ⟧ ss ≡ true

      ------------------------------------------------------------

    → Configuration Iᶜᶠ[ ads , (Iᶜ[ v , vs″ ] , [ c ]) ∷ cs , ds′ ++ ds ] ∋
      (  ⟨ [ c ] ⟩ᶜ
      ∣∣ (ds′ ∣∣ᵈˢ (V.toList Δ ∣∣ˢˢ Γ))
      ∶- refl & refl & refl & refl & refl & refl
      )
      —→[ put[ vs , V.toList ss ] ]
      Configuration Iᶜᶠ[ ads , (Iᶜ[ v′ , vs′ ] , c′) ∷ cs , ds ] ∋
      (  ⟨ c′ ⟩ᶜ
      ∣∣ (V.toList Δ ∣∣ˢˢ Γ)
      ∶- refl & refl & refl & refl & refl & refl
      )

  [C-Withdraw] :

      -------------------------------------------------------

      Configuration Iᶜᶠ[ ads , (Iᶜ[ v , [] ] , [ withdraw A ]) ∷ cs , ds ] ∋
      (  ⟨ [ withdraw A ] ⟩ᶜ
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & refl
      )
      —→[ withdraw[ A , v ] ]
      Configuration Iᶜᶠ[ ads , cs , A has v ∷ ds ] ∋
      (  ⟨ A , v ⟩ᵈ
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & refl
      )


  [C-AuthControl] :
    ∀ {ci} {contract : Contracts ci} {i : Index contract}

      -- `auth` decoration
    → A SETₚ.∈ authDecorations (contract ‼ i)

      ------------------------------------------------------------------

    → Configuration Iᶜᶠ[ ads , (ci , contract) ∷ cs , ds ] ∋
      (  ⟨ contract ⟩ᶜ
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & refl
      )
      —→[ auth-control[ A , (ci , contract) ▷ᵇ i ] ]
      Configuration Iᶜᶠ[ ads , (ci , contract) ∷ cs , ds ] ∋
      (Configuration Iᶜᶠ[ [] , [ (ci , contract) ] , [] ] ∋
         ⟨ contract ⟩ᶜ
      ∣∣ A auth[ contract ▷ᵇ i  ]∶- refl & refl & refl & refl & refl & refl
      ∶- refl & refl & refl & SETᶜ.\\-same {[ ci , contract ]} & refl & refl
      )
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & refl


  [C-Control] :
    ∀ {contract : Contracts ci} {i : Index contract}

      ------------------------------------------------------------------

    → Configuration Iᶜᶠ[ ads , (ci , contract) ∷ cs , ds ] ∋
      ((Configuration Iᶜᶠ[ [] , [ ci , contract ] , [] ] ∋
          ⟨ contract ⟩ᶜ
      ∣∣ᵇ (0ᶠ , i , authDecorations (contract ‼ i))
      )
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & refl
      )
      —→[ empty ]
      Configuration Iᶜᶠ[ ads , (ci , [ contract ‼ i ]) ∷ cs , ds ] ∋
      (  ⟨ [ contract ‼ i ] ⟩ᶜ
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & refl
      )

-----------------------------------------------------------------------------------
-- Semantic rules for timed configurations.

infix 3 _≈ₜ_
_≈ₜ_ : TimedConfiguration cfi → TimedConfiguration cfi → Set
c ≈ₜ c′ = (time c ≡ time c′) × (cfg c ≈ cfg c′)

infix -1 _—→ₜ[_]_
data _—→ₜ[_]_ : TimedConfiguration cfi
              → Label
              → TimedConfiguration cfi′
              → Set where

  -- iv) Rules for handling time
  [Action] :

      Γ —→[ α ] Γ′
      -----------------------
    → Γ at t —→ₜ[ α ] Γ′ at t

  [Delay] :

      -------------------------------------
      Γ at t —→ₜ[ delay[ δ ] ] Γ at (t + δ)

  [Timeout] :
    ∀ {contract : Contracts ci} {i : Index contract}

      -- all time constraints are satisfied
    → All (_≤ t) (timeDecorations (contract ‼ i))

      -- resulting state if we pick branch `i`
    → Configuration Iᶜᶠ[ ads , (ci , [ contract ‼ i ]) ∷ cs , ds ] ∋
         ⟨ [ contract ‼ i ] ⟩ᶜ
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & refl
      —→[ α ]
      Γ′

      ---------------------------------------------------------

    → TimedConfiguration Iᶜᶠ[ ads , (ci , contract) ∷ cs , ds ] ∋
      (  ⟨ contract ⟩ᶜ
      ∣∣ Γ
      ∶- refl & refl & refl & refl & refl & refl
      ) at t
      —→ₜ[ α ]
      Γ′ at t

-----------------------------------------------------------------------------------
-- Reflexive transitive closure for —→.

infix  -1 _—↠[_]_
infix  -2 start_
infixr -1 _—→⟨_⟩_⊢_
infix  0 _∎∎

data _—↠[_]_ : Configuration cfi
             → Labels
             → Configuration cfi′
             → Set where

  _∎∎ : ∀ (M : Configuration cfi)

      ------------
    → M —↠[ [] ] M

  _—→⟨_⟩_⊢_ : ∀ (L    : Configuration cfi)
                {L′   : Configuration cfi}
                {M M′ : Configuration cfi′}
                {N    : Configuration cfi″}

    → L′ —→[ α ] M′
    → (L ≈ L′) × (M ≈ M′)
    → M —↠[ αs ]  N
      -------------------
    → L —↠[ α ∷ αs ] N

start_ : ∀ {M : Configuration cfi} {N : Configuration cfi′}

  → M —↠[ αs ] N
    ------------
  → M —↠[ αs ] N

start M—↠N = M—↠N

-----------------------------------------------------------------------------------
-- Reflexive transitive closure for —→ₜ.

infix  -1 _—↠ₜ[_]_
infix  -2 startₜ_
infixr -1 _—→ₜ⟨_⟩_⊢_
infix  0 _∎∎ₜ

data _—↠ₜ[_]_ : TimedConfiguration cfi
              → Labels
              → TimedConfiguration cfi′
              → Set where

  _∎∎ₜ : ∀ (M : TimedConfiguration cfi)

      -------------
    → M —↠ₜ[ [] ] M

  _—→ₜ⟨_⟩_⊢_ : ∀ (L    : TimedConfiguration cfi)
                 {L′   : TimedConfiguration cfi}
                 {M M′ : TimedConfiguration cfi′}
                 {N    : TimedConfiguration cfi″}

    → L′ —→ₜ[ α ] M′
    → (L ≈ₜ L′) × (M ≈ₜ M′)
    → M —↠ₜ[ αs ] N
      ---------------------
    → L —↠ₜ[ α ∷ αs ] N

startₜ_ : ∀ {M : TimedConfiguration cfi} {N : TimedConfiguration cfi′}

  → M —↠ₜ[ αs ] N
    -------------
  → M —↠ₜ[ αs ] N

startₜ M—↠N = M—↠N
