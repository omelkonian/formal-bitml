module Example where -- (see BitML paper, Section 2)

open import Level        using (0ℓ)
open import Function     using (_∋_; _∘_)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Bool    using (T; Bool; true; false; _∧_)
open import Data.Nat     using (ℕ; _≤_; _>_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (∃; ∃-syntax; Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂; isInj₁; isInj₂)
open import Data.Fin     using (Fin)
  renaming (zero to 0ᶠ; suc to sucᶠ)

open import Data.List            using (List; []; _∷_; [_]; length; map; zip)
open import Data.List.Any        using (Any; any; here; there)
open import Data.List.All        using (All)
  renaming ([] to All-[]; _∷_ to _All-∷_)
open import Data.List.Properties using (++-identityʳ)

open import Relation.Nullary using (yes; no)
open import Relation.Binary using (Decidable)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import Utilities.Lists

-------------------------------------------------------------------------

open import ExampleSetup using (Participant; _≟ₚ_; Honest; A; B)

open import Utilities.Lists

open import Types                                      Participant _≟ₚ_ Honest
open import BitML.Types                                Participant _≟ₚ_ Honest
open import BitML.DecidableEquality                    Participant _≟ₚ_ Honest
open import Semantics.Actions.Types                    Participant _≟ₚ_ Honest
open import Semantics.Configurations.Types             Participant _≟ₚ_ Honest
open import Semantics.Configurations.Helpers           Participant _≟ₚ_ Honest
open import Semantics.Configurations.DecidableEquality Participant _≟ₚ_ Honest
open import Semantics.InferenceRules                   Participant _≟ₚ_ Honest

-------------------------------------------------------------------------

1ᶠ : Fin 2
1ᶠ = sucᶠ 0ᶠ

infix 8 [_-_]
[_-_] : ∀ {ℓ} {A : Set ℓ} → A → A → List A
[ x - y ] = x ∷ y ∷ []

open import Relation.Nullary.Decidable using (True; False; toWitness; fromWitness)
open import Data.List using (_++_; filter)

a : Secret
a = "CHANGE_ME"

t : Time
t = 42

tc : Advertisement 1 [] [] (1 ∷ 0 ∷ [])
tc = ⟨ A :! 1
     ∣ A :secret a ∶- refl & refl
     ∣ B :! 0      ∶- refl & refl
     ⟩ (put [] &reveal [ a ] if `True ⇒ withdraw A
        ∶- sound-put {p = tt} & refl & (λ ()))
     ⊕ (after t ∶ withdraw B)
     ∙
     ∶- sound-≾
      & (λ{ (here px)                                 → here px
          ; (there (here px))                         → here px
          ; (there (there (here px)))                 → there (here px)
          ; (there (there (there (here px))))         → here px
          ; (there (there (there (there (here px))))) → there (here px)
          ; (there (there (there (there (there ())))))
          })
      & refl

tc∃ : ∃[ v ] ∃[ vsᶜ ] ∃[ vsᵛ ] ∃[ vsᵖ ] Advertisement v vsᶜ vsᵛ vsᵖ
tc∃ = 1 , [] , [] , (1 ∷ 0 ∷ []) , tc

tC : Contracts 1 []
tC = C tc

c∃ : ∃[ v ] ∃[ vsᶜ ] Contracts v vsᶜ
c∃ = 1 , [] , tC

c₁∃ : ∃[ v ] ∃[ vsᶜ ] Contracts v vsᶜ
c₁∃ = 1 , [] , [ tC ‼ 0ᶠ ]

c₂∃ : ∃[ v ] ∃[ vsᶜ ] Contracts v vsᶜ
c₂∃ = 1 , [] , [ withdraw A ]

⟨A♯⟩ : Configuration [] [] []
⟨A♯⟩ = ⟨ A ∶ a ♯ inj₁ 9 ⟩ {tt}

A♯ : Configuration [] [] []
A♯ = (A ∶ a ♯ 9) {tt}

A♯9 : Participant × Secret × (ℕ ⊎ ⊥)
A♯9 = A , a , inj₁ 9

Aauth♯ : Configuration′ ([] , [ tc∃ ]) ([] , []) ([] , [])
Aauth♯ = A auth[ ♯▷ tc ]∶- refl & refl & refl

Bauth♯ : Configuration′ ([] , [ tc∃ ]) ([] , []) ([] , [])
Bauth♯ = B auth[ ♯▷ tc ]∶- refl & refl & refl

Aauth▷ : Configuration′ ([] , [ tc∃ ]) ([] , []) ([] , [ A has 1 ])
Aauth▷ = A auth[ Action A [ tc∃ ] [] [ 1 ] [] ∋
                 (tc ▷ˢ 0ᶠ) {pr = fromWitness {0ℓ}
                              {P = [ 1 ] ≡ [ [ 1 ] ‼ 0ᶠ ] }
                              {Q = [ 1 ] SETₙ.≟ₗ [ [ 1 ] ‼ 0ᶠ ]}
                              refl}
               ]∶- refl & refl & refl

Bauth▷ : Configuration′ ([] , [ tc∃ ]) ([] , []) ([] , [ B has 0 ])
Bauth▷ = B auth[ Action B [ tc∃ ] [] [ 0 ] [] ∋
                 (tc ▷ˢ 1ᶠ) {pr = fromWitness {0ℓ}
                              {P = [ 0 ] ≡ [ (1 ∷ [ 0 ]) ‼ 1ᶠ ] }
                              {Q = [ 0 ] SETₙ.≟ₗ [ (1 ∷ [ 0 ]) ‼ 1ᶠ ]}
                              refl}
               ]∶- refl & refl & refl

c₀ : Configuration [] [] [ A has 1 - B has 0 ]
c₀ = ⟨ A , 1 ⟩ᵈ
  ∣∣ ⟨ B , 0 ⟩ᵈ
  ∶- refl & refl & refl & refl & refl & refl

--> [C-Advertise]
c₁ : Configuration [ tc∃ ] [] [ A has 1 - B has 0 ]
c₁ = ` tc
  ∣∣ c₀
  ∶- refl & refl & refl & refl & refl & refl

--> [C-AuthCommit]
c₂ : Configuration [ tc∃ ] [] [ A has 1 - B has 0 ]
c₂ = c₁
  ∣∣ ⟨A♯⟩
  ∶- refl & refl & refl & refl & refl & refl
  ∣∣ Aauth♯
  ∶- refl & refl & refl & refl & refl & refl

c₂′ : Configuration′ ([] , [ tc∃ ]) ([] , []) ([ A has 1 - B has 0 ] , [])
c₂′ = c₀
   ∣∣ ⟨A♯⟩
   ∶- refl & refl & refl & refl & refl & refl
   ∣∣ Aauth♯
   ∶- refl & refl & refl & refl & refl & refl

--> [C-AuthCommit]
c₃ : Configuration [ tc∃ ] [] [ A has 1 - B has 0 ]
c₃ = c₂
  ∣∣ Bauth♯
  ∶- refl & refl & refl & refl & refl & refl

c₃′ : Configuration′ ([] , tc∃ ∷ [ tc∃ ]) ([] , []) ([ A has 1 - B has 0 ] , [])
c₃′ = c₀
   ∣∣ ⟨A♯⟩
   ∶- refl & refl & refl & refl & refl & refl
   ∣∣ Aauth♯
   ∶- refl & refl & refl & refl & refl & refl
   ∣∣ Bauth♯
   ∶- refl & refl & refl & refl & refl & refl

--> [C-AuthInit]
c₄ : Configuration [ tc∃ ] [] [ B has 0 ]
c₄ = c₃
  ∣∣ Aauth▷
  ∶- refl & refl & refl & refl & refl & refl

c₄′ : Configuration′ ([] , tc∃ ∷ tc∃ ∷ [ tc∃ ]) ([] , []) ([ B has 0 ] , [])
c₄′ = c₀
   ∣∣ ⟨A♯⟩
   ∶- refl & refl & refl & refl & refl & refl
   ∣∣ Aauth♯
   ∶- refl & refl & refl & refl & refl & refl
   ∣∣ Bauth♯
   ∶- refl & refl & refl & refl & refl & refl
   ∣∣ Aauth▷
   ∶- refl & refl & refl & refl & refl & refl

--> [C-AuthInit]
c₅ : Configuration [ tc∃ ] [] []
c₅ = c₄
  ∣∣ Bauth▷
  ∶- refl & refl & refl & refl & refl & refl

c₅′ : Configuration′ ([] , tc∃ ∷ tc∃ ∷ tc∃ ∷ [ tc∃ ]) ([] , []) ([] , [])
c₅′ = c₀
   ∣∣ Aauth♯
   ∶- refl & refl & refl & refl & refl & refl
   ∣∣ Bauth♯
   ∶- refl & refl & refl & refl & refl & refl
   ∣∣ Aauth▷
   ∶- refl & refl & refl & refl & refl & refl
   ∣∣ Bauth▷
   ∶- refl & refl & refl & refl & refl & refl

--> [C-Init]
c₆ : Configuration [] [ c∃ ] []
c₆ = ⟨ tC , 1 ⟩ᶜ
  ∣∣ ⟨A♯⟩
  ∶- refl & refl & refl & refl & refl & refl

--> [C-AuthRev]
c₇ : Configuration [] [ c∃ ] []
c₇ = A♯
  ∣∣ ⟨ tC , 1 ⟩ᶜ
  ∶- refl & refl & refl & refl & refl & refl

--> [C-Control]
c₈ : Configuration [] [ c₁∃ ] []
c₈ = ⟨ [ tC ‼ 0ᶠ ] , 1 ⟩ᶜ
  ∣∣ A♯
  ∶- refl & refl & refl & refl & refl & refl

--> [C-PutRev]
c₉ : Configuration [] [ c₂∃ ] []
c₉ = ⟨ [ withdraw {1} A  ] , 1 ⟩ᶜ
  ∣∣ A♯
  ∶- refl & refl & refl & refl & refl & refl

--> [C-Withdraw]
c₁₀ : Configuration [] [] [ A has 1 ]
c₁₀ = ⟨ A , 1 ⟩ᵈ
   ∣∣ A♯
   ∶- refl & refl & refl & refl & refl & refl

tc-semantics :
  c₀ —↠ c₁₀
tc-semantics =
  start
    c₀
  —→⟨ [C-Advertise] {Γ = c₀}
      -- 1. at least one honest participant
      (A , (λ x → here refl))
      -- 2. all deposits in G actually exist
      (λ{ .((A has 1) ⟨ true ⟩) (here refl) → here refl
        ; .((B has 0) ⟨ true ⟩) (there (here refl)) → there (here refl)
        ; d (there (there ()))
        })
    ⟩ (SETᶜᶠ.sound-↭ , SETᶜᶠ.sound-↭) ⊢
    c₁
  —→⟨ [C-AuthCommit] {A = A} {bs = [ inj₁ tt ]} {Γ = c₀} {Δ = [ ⟨A♯⟩ ]}
      -- satisfy rads (none in this case)
      (λ ())
      -- secret commitments are proper
      ( -- 1. provide Δ
        refl
      , -- 2. honest participants have not committed to ⊥
        (λ{ (here refl) → refl ; (there ())}) All-∷ All-[]
      )
    ⟩ (SETᶜᶠ.sound-↭ , SETᶜᶠ.sound-↭) ⊢
    c₂
  —→⟨ [C-AuthCommit] {A = B} {bs = []} {Γ = c₂′} {Δ = []}
      -- satisfy rads
      (λ {x} z → z)
      -- secret commitments are proper
      ( -- 1. provide Δ
        refl
      , -- 2. honest participants have not committed to ⊥
        All-[]
      )
    ⟩ (SETᶜᶠ.sound-↭ , SETᶜᶠ.sound-↭) ⊢
    c₃
  —→⟨ [C-AuthInit] {A = A} {iᵖ = 0ᶠ} {dsˡ = []} {dsʳ = [ B has 0 ]} {Γ = c₃′} {p = refl}
      -- satisfy rads
      (λ { (here refl) → here refl
         ; (there (here refl)) → here refl
         ; (there (there ()))
         })
      -- all participants have committed their secrets
      ((here refl) All-∷ ((here refl) All-∷ ((there (here refl)) All-∷ All-[])))
    ⟩ (SETᶜᶠ.sound-↭ , SETᶜᶠ.sound-↭) ⊢
    c₄
  —→⟨ [C-AuthInit] {A = B} {iᵖ = 1ᶠ} {dsˡ = []} {dsʳ = []} {Γ = c₄′} {p = refl}
      -- satisfy rads (none in this case)
      (λ { (here refl) → here refl
         ; (there (here refl)) → here refl
         ; (there (there (here refl))) → here refl
         ; (there (there (there ())))
         })
      -- all participants have committed their secrets
      ((here refl) All-∷ ((here refl) All-∷ ((there (here refl)) All-∷ All-[])))
    ⟩ (SETᶜᶠ.sound-↭ , SETᶜᶠ.sound-↭) ⊢
    c₅
  —→⟨ [C-Init] {Γ = ⟨A♯⟩} {Δ = c₅′}
      -- satisfy rads (none in this case)
      (λ { (here refl) → here refl
         ; (there (here refl)) → here refl
         ; (there (there (here refl))) → here refl
         ; (there (there (there (here refl)))) → here refl
         ; (there (there (there (there ()))))
         })
      -- all participants have committed their secrets
      ((here refl) All-∷ ((here refl) All-∷ ((there (here refl)) All-∷ All-[])))
      -- all participants have spent the required (persistent) deposits for stipulation
      refl
    ⟩ (SETᶜᶠ.sound-↭ , SETᶜᶠ.sound-↭) ⊢
    c₆
  —→⟨ [C-AuthRev] {A = A} {s = a} {n = 9} {p = refl} {Γ = ⟨ tC , 1 ⟩ᶜ}
      -- valid length given
      refl
    ⟩ (SETᶜᶠ.sound-↭ , SETᶜᶠ.sound-↭) ⊢
    c₇
  —→⟨ [C-Control] {Γ = A♯} {i = 0ᶠ} ⟩ (SETᶜᶠ.sound-↭ , SETᶜᶠ.sound-↭) ⊢
    c₈
  —→⟨ [C-PutRev] {Γ = ∅ᶜ} {s = [ a ]} {ds′ = []} {ss = [ A , a , 9 , refl ]}
      -- `put` command
      (sound-put , refl , (λ ()))
      refl
      -- revealed secrets
      refl
      -- put deposits
      refl
      -- predicate evaluates to `true`
      refl
    ⟩ (SETᶜᶠ.sound-↭ , SETᶜᶠ.sound-↭) ⊢
    c₉
  —→⟨ [C-Withdraw] {Γ = A♯} refl ⟩ (SETᶜᶠ.sound-↭ , SETᶜᶠ.sound-↭) ⊢
    c₁₀
  ∎∎
