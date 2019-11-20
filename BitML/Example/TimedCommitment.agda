{-# OPTIONS --allow-unsolved-metas #-}
module BitML.Example.TimedCommitment where -- (see BitML paper, Section 2)

open import Level        using (0ℓ)
open import Function     using (_∋_; _∘_)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (⊤; tt)
open import Data.Maybe   using (Maybe; just; Is-just)
open import Data.Maybe.Relation.Unary.Any renaming (just to mjust)
open import Data.Bool    using (T; Bool; true; false; _∧_)
open import Data.Nat     using (ℕ; _≤_; _>_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (∃; ∃-syntax; Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
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

open import Prelude.Lists

-------------------------------------------------------------------------

open import BitML.Example.Setup using (Participant; _≟ₚ_; Honest; A; B)


open import BitML.BasicTypes                                 Participant _≟ₚ_ Honest
open import BitML.Contracts.Types                            Participant _≟ₚ_ Honest
open import BitML.Contracts.DecidableEquality                Participant _≟ₚ_ Honest
open import BitML.Semantics.Actions.Types                    Participant _≟ₚ_ Honest
open import BitML.Semantics.Labels.Types                     Participant _≟ₚ_ Honest
open import BitML.Semantics.Configurations.Types             Participant _≟ₚ_ Honest
open import BitML.Semantics.Configurations.Helpers           Participant _≟ₚ_ Honest
open import BitML.Semantics.Configurations.DecidableEquality Participant _≟ₚ_ Honest
open import BitML.Semantics.InferenceRules                   Participant _≟ₚ_ Honest hiding (A; B; t)

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

tc : Advertisement Iᶜ[ 1 , [] ] Iᵖ[ [] , 1 ∷ 0 ∷ [] ]
tc = ⟨ A :! 1
     ∣ A :secret a ∶- refl & refl
     ∣ B :! 0      ∶- refl & refl
     ⟩ (put [] &reveal [ a ] if `True ⇒ [ withdraw A ]
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

tc∃ : ∃Advertisement
tc∃ = Iᶜ[ 1 , [] ] , Iᵖ[ [] , 1 ∷ 0 ∷ [] ] , tc

tC : Contracts Iᶜ[ 1 , [] ]
tC = C tc

c∃ : ∃Contracts
c∃ = Iᶜ[ 1 , [] ] , tC

c₁∃ : ∃Contracts
c₁∃ = Iᶜ[ 1 , [] ] , [ tC ‼ 0ᶠ ]

c₂∃ : ∃Contracts
c₂∃ = Iᶜ[ 1 , [] ] , [ withdraw A ]

⟨A♯⟩ : Configuration Iᶜᶠ[ [] , [] , [] ]
⟨A♯⟩ = ⟨ A ∶ a ♯ just 9 ⟩

A♯ : Configuration Iᶜᶠ[ [] , [] , [] ]
A♯ = A ∶ a ♯ 9

A♯9 : Participant × Secret × Maybe ℕ
A♯9 = A , a , just 9

Aauth♯ : Configuration′ Iᶜᶠ[ [] & [ tc∃ ] , [] & [] , [] & [] ]
Aauth♯ = A auth[ ♯▷ tc ]∶- refl & refl & refl & refl & refl & refl

Bauth♯ : Configuration′ Iᶜᶠ[ [] & [ tc∃ ] , [] & [] , [] & [] ]
Bauth♯ = B auth[ ♯▷ tc ]∶- refl & refl & refl & refl & refl & refl

Aauth▷ : Configuration′ Iᶜᶠ[ [] & [ tc∃ ] , [] & [] , [] & [ A has 1 ] ]
Aauth▷ = A auth[ Action A Iᵃᶜ[ [ tc∃ ] , [] , [ 1 ] , [] ] ∋
                 (tc ▷ˢ 0ᶠ) {pr = fromWitness {0ℓ}
                            {P = [ 1 ] ≡ [ [ 1 ] ‼ 0ᶠ ] }
                            {Q = [ 1 ] SETₙ.≟ₗ [ [ 1 ] ‼ 0ᶠ ]}
                            refl}
               ]∶- refl & refl & refl & refl & refl & refl

Bauth▷ : Configuration′ Iᶜᶠ[ [] & [ tc∃ ] , [] & [] , [] & [ B has 0 ] ]
Bauth▷ = B auth[ Action B Iᵃᶜ[ [ tc∃ ] , [] , [ 0 ] , [] ] ∋
                 (tc ▷ˢ 1ᶠ) {pr = fromWitness {0ℓ}
                            {P = [ 0 ] ≡ [ (1 ∷ [ 0 ]) ‼ 1ᶠ ] }
                            {Q = [ 0 ] SETₙ.≟ₗ [ (1 ∷ [ 0 ]) ‼ 1ᶠ ]}
                            refl}
               ]∶- refl & refl & refl & refl & refl & refl

c₀ : Configuration Iᶜᶠ[ [] , [] , [ A has 1 - B has 0 ] ]
c₀ = ⟨ A , 1 ⟩ᵈ
  ∣∣ ⟨ B , 0 ⟩ᵈ
  ∶- refl & refl & refl & refl & refl & refl

--> [C-Advertise]
c₁ : Configuration Iᶜᶠ[ [ tc∃ ] , [] , [ A has 1 - B has 0 ] ]
c₁ = ` tc
  ∣∣ c₀
  ∶- refl & refl & refl & refl & refl & refl

--> [C-AuthCommit]
c₂ : Configuration Iᶜᶠ[ [ tc∃ ] , [] , [ A has 1 - B has 0 ] ]
c₂ = c₁
  ∣∣ ⟨A♯⟩
  ∶- refl & refl & refl & refl & refl & refl
  ∣∣ Aauth♯
  ∶- refl & refl & refl & refl & refl & refl

c₂′ : Configuration′ Iᶜᶠ[ [] & [ tc∃ ] , [] & [] , [ A has 1 - B has 0 ] & [] ]
c₂′ = c₀
   ∣∣ ⟨A♯⟩
   ∶- refl & refl & refl & refl & refl & refl
   ∣∣ Aauth♯
   ∶- refl & refl & refl & refl & refl & refl

--> [C-AuthCommit]
c₃ : Configuration Iᶜᶠ[ [ tc∃ ] , [] , [ A has 1 - B has 0 ] ]
c₃ = c₂
  ∣∣ Bauth♯
  ∶- refl & refl & refl & refl & refl & refl

c₃′ : Configuration′ Iᶜᶠ[ [] & (tc∃ ∷ [ tc∃ ]) , [] & [] , [ A has 1 - B has 0 ] & [] ]
c₃′ = c₀
   ∣∣ ⟨A♯⟩
   ∶- refl & refl & refl & refl & refl & refl
   ∣∣ Aauth♯
   ∶- refl & refl & refl & refl & refl & refl
   ∣∣ Bauth♯
   ∶- refl & refl & refl & refl & refl & refl

--> [C-AuthInit]
c₄ : Configuration Iᶜᶠ[ [ tc∃ ] , [] , [ B has 0 ] ]
c₄ = c₃
  ∣∣ Aauth▷
  ∶- refl & refl & refl & refl & refl & refl

c₄′ : Configuration′ Iᶜᶠ[ [] & (tc∃ ∷ tc∃ ∷ [ tc∃ ]) , [] & [] , [ B has 0 ] & [] ]
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
c₅ : Configuration Iᶜᶠ[ [ tc∃ ] , [] , [] ]
c₅ = c₄
  ∣∣ Bauth▷
  ∶- refl & refl & refl & refl & refl & refl

c₅′ : Configuration′ Iᶜᶠ[ [] & (tc∃ ∷ tc∃ ∷ tc∃ ∷ [ tc∃ ]) , [] & [] , [] & [] ]
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
c₆ : Configuration Iᶜᶠ[ [] , [ c∃ ] , [] ]
c₆ = ⟨ tC ⟩ᶜ
  ∣∣ ⟨A♯⟩
  ∶- refl & refl & refl & refl & refl & refl

--> [C-AuthRev]
c₇ : Configuration Iᶜᶠ[ [] , [ c∃ ] , [] ]
c₇ = A♯
  ∣∣ ⟨ tC ⟩ᶜ
  ∶- refl & refl & refl & refl & refl & refl

--> [C-Control]
c₈ : Configuration Iᶜᶠ[ [] , [ c₁∃ ] , [] ]
c₈ = ⟨ [ tC ‼ 0ᶠ ] ⟩ᶜ
  ∣∣ A♯
  ∶- refl & refl & refl & refl & refl & refl

--> [C-PutRev]
c₉ : Configuration Iᶜᶠ[ [] , [ c₂∃ ] , [] ]
c₉ = ⟨ [ withdraw A ] ⟩ᶜ
  ∣∣ A♯
  ∶- refl & refl & refl & refl & refl & refl

--> [C-Withdraw]
c₁₀ : Configuration Iᶜᶠ[ [] , [] , [ A has 1 ] ]
c₁₀ = ⟨ A , 1 ⟩ᵈ
   ∣∣ A♯
   ∶- refl & refl & refl & refl & refl & refl

tc-semantics :
  c₀ —↠[
    advertise[ tc∃ ]
  ∷ auth-commit[ A , tc∃ , [ a , just (9 , refl) ] ]
  ∷ auth-commit[ B , tc∃ , [] ]
  ∷ auth-init[ A , tc∃ , 0 ]
  ∷ auth-init[ B , tc∃ , 1 ]
  ∷ init[ tc∃ ]
  ∷ auth-rev[ A , a ]
  ∷ empty
  ∷ put[ [] , [ a ] ]
  ∷ withdraw[ A , 1 ]
  ∷ []
  ] c₁₀
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
    ⟩ ({!!} , {!!}) ⊢
    c₁
  —→⟨ [C-AuthCommit] {A = A} {secrets = [ a , just (9 , refl) ]} {Γ = c₀} {pr = refl}
      -- satisfy rads (none in this case)
      (λ ())
      -- honest participants have not committed to ⊥
      (λ _ → mjust tt All-∷ All-[])
    ⟩ ({!!} , {!!}) ⊢
    c₂
  —→⟨ [C-AuthCommit] {A = B} {secrets = []} {Γ = c₂′} {pr = refl}
      -- satisfy rads
      (λ {x} z → z)
      -- honest participants have not committed to ⊥
      (λ _ → All-[])
      --  All-[]
    ⟩ ({!!} , {!!}) ⊢
    c₃
  —→⟨ [C-AuthInit] {dsˡ = []} {dsʳ = [ B has 0 ]} {Γ = c₃′} {p = refl}
      -- satisfy rads
      (λ { (here refl) → here refl
         ; (there (here refl)) → here refl
         ; (there (there ()))
         })
      -- all participants have committed their secrets
      ((here refl) All-∷ ((here refl) All-∷ ((there (here refl)) All-∷ All-[])))
    ⟩ ({!!} , {!!}) ⊢
    c₄
  —→⟨ [C-AuthInit] {dsˡ = []} {dsʳ = []} {Γ = c₄′} {p = refl}
      -- satisfy rads (none in this case)
      (λ { (here refl) → here refl
         ; (there (here refl)) → here refl
         ; (there (there (here refl))) → here refl
         ; (there (there (there ())))
         })
      -- all participants have committed their secrets
      ((here refl) All-∷ ((here refl) All-∷ ((there (here refl)) All-∷ All-[])))
    ⟩ ({!!} , {!!}) ⊢
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
    ⟩ ({!!} , {!!}) ⊢
    c₆
  —→⟨ [C-AuthRev] {s = a} {n = 9} {Γ = ⟨ tC ⟩ᶜ}
      -- valid length given
      refl
    ⟩ ({!!} , {!!}) ⊢
    c₇
  —→⟨ [C-Control] {Γ = A♯} {i = 0ᶠ} ⟩ ({!!} , {!!}) ⊢
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
    ⟩ ({!!} , {!!}) ⊢
    c₉
  —→⟨ [C-Withdraw] {Γ = A♯} ⟩ ({!!} , {!!}) ⊢
    c₁₀
  ∎∎
