module BitML.Example.TimedCommitment where -- (see BitML paper, Section 2)

open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Setoid

open import BitML.BasicTypes hiding (a; x; y; t)
open import BitML.Predicate hiding (`; ∣_∣)

-------------------------------------------------------------------------

open import BitML.Example.Setup using (Participant; Honest; A; B)

open import BitML.Contracts.Types Participant Honest hiding (A; B)
open import BitML.Contracts.Helpers Participant Honest
open import BitML.Contracts.Validity Participant Honest
open import BitML.Semantics.Action Participant Honest
open import BitML.Semantics.Label Participant Honest
open import BitML.Semantics.Configurations.Types Participant Honest
open import BitML.Semantics.Configurations.Helpers Participant Honest
open import BitML.Semantics.InferenceRules Participant Honest
open import BitML.Semantics.DecidableInference Participant Honest

-------------------------------------------------------------------------

-- Do not postulate constants, in order for computation to go through
a = "CHANGE_ME" ; N = 9 ; t = 42 ; x = "x" ; y = "y" ; x₁ = "x₁" ; x₂ = "x₂" ; x₃ = "x₃"

tc : Advertisement
tc = ⟨ A :! 1 at x ∣∣ A :secret a ∣∣ B :! 0 at y ⟩
       reveal [ a ] ⇒ [ withdraw A ]
     ⊕ after t ⇒ withdraw B
     ∙

tc-steps :
  ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y
    —[ advertise⦅ tc ⦆
     ∷ auth-commit⦅ A , tc , [ a , just N ] ⦆
     ∷ auth-commit⦅ B , tc , [] ⦆
     ∷ auth-init⦅ A , tc , x ⦆
     ∷ auth-init⦅ B , tc , y ⦆
     ∷ init⦅ G tc , C tc ⦆
     ∷ auth-rev⦅ A , a ⦆
     ∷ put⦅ [] , [ a ] , x₁ ⦆
     ∷ withdraw⦅ A , 1 , x₂ ⦆
     ∷ []
     ]↠
  ⟨ A has 1 ⟩at x₃ ∣ A ∶ a ♯ N
tc-steps =
  begin
    ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y
  —→⟨ C-Advertise {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y} ⟩
    ` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y
  —→⟨ C-AuthCommit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y} {secrets = [ a , just N ]} ⟩
    ` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ]
  —→⟨ C-AuthCommit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ]} {secrets = []} ⟩
    ` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ]
  —→⟨ C-AuthInit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ]}
                 {v = 1} ⟩
    ` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ]
         ∣ B auth[ ♯▷ tc ] ∣ A auth[ x ▷ˢ tc ]
  —→⟨ C-AuthInit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                    ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ] ∣ A auth[ x ▷ˢ tc ]}
                 {v = 0} ⟩
    ` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ]
         ∣ B auth[ ♯▷ tc ] ∣ A auth[ x ▷ˢ tc ] ∣ B auth[ y ▷ˢ tc ]
  —→⟨ [C-Init] {Γ = ⟨ A ∶ a ♯ just 9 ⟩} {x = x₁} ⟩
    ⟨ C tc , 1 ⟩at x₁ ∣ ⟨ A ∶ a ♯ just 9 ⟩
  —→⟨ [C-AuthRev] {n = 9} {Γ = ⟨ C tc , 1 ⟩at x₁} ⟩
    ⟨ C tc , 1 ⟩at x₁ ∣ A ∶ a ♯ 9
  —→⟨ [C-Control] {c = C tc}
                  {Γ = A ∶ a ♯ 9}
                  {Γ′ = ⟨ [ withdraw A ] , 1 ⟩at x₂ ∣ (A ∶ a ♯ 9 ∣ ∅ᶜ)}
                  {i = 0F}
        (toWitness {Q = ⟨ [ reveal [ a ] ⇒ [ withdraw A ] ] , 1 ⟩at x₁ ∣ A ∶ a ♯ 9
                     ≈? ⟨ [ reveal [ a ] ⇒ [ withdraw A ] ] , 1 ⟩at x₁ ∣ (∅ᶜ ∣ A ∶ a ♯ 9 ∣ ∅ᶜ)} tt)
        ([C-PutRev] {ds = []} {ss = [ A , a , 9 ]} refl)
        refl
    ⟩
    ⟨ [ withdraw A ] , 1 ⟩at x₂ ∣ A ∶ a ♯ 9
  —→⟨ [C-Withdraw] {Γ = A ∶ a ♯ 9} {x = x₃} ⟩
    ⟨ A has 1 ⟩at x₃ ∣ A ∶ a ♯ N
  ∎

tc-steps′ :
  ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y
    —[ advertise⦅ tc ⦆
     ∷ auth-commit⦅ A , tc , [ a , just N ] ⦆
     ∷ auth-commit⦅ B , tc , [] ⦆
     ∷ auth-donate⦅ A , x ▷ᵈ B ⦆
     ∷ donate⦅ x ▷ᵈ B ⦆
     ∷ auth-init⦅ A , tc , x ⦆
     ∷ auth-init⦅ B , tc , y ⦆
     {-
     ∷ init⦅ G tc , C tc ⦆
     ∷ auth-rev⦅ A , a ⦆
     ∷ put⦅ [] , [ a ] , x₁ ⦆
     ∷ withdraw⦅ A , 1 , x₂ ⦆
     -}
     ∷ []
     ]↠
    ` tc ∣ ⟨ B has 1 ⟩at y ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ]
         ∣ B auth[ ♯▷ tc ] ∣ A auth[ x ▷ˢ tc ] ∣ B auth[ y ▷ˢ tc ]
tc-steps′ =
  begin
    ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y
  —→⟨ C-Advertise {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y} ⟩
    ` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y
  —→⟨ C-AuthCommit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y} {secrets = [ a , just N ]} ⟩
    ` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ]
  —→⟨ C-AuthCommit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ]} {secrets = []} ⟩
    ` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ]

  —→⟨ [DEP-AuthDonate] {A}{1}{x}{` tc ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ]}{B} ⟩
    ⟨ A has 1 ⟩at x ∣ A auth[ x ▷ᵈ B ] ∣ ` tc ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ]

  —→⟨ [DEP-Donate] {A}{1}{x}{B}{` tc ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ]}{y} ⟩
    ⟨ B has 1 ⟩at y ∣ ` tc ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ]

  —→⟨ C-AuthInit {Γ = ⟨ B has 1 ⟩at y ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ]}
                 {v = 1} ⟩
    ` tc ∣ ⟨ B has 1 ⟩at y ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ]
         ∣ B auth[ ♯▷ tc ] ∣ A auth[ x ▷ˢ tc ]
  —→⟨ C-AuthInit {Γ = ⟨ B has 1 ⟩at y ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                    ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ] ∣ A auth[ x ▷ˢ tc ]}
                 {v = 0} ⟩
    ` tc ∣ ⟨ B has 1 ⟩at y ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ]
         ∣ B auth[ ♯▷ tc ] ∣ A auth[ x ▷ˢ tc ] ∣ B auth[ y ▷ˢ tc ]
{-
  —→⟨ [C-Init] {Γ = ⟨ A ∶ a ♯ just 9 ⟩} {x = x₁} ⟩
    ⟨ C tc , 1 ⟩at x₁ ∣ ⟨ A ∶ a ♯ just 9 ⟩
  —→⟨ [C-AuthRev] {n = 9} {Γ = ⟨ C tc , 1 ⟩at x₁} ⟩
    ⟨ C tc , 1 ⟩at x₁ ∣ A ∶ a ♯ 9
  —→⟨ [C-Control] {c = C tc}
                  {Γ = A ∶ a ♯ 9}
                  {Γ′ = ⟨ [ withdraw A ] , 1 ⟩at x₂ ∣ (A ∶ a ♯ 9 ∣ ∅ᶜ)}
                  {i = 0F}
        (toWitness {Q = ⟨ [ reveal [ a ] ⇒ [ withdraw A ] ] , 1 ⟩at x₁ ∣ A ∶ a ♯ 9
                     ≈? ⟨ [ reveal [ a ] ⇒ [ withdraw A ] ] , 1 ⟩at x₁ ∣ (∅ᶜ ∣ A ∶ a ♯ 9 ∣ ∅ᶜ)} tt)
        ([C-PutRev] {ds = []} {ss = [ A , a , 9 ]} refl)
        refl
    ⟩
    ⟨ [ withdraw A ] , 1 ⟩at x₂ ∣ A ∶ a ♯ 9
  —→⟨ [C-Withdraw] {Γ = A ∶ a ♯ 9} {x = x₃} ⟩
    ⟨ A has 1 ⟩at x₃ ∣ A ∶ a ♯ N
-}
  ∎
