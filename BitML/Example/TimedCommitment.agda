module BitML.Example.TimedCommitment where -- (see BitML paper, Section 2)

open import Prelude.Init; open SetAsType
open import Prelude.DecEq
open import Prelude.Lists
open import Prelude.Lists.Dec
open import Prelude.Decidable
open import Prelude.Setoid
open import Prelude.Ord

open import BitML.BasicTypes hiding (a; x; y; t)
open import BitML.Predicate hiding (`; ∣_∣)

-------------------------------------------------------------------------

data Participant : Type where
  A B : Participant
unquoteDecl DecEqₚ = DERIVE DecEq [ quote Participant , DecEqₚ ]

Honest : List⁺ Participant
Honest = A ∷ []

open import BitML.Contracts ⋯ Participant , Honest ⋯ hiding (A; B)
open import BitML.Semantics ⋯ Participant , Honest ⋯

-------------------------------------------------------------------------

-- Do not postulate constants, in order for computation to go through
a = "CHANGE_ME" ; N = 9 ; t = 42 ; x = "x" ; y = "y" ; x₁ = "x₁" ; x₂ = "x₂" ; x₃ = "x₃"; y₁ = "y₁"

tc : Ad
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
     ∷ init⦅ G tc , tc .C ⦆
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
  —→⟨ C-AuthCommit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                      ∣ A auth[ ♯▷ tc ]} {secrets = []} ⟩
    ` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
         ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ]
  —→⟨ C-AuthInit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                    ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ]}
                 {v = 1} ⟩
    ` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ]
         ∣ B auth[ ♯▷ tc ] ∣ A auth[ x ▷ˢ tc ]
  —→⟨ C-AuthInit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                    ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ] ∣ A auth[ x ▷ˢ tc ]}
                 {v = 0} ⟩
    ` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ]
         ∣ B auth[ ♯▷ tc ] ∣ A auth[ x ▷ˢ tc ] ∣ B auth[ y ▷ˢ tc ]
  —→⟨ C-Init {x = x₁} {Γ = ⟨ A ∶ a ♯ just 9 ⟩} ⟩
    ⟨ tc .C , 1 ⟩at x₁ ∣ ⟨ A ∶ a ♯ just 9 ⟩
  —→⟨ [C-AuthRev] {n = 9} {Γ = ⟨ tc .C , 1 ⟩at x₁} ⟩
    ⟨ tc .C , 1 ⟩at x₁ ∣ A ∶ a ♯ 9
  —→⟨ C-Control {c = tc .C}
                {Γ = A ∶ a ♯ 9}
                {Γ′ = ⟨ [ withdraw A ] , 1 ⟩at x₂ ∣ (A ∶ a ♯ 9 ∣ ∅ᶜ)}
                {i = 0F}
    $ C-PutRev {ds = []} {ss = [ A , a , 9 ]} ⟩
    ⟨ [ withdraw A ] , 1 ⟩at x₂ ∣ A ∶ a ♯ 9
  —→⟨ C-Withdraw {x = x₃} {Γ = A ∶ a ♯ 9} ⟩
    ⟨ A has 1 ⟩at x₃ ∣ A ∶ a ♯ N
  ∎

tc-stepsₜ :
  (⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y) at 0
    —[ advertise⦅ tc ⦆
     ∷ auth-commit⦅ A , tc , [ a , just N ] ⦆
     ∷ auth-commit⦅ B , tc , [] ⦆
     ∷ auth-init⦅ A , tc , x ⦆
     ∷ auth-init⦅ B , tc , y ⦆
     ∷ init⦅ G tc , tc .C ⦆
     ∷ auth-rev⦅ A , a ⦆
     ∷ put⦅ [] , [ a ] , x₁ ⦆
     ∷ withdraw⦅ A , 1 , x₂ ⦆
     ∷ []
     ]↠ₜ
  (⟨ A has 1 ⟩at x₃ ∣ A ∶ a ♯ N) at 0
tc-stepsₜ =
  beginₜ
    (⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y) at 0
  —→ₜ⟨ Act {t = 0}
     $ C-Advertise {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y} ⟩
    (` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y) at 0
  —→ₜ⟨ Act {t = 0}
     $ C-AuthCommit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y} {secrets = [ a , just N ]} ⟩
    (` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ]) at 0
  —→ₜ⟨ Act {t = 0}
     $ C-AuthCommit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                       ∣ A auth[ ♯▷ tc ]} {secrets = []} ⟩
    (` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
          ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ]) at 0
  —→ₜ⟨ Act {t = 0}
     $ C-AuthInit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                     ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ]} {v = 1} ⟩
    (` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ]
          ∣ B auth[ ♯▷ tc ] ∣ A auth[ x ▷ˢ tc ]) at 0
  —→ₜ⟨ Act {t = 0}
     $ C-AuthInit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                       ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ] ∣ A auth[ x ▷ˢ tc ]}
                  {v = 0} ⟩
    (` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ]
          ∣ B auth[ ♯▷ tc ] ∣ A auth[ x ▷ˢ tc ] ∣ B auth[ y ▷ˢ tc ]) at 0
  —→ₜ⟨ Act {t = 0}
     $ C-Init {x = x₁} {Γ = ⟨ A ∶ a ♯ just 9 ⟩} ⟩
    (⟨ tc .C , 1 ⟩at x₁ ∣ ⟨ A ∶ a ♯ just 9 ⟩) at 0
  —→ₜ⟨ Act {t = 0}
     $ [C-AuthRev] {n = 9} {Γ = ⟨ tc .C , 1 ⟩at x₁} ⟩
    (⟨ tc .C , 1 ⟩at x₁ ∣ A ∶ a ♯ 9) at 0
  —→ₜ⟨ Timeout {c = tc .C} {t = 0} {v = 1} {i = 0F}
     $ C-PutRev {Γ′ = ∅ᶜ} {z = x₂} {ds = []} {ss = [ A , a , 9 ]} ⟩
    (⟨ [ withdraw A ] , 1 ⟩at x₂ ∣ A ∶ a ♯ 9) at 0
  —→ₜ⟨ Timeout {c = [ withdraw A ]} {t = 0} {v = 1} {i = 0F}
     $ C-Withdraw {x = x₃} {Γ = A ∶ a ♯ 9} ⟩
    (⟨ A has 1 ⟩at x₃ ∣ A ∶ a ♯ N) at 0
  ∎ₜ

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
     ∷ init⦅ tc .G , tc .C ⦆
     ∷ auth-rev⦅ A , a ⦆
     ∷ put⦅ [] , [ a ] , x₁ ⦆
     ∷ withdraw⦅ A , 1 , x₂ ⦆
     -}
     ∷ []
     ]↠
    ` tc ∣ ⟨ B has 1 ⟩at y₁ ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ]
         ∣ B auth[ ♯▷ tc ] ∣ A auth[ x ▷ˢ tc ] ∣ B auth[ y ▷ˢ tc ]
tc-steps′ =
  begin
    ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y
  —→⟨ C-Advertise {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y} ⟩
    ` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y
  —→⟨ C-AuthCommit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y} {secrets = [ a , just N ]} ⟩
    ` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ]
  —→⟨ C-AuthCommit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                      ∣ A auth[ ♯▷ tc ]} {secrets = []} ⟩
    ` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
         ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ]
  —→⟨ [DEP-AuthDonate] {A}{1}{x}{` tc ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                                      ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ]}{B} ⟩
    ⟨ A has 1 ⟩at x ∣ A auth[ x ▷ᵈ B ] ∣ ` tc ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                    ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ]
  —→⟨ DEP-Donate {y₁}{x}{` tc ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                              ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ]}{A}{1}{B} ⟩
    ⟨ B has 1 ⟩at y₁ ∣ ` tc ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                     ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ]
  —→⟨ C-AuthInit {Γ = ⟨ B has 1 ⟩at y₁ ∣ ⟨ B has 0 ⟩at y
                    ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ]} {v = 1} ⟩
    ` tc ∣ ⟨ B has 1 ⟩at y₁ ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
         ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ] ∣ A auth[ x ▷ˢ tc ]
  —→⟨ C-AuthInit {Γ = ⟨ B has 1 ⟩at y₁ ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                    ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ] ∣ A auth[ x ▷ˢ tc ]}
                 {v = 0} ⟩
    ` tc ∣ ⟨ B has 1 ⟩at y₁ ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
         ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ] ∣ A auth[ x ▷ˢ tc ] ∣ B auth[ y ▷ˢ tc ]
{-
  —→⟨ C-Init {x = x₁} {Γ = ⟨ A ∶ a ♯ just 9 ⟩} ⟩
    ⟨ tc .C , 1 ⟩at x₁ ∣ ⟨ A ∶ a ♯ just 9 ⟩
  —→⟨ [C-AuthRev] {n = 9} {Γ = ⟨ tc .C , 1 ⟩at x₁} ⟩
    ⟨ tc .C , 1 ⟩at x₁ ∣ A ∶ a ♯ 9
  —→⟨ [C-Control] {c = tc .C}
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

tc-stepsₜ′ :
  (⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y) at t
    —[ advertise⦅ tc ⦆
     ∷ auth-commit⦅ A , tc , [ a , just N ] ⦆
     ∷ auth-commit⦅ B , tc , [] ⦆
     ∷ auth-init⦅ A , tc , x ⦆
     ∷ auth-init⦅ B , tc , y ⦆
     ∷ init⦅ G tc , tc .C ⦆
     ∷ delay⦅ 1 ⦆
     ∷ withdraw⦅ B , 1 , x₁ ⦆
     ∷ []
     ]↠ₜ
  (⟨ B has 1 ⟩at x₂ ∣ ⟨ A ∶ a ♯ just N ⟩) at suc t
tc-stepsₜ′ =
  beginₜ
    (⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y) at t
  —→ₜ⟨ Act {t = t}
     $ C-Advertise {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y} ⟩
    (` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y) at t
  —→ₜ⟨ Act {t = t}
     $ C-AuthCommit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y} {secrets = [ a , just N ]} ⟩
    (` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just N ⟩ ∣ A auth[ ♯▷ tc ]) at t
  —→ₜ⟨ Act {t = t}
     $ C-AuthCommit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just N ⟩
                       ∣ A auth[ ♯▷ tc ]} {secrets = []} ⟩
    (` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just N ⟩
          ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ]) at t
  —→ₜ⟨ Act {t = t}
     $ C-AuthInit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just N ⟩
                     ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ]} {v = 1} ⟩
    (` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just N ⟩ ∣ A auth[ ♯▷ tc ]
          ∣ B auth[ ♯▷ tc ] ∣ A auth[ x ▷ˢ tc ]) at t
  —→ₜ⟨ Act {t = t}
     $ C-AuthInit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just N ⟩
                       ∣ A auth[ ♯▷ tc ] ∣ B auth[ ♯▷ tc ] ∣ A auth[ x ▷ˢ tc ]}
                  {v = 0} ⟩
    (` tc ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just N ⟩ ∣ A auth[ ♯▷ tc ]
          ∣ B auth[ ♯▷ tc ] ∣ A auth[ x ▷ˢ tc ] ∣ B auth[ y ▷ˢ tc ]) at t
  —→ₜ⟨ Act {t = t}
     $ C-Init {x = x₁} {Γ = ⟨ A ∶ a ♯ just N ⟩} ⟩
    (⟨ tc .C , 1 ⟩at x₁ ∣ ⟨ A ∶ a ♯ just N ⟩) at t
  —→ₜ⟨ Delay {Γ = ⟨ tc .C , 1 ⟩at x₁ ∣ ⟨ A ∶ a ♯ just N ⟩} {t = t} ⟩
    (⟨ tc .C , 1 ⟩at x₁ ∣ ⟨ A ∶ a ♯ just N ⟩) at suc t
  —→ₜ⟨ Timeout {c = tc .C} {t = suc t} {v = 1} {i = 1F}
     $ C-Withdraw {x = x₂} {y = x₁} {Γ = ⟨ A ∶ a ♯ just N ⟩} ⟩
    (⟨ B has 1 ⟩at x₂ ∣ ⟨ A ∶ a ♯ just N ⟩) at suc t
  ∎ₜ
