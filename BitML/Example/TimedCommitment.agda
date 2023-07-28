module BitML.Example.TimedCommitment where -- (see BitML paper, Section 2)

open import Prelude.Init; open SetAsType
open import Prelude.DecEq
open import Prelude.Lists
open import Prelude.Lists.Dec
open import Prelude.Decidable
open import Prelude.Setoid
open import Prelude.Ord
open import Prelude.Lists.NoNil using ()

open import BitML.BasicTypes hiding (a; x; y; t)
open import BitML.Predicate

open import BitML.Example.Setup hiding (C)

open import BitML.Contracts ⋯ Participant , Honest ⋯ hiding (A; B)
open import BitML.Semantics ⋯ Participant , Honest ⋯

-- Do not postulate constants, in order for computation to go through
a = "CHANGE_ME"; N = 9; t = 42
x = "x"; y = "y"; x₁ = "x₁"; x₂ = "x₂"; x₃ = "x₃"; y₁ = "y₁"

TC : Ad
TC = ⟨ A :! 1 at x ∣ A :secret a ∣ B :! 0 at y ⟩
       reveal a ． withdraw A
     ⊕ after t ∶ withdraw B

TC-steps :
  ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y
    —[ advertise⦅ TC ⦆
     ∷ auth-commit⦅ A , TC , [ a , just N ] ⦆
     ∷ auth-commit⦅ B , TC , [] ⦆
     ∷ auth-init⦅ A , TC , x ⦆
     ∷ auth-init⦅ B , TC , y ⦆
     ∷ init⦅ TC .G , TC .C ⦆
     ∷ auth-rev⦅ A , a ⦆
     ∷ put⦅ [] , [ a ] , x₁ ⦆
     ∷ withdraw⦅ A , 1 , x₂ ⦆
     ∷ []
     ]↠
  ⟨ A has 1 ⟩at x₃ ∣ A ∶ a ♯ N
TC-steps =
  begin
    ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y
  —→⟨ C-Advertise {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y} ⟩
    ` TC ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y
  —→⟨ C-AuthCommit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y} {secrets = [ a , just N ]} ⟩
    ` TC ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ TC ]
  —→⟨ C-AuthCommit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                      ∣ A auth[ ♯▷ TC ]} {secrets = []} ⟩
    ` TC ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
         ∣ A auth[ ♯▷ TC ] ∣ B auth[ ♯▷ TC ]
  —→⟨ C-AuthInit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                    ∣ A auth[ ♯▷ TC ] ∣ B auth[ ♯▷ TC ]}
                 {v = 1} ⟩
    ` TC ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ TC ]
         ∣ B auth[ ♯▷ TC ] ∣ A auth[ x ▷ˢ TC ]
  —→⟨ C-AuthInit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                    ∣ A auth[ ♯▷ TC ] ∣ B auth[ ♯▷ TC ] ∣ A auth[ x ▷ˢ TC ]}
                 {v = 0} ⟩
    ` TC ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ TC ]
         ∣ B auth[ ♯▷ TC ] ∣ A auth[ x ▷ˢ TC ] ∣ B auth[ y ▷ˢ TC ]
  —→⟨ C-Init {x = x₁} {Γ = ⟨ A ∶ a ♯ just 9 ⟩} ⟩
    ⟨ TC .C , 1 ⟩at x₁ ∣ ⟨ A ∶ a ♯ just 9 ⟩
  —→⟨ [C-AuthRev] {n = 9} {Γ = ⟨ TC .C , 1 ⟩at x₁} ⟩
    ⟨ TC .C , 1 ⟩at x₁ ∣ A ∶ a ♯ 9
  —→⟨ C-Control {c = TC .C}
                {Γ = A ∶ a ♯ 9}
                {Γ′ = ⟨ [ withdraw A ] , 1 ⟩at x₂ ∣ (A ∶ a ♯ 9 ∣ ∅ᶜ)}
                {i = 0F}
    $ C-PutRev {ds = []} {ss = [ A , a , 9 ]} ⟩
    ⟨ [ withdraw A ] , 1 ⟩at x₂ ∣ A ∶ a ♯ 9
  —→⟨ C-Withdraw {x = x₃} {Γ = A ∶ a ♯ 9} ⟩
    ⟨ A has 1 ⟩at x₃ ∣ A ∶ a ♯ N
  ∎

TC-stepsₜ :
  (⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y) at 0
    —[ advertise⦅ TC ⦆
     ∷ auth-commit⦅ A , TC , [ a , just N ] ⦆
     ∷ auth-commit⦅ B , TC , [] ⦆
     ∷ auth-init⦅ A , TC , x ⦆
     ∷ auth-init⦅ B , TC , y ⦆
     ∷ init⦅ TC .G , TC .C ⦆
     ∷ auth-rev⦅ A , a ⦆
     ∷ put⦅ [] , [ a ] , x₁ ⦆
     ∷ withdraw⦅ A , 1 , x₂ ⦆
     ∷ []
     ]↠ₜ
  (⟨ A has 1 ⟩at x₃ ∣ A ∶ a ♯ N) at 0
TC-stepsₜ =
  beginₜ
    (⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y) at 0
  —→ₜ⟨ Act {t = 0}
     $ C-Advertise {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y} ⟩
    (` TC ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y) at 0
  —→ₜ⟨ Act {t = 0}
     $ C-AuthCommit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y} {secrets = [ a , just N ]} ⟩
    (` TC ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ TC ]) at 0
  —→ₜ⟨ Act {t = 0}
     $ C-AuthCommit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                       ∣ A auth[ ♯▷ TC ]} {secrets = []} ⟩
    (` TC ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
          ∣ A auth[ ♯▷ TC ] ∣ B auth[ ♯▷ TC ]) at 0
  —→ₜ⟨ Act {t = 0}
     $ C-AuthInit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                     ∣ A auth[ ♯▷ TC ] ∣ B auth[ ♯▷ TC ]} {v = 1} ⟩
    (` TC ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ TC ]
          ∣ B auth[ ♯▷ TC ] ∣ A auth[ x ▷ˢ TC ]) at 0
  —→ₜ⟨ Act {t = 0}
     $ C-AuthInit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                       ∣ A auth[ ♯▷ TC ] ∣ B auth[ ♯▷ TC ] ∣ A auth[ x ▷ˢ TC ]}
                  {v = 0} ⟩
    (` TC ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ TC ]
          ∣ B auth[ ♯▷ TC ] ∣ A auth[ x ▷ˢ TC ] ∣ B auth[ y ▷ˢ TC ]) at 0
  —→ₜ⟨ Act {t = 0}
     $ C-Init {x = x₁} {Γ = ⟨ A ∶ a ♯ just 9 ⟩} ⟩
    (⟨ TC .C , 1 ⟩at x₁ ∣ ⟨ A ∶ a ♯ just 9 ⟩) at 0
  —→ₜ⟨ Act {t = 0}
     $ [C-AuthRev] {n = 9} {Γ = ⟨ TC .C , 1 ⟩at x₁} ⟩
    (⟨ TC .C , 1 ⟩at x₁ ∣ A ∶ a ♯ 9) at 0
  —→ₜ⟨ Timeout {c = TC .C} {t = 0} {v = 1} {i = 0F}
     $ C-PutRev {Γ′ = ∅ᶜ} {z = x₂} {ds = []} {ss = [ A , a , 9 ]} ⟩
    (⟨ [ withdraw A ] , 1 ⟩at x₂ ∣ A ∶ a ♯ 9) at 0
  —→ₜ⟨ Timeout {c = [ withdraw A ]} {t = 0} {v = 1} {i = 0F}
     $ C-Withdraw {x = x₃} {Γ = A ∶ a ♯ 9} ⟩
    (⟨ A has 1 ⟩at x₃ ∣ A ∶ a ♯ N) at 0
  ∎ₜ

TC-steps′ :
  ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y
    —[ advertise⦅ TC ⦆
     ∷ auth-commit⦅ A , TC , [ a , just N ] ⦆
     ∷ auth-commit⦅ B , TC , [] ⦆
     ∷ auth-donate⦅ A , x ▷ᵈ B ⦆
     ∷ donate⦅ x ▷ᵈ B ⦆
     ∷ auth-init⦅ A , TC , x ⦆
     ∷ auth-init⦅ B , TC , y ⦆
     {-
     ∷ init⦅ TC .G , TC .C ⦆
     ∷ auth-rev⦅ A , a ⦆
     ∷ put⦅ [] , [ a ] , x₁ ⦆
     ∷ withdraw⦅ A , 1 , x₂ ⦆
     -}
     ∷ []
     ]↠
    ` TC ∣ ⟨ B has 1 ⟩at y₁ ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ TC ]
         ∣ B auth[ ♯▷ TC ] ∣ A auth[ x ▷ˢ TC ] ∣ B auth[ y ▷ˢ TC ]
TC-steps′ =
  begin
    ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y
  —→⟨ C-Advertise {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y} ⟩
    ` TC ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y
  —→⟨ C-AuthCommit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y} {secrets = [ a , just N ]} ⟩
    ` TC ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ TC ]
  —→⟨ C-AuthCommit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                      ∣ A auth[ ♯▷ TC ]} {secrets = []} ⟩
    ` TC ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
         ∣ A auth[ ♯▷ TC ] ∣ B auth[ ♯▷ TC ]
  —→⟨ [DEP-AuthDonate] {A}{1}{x}{` TC ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                                      ∣ A auth[ ♯▷ TC ] ∣ B auth[ ♯▷ TC ]}{B} ⟩
    ⟨ A has 1 ⟩at x ∣ A auth[ x ▷ᵈ B ] ∣ ` TC ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                    ∣ A auth[ ♯▷ TC ] ∣ B auth[ ♯▷ TC ]
  —→⟨ DEP-Donate {y₁}{x}{` TC ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                              ∣ A auth[ ♯▷ TC ] ∣ B auth[ ♯▷ TC ]}{A}{1}{B} ⟩
    ⟨ B has 1 ⟩at y₁ ∣ ` TC ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                     ∣ A auth[ ♯▷ TC ] ∣ B auth[ ♯▷ TC ]
  —→⟨ C-AuthInit {Γ = ⟨ B has 1 ⟩at y₁ ∣ ⟨ B has 0 ⟩at y
                    ∣ ⟨ A ∶ a ♯ just 9 ⟩ ∣ A auth[ ♯▷ TC ] ∣ B auth[ ♯▷ TC ]} {v = 1} ⟩
    ` TC ∣ ⟨ B has 1 ⟩at y₁ ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
         ∣ A auth[ ♯▷ TC ] ∣ B auth[ ♯▷ TC ] ∣ A auth[ x ▷ˢ TC ]
  —→⟨ C-AuthInit {Γ = ⟨ B has 1 ⟩at y₁ ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
                    ∣ A auth[ ♯▷ TC ] ∣ B auth[ ♯▷ TC ] ∣ A auth[ x ▷ˢ TC ]}
                 {v = 0} ⟩
    ` TC ∣ ⟨ B has 1 ⟩at y₁ ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just 9 ⟩
         ∣ A auth[ ♯▷ TC ] ∣ B auth[ ♯▷ TC ] ∣ A auth[ x ▷ˢ TC ] ∣ B auth[ y ▷ˢ TC ]
{-
  —→⟨ C-Init {x = x₁} {Γ = ⟨ A ∶ a ♯ just 9 ⟩} ⟩
    ⟨ TC .C , 1 ⟩at x₁ ∣ ⟨ A ∶ a ♯ just 9 ⟩
  —→⟨ [C-AuthRev] {n = 9} {Γ = ⟨ TC .C , 1 ⟩at x₁} ⟩
    ⟨ TC .C , 1 ⟩at x₁ ∣ A ∶ a ♯ 9
  —→⟨ [C-Control] {c = TC .C}
                  {Γ = A ∶ a ♯ 9}
                  {Γ′ = ⟨ [ withdraw A ] , 1 ⟩at x₂ ∣ (A ∶ a ♯ 9 ∣ ∅ᶜ)}
                  {i = 0F}
        (toWitness {Q = ⟨ [ reveal a ． withdraw A ] , 1 ⟩at x₁ ∣ A ∶ a ♯ 9
                     ≈? ⟨ [ reveal a ． withdraw A ] , 1 ⟩at x₁ ∣ (∅ᶜ ∣ A ∶ a ♯ 9 ∣ ∅ᶜ)} tt)
        ([C-PutRev] {ds = []} {ss = [ A , a , 9 ]} refl)
        refl
    ⟩
    ⟨ [ withdraw A ] , 1 ⟩at x₂ ∣ A ∶ a ♯ 9
  —→⟨ [C-Withdraw] {Γ = A ∶ a ♯ 9} {x = x₃} ⟩
    ⟨ A has 1 ⟩at x₃ ∣ A ∶ a ♯ N
-}
  ∎

TC-stepsₜ′ :
  (⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y) at t
    —[ advertise⦅ TC ⦆
     ∷ auth-commit⦅ A , TC , [ a , just N ] ⦆
     ∷ auth-commit⦅ B , TC , [] ⦆
     ∷ auth-init⦅ A , TC , x ⦆
     ∷ auth-init⦅ B , TC , y ⦆
     ∷ init⦅ TC .G , TC .C ⦆
     ∷ delay⦅ 1 ⦆
     ∷ withdraw⦅ B , 1 , x₁ ⦆
     ∷ []
     ]↠ₜ
  (⟨ B has 1 ⟩at x₂ ∣ ⟨ A ∶ a ♯ just N ⟩) at suc t
TC-stepsₜ′ =
  beginₜ
    (⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y) at t
  —→ₜ⟨ Act {t = t}
     $ C-Advertise {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y} ⟩
    (` TC ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y) at t
  —→ₜ⟨ Act {t = t}
     $ C-AuthCommit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y} {secrets = [ a , just N ]} ⟩
    (` TC ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just N ⟩ ∣ A auth[ ♯▷ TC ]) at t
  —→ₜ⟨ Act {t = t}
     $ C-AuthCommit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just N ⟩
                       ∣ A auth[ ♯▷ TC ]} {secrets = []} ⟩
    (` TC ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just N ⟩
          ∣ A auth[ ♯▷ TC ] ∣ B auth[ ♯▷ TC ]) at t
  —→ₜ⟨ Act {t = t}
     $ C-AuthInit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just N ⟩
                     ∣ A auth[ ♯▷ TC ] ∣ B auth[ ♯▷ TC ]} {v = 1} ⟩
    (` TC ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just N ⟩ ∣ A auth[ ♯▷ TC ]
          ∣ B auth[ ♯▷ TC ] ∣ A auth[ x ▷ˢ TC ]) at t
  —→ₜ⟨ Act {t = t}
     $ C-AuthInit {Γ = ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just N ⟩
                       ∣ A auth[ ♯▷ TC ] ∣ B auth[ ♯▷ TC ] ∣ A auth[ x ▷ˢ TC ]}
                  {v = 0} ⟩
    (` TC ∣ ⟨ A has 1 ⟩at x ∣ ⟨ B has 0 ⟩at y ∣ ⟨ A ∶ a ♯ just N ⟩ ∣ A auth[ ♯▷ TC ]
          ∣ B auth[ ♯▷ TC ] ∣ A auth[ x ▷ˢ TC ] ∣ B auth[ y ▷ˢ TC ]) at t
  —→ₜ⟨ Act {t = t}
     $ C-Init {x = x₁} {Γ = ⟨ A ∶ a ♯ just N ⟩} ⟩
    (⟨ TC .C , 1 ⟩at x₁ ∣ ⟨ A ∶ a ♯ just N ⟩) at t
  —→ₜ⟨ Delay {Γ = ⟨ TC .C , 1 ⟩at x₁ ∣ ⟨ A ∶ a ♯ just N ⟩} {t = t} ⟩
    (⟨ TC .C , 1 ⟩at x₁ ∣ ⟨ A ∶ a ♯ just N ⟩) at suc t
  —→ₜ⟨ Timeout {c = TC .C} {t = suc t} {v = 1} {i = 1F}
     $ C-Withdraw {x = x₂} {y = x₁} {Γ = ⟨ A ∶ a ♯ just N ⟩} ⟩
    (⟨ B has 1 ⟩at x₂ ∣ ⟨ A ∶ a ♯ just N ⟩) at suc t
  ∎ₜ
