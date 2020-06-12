module BitML.Example.TimedCommitment where -- (see BitML paper, Section 2)

open import Level             using (0ℓ)
open import Function          using (_∋_; _∘_)
open import Data.Empty        using (⊥; ⊥-elim)
open import Data.Unit         using (⊤; tt)
open import Data.Maybe        using (Maybe; just; Is-just)
open import Data.Bool         using (T; Bool; true; false; _∧_)
open import Data.Nat          using (ℕ; _>_; _+_)
open import Data.Product      using (Σ-syntax; _×_; _,_)
open import Data.Fin.Patterns using (0F)

open import Data.Maybe.Relation.Unary.Any renaming (just to mjust)

open import Data.List using (List; []; _∷_; [_]; length; map; zip)
open import Data.List.Relation.Unary.Any using (Any; any; here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)

open import Relation.Nullary.Decidable            using (fromWitness; toWitness)
open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Prelude.Lists

open import BitML.BasicTypes hiding (a; x; y; t)
open import BitML.Predicate.Base hiding (`; ∣_∣)

-------------------------------------------------------------------------

open import BitML.Example.Setup using (Participant; _≟ₚ_; Honest; A; B)

open import BitML.Contracts.Types                  Participant _≟ₚ_ Honest hiding (A; B)
open import BitML.Contracts.Helpers                Participant _≟ₚ_ Honest
open import BitML.Contracts.Validity               Participant _≟ₚ_ Honest
open import BitML.Semantics.Actions.Types          Participant _≟ₚ_ Honest
open import BitML.Semantics.Labels.Types           Participant _≟ₚ_ Honest
open import BitML.Semantics.Configurations.Types   Participant _≟ₚ_ Honest
open import BitML.Semantics.Configurations.Helpers Participant _≟ₚ_ Honest
open import BitML.Semantics.Configurations.DecidableEquality Participant _≟ₚ_ Honest
open import BitML.Semantics.InferenceRules         Participant _≟ₚ_ Honest
open import BitML.Semantics.Reasoning              Participant _≟ₚ_ Honest
open import BitML.Semantics.DecidableInference     Participant _≟ₚ_ Honest

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
    —↠[ advertise[ tc ]
      ∷ auth-commit[ A , tc , [ a , just N ] ]
      ∷ auth-commit[ B , tc , [] ]
      ∷ auth-init[ A , tc , x ]
      ∷ auth-init[ B , tc , y ]
      ∷ init[ G tc , C tc ]
      ∷ auth-rev[ A , a ]
      ∷ put[ [] , [ a ] , x₁ ]
      ∷ withdraw[ A , 1 , x₂ ]
      ∷ []
      ]
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
                  {Γ′ = ⟨ [ withdraw A ] , 1 ⟩at x₂ ∣ A ∶ a ♯ 9 ∣ ∅ᶜ}
                  {i = 0F}
        (toWitness {Q = ⟨ [ reveal [ a ] ⇒ [ withdraw A ] ] , 1 ⟩at x₁ ∣ A ∶ a ♯ 9
                     ≈? ⟨ [ reveal [ a ] ⇒ [ withdraw A ] ] , 1 ⟩at x₁ ∣ ∅ᶜ ∣ A ∶ a ♯ 9 ∣ ∅ᶜ} tt)
        ([C-PutRev] {ds = []} {ss = [ A , a , 9 ]} refl)
        refl
    ⟩
    ⟨ [ withdraw A ] , 1 ⟩at x₂ ∣ A ∶ a ♯ 9
  —→⟨ [C-Withdraw] {Γ = A ∶ a ♯ 9} {x = x₃} ⟩
    ⟨ A has 1 ⟩at x₃ ∣ A ∶ a ♯ N
  ∎
