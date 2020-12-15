{-# OPTIONS --allow-unsolved-metas #-}
open import Induction using (Recursor)
open import Data.List.Membership.Propositional.Properties

open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Semigroup
open import Prelude.Applicative
open import Prelude.Nary
open import Prelude.Collections

module BitML.Contracts.Induction
  (Participant : Set)
  {{_ : DecEq Participant}}
  (Honest : List⁺ Participant)
  where

open import BitML.BasicTypes
open import BitML.Predicate
open import BitML.Contracts.Types Participant Honest hiding (C)
open import BitML.Contracts.Helpers Participant Honest


data ℂ : Set where
  C   : Contract → ℂ
  CS  : Contracts → ℂ
  VCS : VContracts → ℂ

instance
  HP-ℂ : ∀ {X : Set} {{_ : Contract has X}} → ℂ has X
  HP-ℂ .collect (C d)     = collect d
  HP-ℂ .collect (CS ds)   = collect ds
  HP-ℂ .collect (VCS vcs) = collect vcs

participants-helperᶜˢ : participants (CS ds) ⊆ participants (put xs &reveal as if p ⇒ ds)
participants-helperᶜˢ {ds = d ∷ ds} d∈
  with ∈-++⁻ (participants d) d∈
... | inj₁ d∈ˡ = ∈-++⁺ˡ d∈ˡ
... | inj₂ d∈ʳ = ∈-++⁺ʳ (participants d) (participants-helperᶜˢ {ds = ds} d∈ʳ)

participants-helperᵛᶜˢ : participants (VCS vcs) ⊆ participants (split vcs)
participants-helperᵛᶜˢ {vcs = (_ , ds) ∷ vcs} d∈
  with ∈-++⁻ (participants ds) d∈
... | inj₁ d∈ˡ = {!!} -- ∈-++⁺ˡ d∈ˡ
... | inj₂ d∈ʳ = {!!} -- there (∈-++⁺ʳ (participants (CS ds))) (participants-helperᵛᶜˢ {vcs = vcs} d∈ʳ)

subterms subterms⁺ : ℂ → List Contract

subterms c@(C _)   = drop 1 $ subterms⁺ c
subterms c@(CS _)  = subterms⁺ c
subterms c@(VCS _) = subterms⁺ c

subterms⁺ (C c) with c
... | _ ⇒ d                      = subterms⁺ (C d)
... | after _ ⇒ d                = subterms⁺ (C d)
... | split vcs                  = c ∷ subterms⁺ (VCS vcs)
... | put _ &reveal _ if _ ⇒ cs  = c ∷ subterms⁺ (CS cs)
... | withdraw _                 = c ∷ []
subterms⁺ (CS [])                = []
subterms⁺ (CS (c ∷ cs))          = subterms⁺ (C c) ++ subterms⁺ (CS cs)
subterms⁺ (VCS [])               = []
subterms⁺ (VCS ((_ , cs) ∷ vcs)) = subterms⁺ (CS cs) ++ subterms⁺ (VCS vcs)

subterms′ : ℂ → List Contract
subterms′ (C c) with c
... | _ ⇒ d                      = subterms′ (C d)
... | after _ ⇒ d                = subterms′ (C d)
... | split vcs                  = subterms′ (VCS vcs)
... | put _ &reveal _ if _ ⇒ cs  = subterms′ (CS cs)
... | withdraw _                 = []
subterms′ (CS [])                = []
subterms′ (CS (c ∷ cs))          = c ∷ subterms′ (C c) ++ subterms′ (CS cs)
subterms′ (VCS [])               = []
subterms′ (VCS ((_ , cs) ∷ vcs)) = subterms′ (CS cs) ++ subterms′ (VCS vcs)

subterms′-names⊆ : d ∈ subterms′ (CS ds) → names d ⊆ names ds
subterms′-names⊆ d∈ = {!!}

subterms′-putComponents⊆ : d ∈ subterms′ (CS ds) → putComponents d ⊆ putComponents ds
subterms′-putComponents⊆ d∈ = {!!}

subterms⊆ᶜˢ : ds ⊆ subterms′ (CS ds)
subterms⊆ᶜˢ {ds = d ∷ ds} (here refl) = here refl
subterms⊆ᶜˢ {ds = d ∷ ds} (there d∈)  = there $ ∈-++⁺ʳ (subterms′ $ C d) (subterms⊆ᶜˢ d∈)

subterms⊆ᵛᶜˢ : (v , ds) ∈ vcs → ds ⊆ subterms′ (VCS vcs)
subterms⊆ᵛᶜˢ {vcs = (_ , ds) ∷ vcs} (here refl) = ∈-++⁺ˡ ∘ subterms⊆ᶜˢ
subterms⊆ᵛᶜˢ {vcs = (_ , ds) ∷ vcs} (there p)   = ∈-++⁺ʳ (subterms′ (CS ds)) ∘ subterms⊆ᵛᶜˢ p

data _≺_ : Rel ℂ 0ℓ where

  ≺-∈  : d ∈ ds → C d ≺ CS ds
  ≺-∈ᵛ : ds ∈ map proj₂ vcs → CS ds ≺ VCS vcs
  instance
    ≺-put   : CS ds ≺ C (put xs &reveal as if p ⇒ ds)
    ≺-auth  : C d ≺ C (A ⇒ d)
    ≺-after : C d ≺ C (after t ⇒ d)
    ≺-split : VCS vcs ≺ C (split vcs)

≺-wf : WellFounded _≺_
≺-wf = acc ∘ _≻_
  where
    _≻_ : ∀ c c′ → c′ ≺ c → Acc _≺_ c′
    (.(CS (_ ∷ _))  ≻ .(C _))  (≺-∈                (here refl)) = acc (_ ≻_)
    (.(CS (_ ∷ _))  ≻ .(C _))  (≺-∈                (there p))   = (_ ≻ _) (≺-∈ p)
    (.(VCS (_ ∷ _)) ≻ .(CS _)) (≺-∈ᵛ {vcs = _ ∷ _} (here refl)) = acc (_ ≻_)
    (.(VCS (_ ∷ _)) ≻ .(CS _)) (≺-∈ᵛ {vcs = _ ∷ _} (there p))   = (_ ≻ _) (≺-∈ᵛ p)

    (.(C (put _ &reveal _ if _ ⇒ _)) ≻ .(CS _))  ≺-put   = acc (_ ≻_)
    (.(C (_ ⇒ _))                    ≻ .(C _))   ≺-auth  = acc (_ ≻_)
    (.(C (after _ ⇒ _))              ≻ .(C _))   ≺-after = acc (_ ≻_)
    (.(C (split _))                  ≻ .(VCS _)) ≺-split = acc (_ ≻_)

≺-rec : Recursor (WF.WfRec _≺_)
≺-rec = WF.All.wfRec ≺-wf 0ℓ

record Toℂ (A : Set) : Set where
  field
    toℂ : A → ℂ

  -- subterms′ : A → List Contract
  -- subterms′ = subterms ∘ toℂ
open Toℂ {{...}} public

instance
  Toℂᶜ : Toℂ Contract
  Toℂᶜ .toℂ = C

  Toℂᶜˢ : Toℂ Contracts
  Toℂᶜˢ .toℂ = CS

  Toℂᵛᶜˢ : Toℂ VContracts
  Toℂᵛᶜˢ .toℂ = VCS

_≺ℂ_ : ∀ {A B : Set} {{_ : Toℂ A}} {{_ : Toℂ B}} → A → B → Set
x ≺ℂ y = toℂ x ≺ toℂ y

-- Helpers.
↦-∈ : ∀ {R : Set}
  → (∀ {d} → d ∈ ds → subterms⁺ (C d) ↦ R)
  → subterms⁺ (CS ds) ↦ R
↦-∈ {ds = c ∷ cs} f x∈
  with ∈-++⁻ (subterms⁺ (C c)) x∈
... | inj₁ x∈ˡ = f (here refl) x∈ˡ
... | inj₂ x∈ʳ = ↦-∈ (f ∘ there) x∈ʳ

↦-∈ᵛ : ∀ {R : Set}
  → (∀ {cs} → cs ∈ map proj₂ vcs → subterms⁺ (CS cs) ↦ R)
  → subterms⁺ (VCS vcs) ↦ R
↦-∈ᵛ {vcs = (_ , cs) ∷ vcs} f x∈
  with ∈-++⁻ (subterms⁺ (CS cs)) x∈
... | inj₁ x∈ˡ = f (here refl) x∈ˡ
... | inj₂ x∈ʳ = ↦-∈ᵛ (f ∘ there) x∈ʳ


-- Example well-founded recursion on contracts.
private

  State : ℂ → Set
  State c = ℕ

  Return : ℂ → Set
  Return c = subterms⁺ c ↦ ℕ

  count-decorations : ∀ c → Return c
  count-decorations c = (≺-rec _ go) c 0
    where
      -- ** AGDA BUG **
      -- cannot use `it` in the proofs ≺-put,≺-split,etc..
      -- although it type-checks, the examples stop computing...
    go : ∀ c → (∀ c′ → c′ ≺ c → State c′ → Return c′) → State c → Return c
    go (C (put _ &reveal _ if _ ⇒ cs)) f st (here refl) = st
    go (C (put _ &reveal _ if _ ⇒ cs)) f st (there x∈)  = f (CS cs) ≺-put st x∈
    go (C (split vcs))                 f st (here refl) = st
    go (C (split vcs))                 f st (there x∈)  = f (VCS vcs) ≺-split st x∈
    go (C (_ ⇒ c))                     f = f (C c) ≺-auth ∘ suc
    go (C (after _ ⇒ c))               f = f (C c) ≺-after ∘ suc
    go (C (withdraw _))                _ st (here refl) = st
    go (CS cs)   f st = ↦-∈ λ {d} d∈ → f (C d) (≺-∈ d∈) st
    go (VCS vcs) f st = ↦-∈ᵛ λ {cs} cs∈ → f (CS cs) (≺-∈ᵛ cs∈) st

  module Ex (A B : Participant) where

    vcs' : VContracts
    vcs' = 2 ⊸ (withdraw A ∙)
         ⊕ 3 ⊸ (after 100 ⇒ withdraw B ∙)
         ∙

    cs : Contracts
    cs = A ⇒ withdraw B
       ⊕ B ⇒ split vcs'
       ∙

    _ : subterms⁺ (CS cs) ≡ ⟦ withdraw B , split vcs' , withdraw A , withdraw B ⟧
    _ = refl

    _ : codom (count-decorations (CS cs)) ≡ ⟦ 1 , 1 , 1 , 2 ⟧
    _ = refl
