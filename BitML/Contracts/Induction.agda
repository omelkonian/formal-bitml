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


{-
validContract? : Advertisement → Bool
validContract? (⟨ g ⟩ cs) = all (λ c → go c (persistents , volatiles)) cs
  where
    persistents : Value
    persistents = sum $ map (proj₁ ∘ proj₂) (persistentDeposits g)

    volatiles : namesʳ c ↦ Value
    volatiles = {!!}

    go : ∀ c → Value × (namesʳ c ↦ Value) → Bool
    go c (v , f) with c
    ... | _ ⇒ d
        = go d (v , f)
    ... | after _ ⇒ d
        = go d (v , f)
    ... | split vcs
        = ⌊ sum (map proj₁ vcs) ≤? v ⌋
        ∧ all (λ{ (v′ , cs) → all (λ c′ → go c′ (v′ , {!!})) cs }) vcs
    ... | put xs &reveal _ if _ ⇒ cs
        = all (λ c′ → go c′ (v + sum (mapWith∈ cs (f ∘ {!names∈!})) , {!!})) cs
 -- (mapWith∈ (? ∘ names∈) xs) , ?)) cs
      where
        names∈ : ∀ {x} → x ∈ xs → x ∈ namesʳ c
        names∈ = {!!} -- ∈-++⁺ˡ ∘ ∈-mapMaybe⁺ ? ?
    ... | withdraw _
        = true
-}

data ℂ : Set where
  C   : Contract → ℂ
  CS  : Contracts → ℂ
  VCS : VContracts → ℂ
  -- AD  : Advertisement → ℂ

subterms subterms⁺ : ℂ → List Contract

subterms c@(C _)   = drop 1 $ subterms⁺ c
subterms c@(CS _)  = subterms⁺ c
subterms c@(VCS _) = subterms⁺ c
-- subterms c@(AD _)  = subterms⁺ c

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
-- subterms⁺ (AD (⟨ _ ⟩ cs))        = subterms⁺ (CS cs)

subterms′ subterms⁺′ : ℂ → List Contract
subterms′ c@(C _)   = drop 1 $ subterms⁺′ c
subterms′ c@(CS _)  = subterms⁺′ c
subterms′ c@(VCS _) = subterms⁺′ c

subterms⁺′ (C c) with c
... | _ ⇒ d                      = subterms⁺′ (C d)
... | after _ ⇒ d                = subterms⁺′ (C d)
... | split vcs                  = subterms⁺′ (VCS vcs)
... | put _ &reveal _ if _ ⇒ cs  = subterms⁺′ (CS cs)
... | withdraw _                 = []
subterms⁺′ (CS [])                = []
subterms⁺′ (CS (c ∷ cs))          = c ∷ subterms⁺′ (C c) ++ subterms⁺′ (CS cs)
subterms⁺′ (VCS [])               = []
subterms⁺′ (VCS ((_ , cs) ∷ vcs)) = subterms⁺′ (CS cs) ++ subterms⁺′ (VCS vcs)

subterms′-names⊆ : d ∈ subterms′ (CS ds) → names d ⊆ names ds
subterms′-names⊆ d∈ = ?

subterms′-putComponents⊆ : d ∈ subterms′ (CS ds) → putComponents d ⊆ putComponents ds
subterms′-putComponents⊆ d∈ = ?


data _≺_ : Rel ℂ 0ℓ where

  ≺-∈  : d ∈ ds → C d ≺ CS ds
  ≺-∈ᵛ : ds ∈ map proj₂ vcs → CS ds ≺ VCS vcs
  instance
    ≺-put   : CS ds ≺ C (put xs &reveal as if p ⇒ ds)
    ≺-auth  : C d ≺ C (A ⇒ d)
    ≺-after : C d ≺ C (after t ⇒ d)
    ≺-split : VCS vcs ≺ C (split vcs)
    -- ≺-ad    : CS ds ≺ AD (⟨ g ⟩ ds)

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
    -- (.(AD (⟨ _ ⟩ _)                  ≻ .(CS _))  ≺-ad    = acc (_ ≻_)

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

  -- Toℂᵃᵈ : Toℂ Advertisement
  -- Toℂᵃᵈ .toℂ = AD

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
      -- although it type-checks, they examples stop computing...
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

{-
  collect : ∀ c → subterms⁺ c ↦ ℕ → List ℕ
  collect (C (put _ &reveal _ if _ ⇒ cs)) f = f (here refl) ∷ collect (CS cs) (f ∘ there)
  collect (C (split vcs))                 f = f (here refl) ∷ collect (VCS vcs) (f ∘ there)
  collect (C (withdraw _))                f = [ f (here refl) ]
  collect (C (_ ⇒ c))       = collect (C c)
  collect (C (after _ ⇒ c)) = collect (C c)
  collect (CS [])       _ = []
  collect (CS (c ∷ cs)) f = collect (C c) (f ∘ ∈-++⁺ˡ) ++ collect (CS cs) (f ∘ ∈-++⁺ʳ _)
  collect (VCS [])               _ = []
  collect (VCS ((_ , cs) ∷ vcs)) f = collect (CS cs) (f ∘ ∈-++⁺ˡ) ++ collect (VCS vcs) (f ∘ ∈-++⁺ʳ _)
-}

{-
record RecState : Set where
  field
    Dₚ,T,o : Contract × HashId × N
    v : Value
    P,t : List Participant × Time


rec : ∀ {X : Set} {{_ : Semigroup X}}

  → (c : ℂ)

  -- → (f-withdraw : Participant → X)
  -- → ()

    --------------
  → subterms c ↦ X
rec {X = X} c = goo _ (≺-wf c)
  where
    goo : (c : ℂ) → Acc _≺_ c → subterms c ↦ X
    goo c (acc a) = {!!}

-}

{-
data _≺_ : Rel ℂ 0ℓ where

  ≺-∈ :
      d ∈ ds
      -----------
    → C d ≺ CS ds

  ≺-∈ᵛ :
      ds ∈ map proj₂ vcs
      ------------------
    → CS ds ≺ VCS vcs

  ≺-put :
      ---------------------------------------
      CS ds ≺ C (put xs &reveal as if p ⇒ ds)

  ≺-auth :
      ---------------
      C d ≺ C (A ⇒ d)

  ≺-after :
      ---------------------
      C d ≺ C (after t ⇒ d)

  ≺-split :
      -----------------------
      VCS vcs ≺ C (split vcs)

  ≺-trans : ∀ {c c′ c″ }
    → c ≺ c′
    → c′ ≺ c″
      -------
    → c ≺ c″

step-≺ : ∀ c {c′ c″} → c ≺ c′ → c′ ≺ c″ → c ≺ c″
step-≺ _ = ≺-trans

stop-≺ : ∀ c {c′} → c ≺ c′ → c ≺ c′
stop-≺ _ x = x

infixr 2 step-≺
infix  3 stop-≺
syntax step-≺ x x<y y∼z = x ≺⟨ x<y ⟩ y∼z
syntax stop-≺ x x<y = x ≺⟨ x<y ⟩∎

module Ex (A B : Participant) where

  cs : Contracts
  cs = A ⇒ withdraw B
     ⊕ B ⇒ split ( 2 ⊸ (withdraw A ∙)
                 ⊕ 3 ⊸ (after 100 ⇒ withdraw B ∙)
                 ⊕ 0 ⊸ (put [ "y" ] ⇒ (A ⇒ withdraw B ∙) ∙)
                 ∙)
     ∙

  _ : C (withdraw B) ≺ CS cs
  _ =
      C (withdraw B)
    ≺⟨ ≺-after ⟩
      C (after 100 ⇒ withdraw B)
    ≺⟨ ≺-∈ (here refl) ⟩
      CS (after 100 ⇒ withdraw B ∙)
    ≺⟨ ≺-∈ᵛ (there (here refl)) ⟩
      VCS ( 2 ⊸ (withdraw A ∙)
          ⊕ 3 ⊸ (after 100 ⇒ withdraw B ∙)
          ⊕ 0 ⊸ (put [ "y" ] ⇒ (A ⇒ withdraw B ∙) ∙)
          ∙)
    ≺⟨ ≺-split ⟩
      C (split ( 2 ⊸ (withdraw A ∙)
               ⊕ 3 ⊸ (after 100 ⇒ withdraw B ∙)
               ⊕ 0 ⊸ (put [ "y" ] ⇒ (A ⇒ withdraw B ∙) ∙)
               ∙))
    ≺⟨ ≺-auth ⟩
      C (B ⇒ split ( 2 ⊸ (withdraw A ∙)
                   ⊕ 3 ⊸ (after 100 ⇒ withdraw B ∙)
                   ⊕ 0 ⊸ (put [ "y" ] ⇒ (A ⇒ withdraw B ∙) ∙)
                   ∙))
    ≺⟨ ≺-∈ (there (here refl)) ⟩∎

  _ : C (withdraw B) ≺ CS cs
  _ = {!!}
-}


{-
get-v : ∀ {c′ : ℂ}
  → c′ ≺ CS c
  → Value
get-v = ?

rec′ : ∀ {X : Set} {{_ : Monoid X}}

  → ValidAdvertisement (⟨ g ⟩ c)

  → (f-withdraw : Participant → X)
  → ()
    -----------------------
  → (∀ c′ → c′ ≺ CS c → X)
rec′ {g = g} {c = c} vad f-withdraw
  with c
... |

rec : ∀ {X : Set} {{_ : Monoid X}}
    ...
    -----------------------
  → X
rec ... = fold ∘ rec′ ....
-}

{-

_∈ℂ_ : Rel ℂ 0ℓ
C c   ∈ℂ CS cs   = c ∈ cs
C c   ∈ℂ VCS vcs = ∃ λ cs → (C c ∈ℂ CS cs) × (CS cs ∈ℂ VCS vcs)
CS cs ∈ℂ VCS vcs = cs ∈ map proj₂ vcs
_     ∈ℂ _       = ⊥

_≺_ : Rel ℂ 0ℓ
CS cs   ≺ C (put _ &reveal _ if _ ⇒ cs′) = cs ≡ cs′
VCS vcs ≺ C (split vcs′)                 = vcs ≡ vcs′
C c     ≺ C (_ ⇒ c′)                     = c ≡ c′
C c     ≺ C (after _ ⇒ c′)               = c ≡ c′
c       ≺ c′                             = c ∈ℂ c′
-}

{-
≺-wf : WellFounded _≺_
≺-wf = acc ∘ flip _≻_
  where
    _≻_ : ∀ c′ c → c′ ≺ c → Acc _≺_ c′
    (CS cs   ≻ C (put _ &reveal _ if _ ⇒ .cs) ) refl = acc (_≻ CS cs)
    (VCS vcs ≻ C (split .vcs)  )                refl = acc (_≻ VCS vcs)
    (C c     ≻ C (_ ⇒ .c)      )                refl = acc (_≻ C c)
    (C c     ≻ C (after _ ⇒ .c))                refl = acc (_≻ C c)

    (C c ≻ CS (.c ∷ _)) (here refl) = acc (_≻ C c)
    (C c ≻ CS (_ ∷ cs)) (there c∈)  = (C c ≻ CS cs) c∈

    (C c ≻ VCS ((v , .cs) ∷ vcs)) (cs , c∈ , here refl) = (C c ≻ CS cs) c∈
    (C c ≻ VCS (_ ∷ vcs))         (cs , c∈ , there cs∈) = (C c ≻ VCS vcs) (cs , c∈ , cs∈)

    (CS cs ≻ VCS ((v , .cs) ∷ vcs)) (here refl) = acc (_≻ CS cs)
    (CS cs ≻ VCS ((v , _)   ∷ vcs)) (there cs∈) = (CS cs ≻ VCS vcs) cs∈
-}
