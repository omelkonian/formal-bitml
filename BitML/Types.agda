------------------------------------------------------------------------
-- BitML datatypes: Contracts & Advertisements
------------------------------------------------------------------------

open import Level    using (0ℓ)
open import Function using (_on_; const; _∘_; id; _∋_)

open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit    using (tt; ⊤)
open import Data.Bool    using (T; true; false)
  renaming (_≟_ to _≟ᵇ_)
open import Data.List    using ( List; []; _∷_; [_]; _++_
                               ; map; concat; concatMap; length; sum; foldr; filter
                               )
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; ∃₂; ∃-syntax; Σ; Σ-syntax)

open import Data.List.Any using (Any; any; here; there)
open import Data.List.Any.Properties using (any⁺)
import Data.List.Relation.Pointwise as PW

open import Data.Nat using ( ℕ; zero; suc; _<_; _>_; _+_; _∸_
                           ; _≤_; z≤n; s≤s; _≤?_; _≥?_; _≟_
                           )
open import Data.Nat.Properties using (<-trans; <-cmp; +-identityʳ; m∸n+n≡m)

open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; toWitness; fromWitness; True)
open import Relation.Binary  using (Decidable)

import Relation.Binary.PropositionalEquality as Eq
-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open Eq using (_≡_; refl; sym; trans; cong; cong₂) --; inspect)

open import Category.Functor using (RawFunctor)
open import Data.List.Categorical renaming (functor to listFunctor)
open RawFunctor {0ℓ} listFunctor using (_<$>_)

module BitML.Types
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))
  where

open import Utilities.Lists
open import Types Participant _≟ₚ_ Honest

------------------------------------------------------------------------
-- Contracts

data Contract : Value  -- the monetary value it carries
              → Values -- the deposits it presumes (kind of a DeBruijn encoding)
              → Set

ContractCases : Set
ContractCases = List (∃[ v ] ∃[ vs ] Contract v vs)

data Split : ContractCases → Value → Set where

  base-split : ----------------------
               Split [] 0

  step-split : ∀ {v Σcs v′ : Value} {vs : Values} {cs : ContractCases} {c : Contract v vs}

             → Split cs Σcs
             → .{p : v′ ≡ v + Σcs}
               -----------------------------------------
             → Split ((v , vs , c) ∷ cs) v′

open import Data.Nat.Properties using (≤⇒≤″; _≤″?_)
open import Data.Nat using (_≤″_) renaming (less-than-or-equal to lt-or-eq)
open _≤″_

split? : ContractCases → Value → Set
split? [] zero    = ⊤
split? [] (suc _) = ⊥
split? ((v , _) ∷ cs) v′   with v ≤″? v′
... | no  _                = ⊥
... | yes (lt-or-eq {k} _) = split? cs k

sound-split : ∀ {cs} {n} {p : split? cs n} → Split cs n
sound-split {[]}                {zero}  {tt} = base-split
sound-split {[]}                {suc n} {()}
sound-split {(v , vs , c) ∷ cs} {n}     {p} with v ≤″? n | p
... | no _                     | ()
... | yes (lt-or-eq {k} v+k≡n) | pp = step-split (sound-split {p = pp}) {sym v+k≡n}

data Put (v′ : Value) : Values → Value → Set where

  base-put : ------------------
             Put v′ [] v′

  step-put : ∀ {v x x+v : Value} {xs : Values}

           → Put v′ xs v
           → .{p : x+v ≡ x + v}
             -------------------------------------
           → Put v′ (x ∷ xs) x+v

put? : Value → Values → Value → Set
put? v′ [] v with v ≟ v′
... | yes _ = ⊤
... | no  _ = ⊥
put? v′ (x ∷ xs) v with x ≤″? v
... | no  _                = ⊥
... | yes (lt-or-eq {k} _) = put? v′ xs k

sound-put : ∀ {xs} {v′ v} {p : put? v′ xs v} → Put v′ xs v
sound-put {[]} {v′} {v} {p} with v ≟ v′ | p
... | no  _    | ()
... | yes refl | _ = base-put
sound-put {x ∷ xs} {v′} {v} {p} with x ≤″? v | p
... | no _                     | ()
... | yes (lt-or-eq {k} x+k≡v) | pp = step-put (sound-put {p = pp}) {sym x+k≡v}

data Contract where

  -- collect deposits and secrets
  put_&reveal_if_⇒_∶-_ : ∀ {v v′ vs′ s′ vs′′}
                      → (vs : Values)
                      → (s : Secrets)
                      → Predicate s′
                      → Contract v′ vs′
                      → .( Put v vs v′ -- v′ ≡ v + sum (lookup <$>ₗ vs))
                         × s′ SETₛ.⊆ s
                         × vs′′ ≡ vs′ ++ vs)
                      → Contract v vs′′

  -- transfer the balance to <Participant>
  withdraw : ∀ {v} → Participant → Contract v []

  -- split the balance
  split_∶-_ : ∀ {v vs} (cs : ContractCases)
        → .(Split cs v) -- v ≡ sum (proj₁ <$>ₗ cs)
        → Contract v vs

  -- wait for participant's authorization
  _∶_ : ∀ {v vs} → Participant → Contract v vs → Contract v vs

  -- wait until time <Time>
  after_∶_ : ∀ {v vs} → Time → Contract v vs → Contract v vs

-- Implicit-proof-style operators.
split_ : ∀ {v vs} (cs : ContractCases) → {p : split? cs v} → Contract v vs
(split cs) {p} = split cs ∶- sound-split {p = p}

put_&reveal_if_⇒_ : ∀ {v v′ vs′ s′ vs′′}
  → (vs : Values)
  → (s : Secrets)
  → Predicate s′
  → Contract v′ vs′
  → .{p₁ : put? v vs v′}
  → .{p₂ : s′ SETₛ.⊆ s}
  → .{p₃ : True (vs′′ SETₙ.≟ₗ vs′ ++ vs)}
  → Contract v vs′′
(put vs &reveal s if p ⇒ c) {p₁} {p₂} {p₃} =
  put vs &reveal s if p ⇒ c
  ∶- (sound-put {p = p₁} , p₂ , toWitness p₃)

-- Lists of contracts.
Contracts : Value → Values → Set
Contracts v vs = List (Contract v vs)

infixr 9 _∶_

infixr 5 _⊕_
_⊕_ : ∀ {A : Set} → A → List A → List A
_⊕_ = _∷_

_∙ : ∀ {A : Set} → A → List A
_∙ = [_]

infix 1 _⊸_
_⊸_ : ∀ {vs : Values}
    → (v : Value)
    → Contract v vs
    → ∃[ v ] ∃[ vs ] Contract v vs
_⊸_ {vs} v c = v , vs , c

------------------------------------------------------------------------
-- Utilities.

secretsᵖ : ∀ {vs} → Participant → Precondition vs → Secrets
secretsᵖ _ (_ :? _) = []
secretsᵖ _ (_ :! _) = []
secretsᵖ A (B :secret s) with A SETₚ.≣ B
... | yes _ = [ s ]
... | no  _ = []
secretsᵖ A (l ∣ r) = secretsᵖ A l ++ secretsᵖ A r

participantsᶜ : ∀ {v vs} → Contracts v vs → List Participant
participantsᶜ = concatMap go
  where
    goᶜ : List (∃[ v ] ∃[ vs ] Contract v vs) → List Participant
    go  : ∀ {v vs} → Contract v vs → List Participant

    goᶜ []                 = []
    goᶜ ((_ , _ , c) ∷ cs) = go c ++ goᶜ cs

    go (put _ &reveal _ if _ ⇒ c ∶- _) = go c
    go (withdraw p)                    = [ p ]
    go (split cs ∶- _)                 = goᶜ cs
    go (p ∶ c)                         = p ∷ go c
    go (after _ ∶ c)                   = go c

participantsᵍ : ∀ {vs} → Precondition vs → List Participant
participantsᵍ (p :? _)      = [ p ]
participantsᵍ (p :! _)      = [ p ]
participantsᵍ (p :secret _) = [ p ]
participantsᵍ (p₁ ∣ p₂)     = participantsᵍ p₁ ++ participantsᵍ p₂

depositsᵖ : ∀ {vs} → Precondition vs → List DepositRef
depositsᵖ (p₁ ∣ p₂)     = depositsᵖ p₁ ++ depositsᵖ p₂
depositsᵖ (a :! v)      = [ (a has v ⟨ true  ⟩) ]
depositsᵖ (a :? v)      = [ (a has v ⟨ false ⟩) ]
depositsᵖ (_ :secret _) = []

persistentDepositsᵖ : ∀ {vs} → Precondition vs → List Deposit
persistentDepositsᵖ = map deposit ∘ filter ((_≟ᵇ true) ∘ persistent) ∘ depositsᵖ

toStipulate : ∀ {vs} → Precondition vs → List (Participant × Value)
toStipulate (p :! v) = [ p , v ]
toStipulate (l ∣ r)  = toStipulate l ++ toStipulate r
toStipulate _        = []

------------------------------------------------------------------------
-- Advertisements.

module _ where

  infix 2 ⟨_⟩_∶-_
  record Advertisement (v : Value) (vsᶜ vsᵍ : Values) : Set where
    constructor ⟨_⟩_∶-_

    field
      G : Precondition vsᵍ
      C : Contracts v vsᶜ

      .valid : -- 1. each name in C appears in G
               vsᶜ ≾ vsᵍ

               -- 2. each participant has a persistent deposit in G
             × participantsᵍ G ++ participantsᶜ C
                 SETₚ.⊆
               (participant <$> persistentDepositsᵖ G)

               -- 3. T0D0: v = Σ vsᵍ

               -- *** correct by construction ***
               -- - names in G are distinct
               -- - secrets in `if ...` appear in `reveal ...`
               -- - the names in put_&_ are distinct

  open Advertisement public

infix 2 put_&reveal_if_⇒_∶-_
infixr 9 _&_

_&_ : ∀ {A B : Set} → A → B → A × B
_&_ = _,_

depositsᵃ : ∀ {v vsᶜ vsᵍ} → Advertisement v vsᶜ vsᵍ → List DepositRef
depositsᵃ ad = depositsᵖ (G ad)
