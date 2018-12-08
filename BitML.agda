{-# OPTIONS --allow-unsolved-metas #-}

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
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open Eq using (_≡_; refl; sym; trans; cong; cong₂) --; inspect)

open import Category.Functor       using (RawFunctor)
open import Data.Maybe.Categorical renaming (functor to maybeFunctor)
open import Data.List.Categorical  renaming (functor to listFunctor)
open RawFunctor {0ℓ} maybeFunctor renaming (_<$>_ to _<$>ₘ_)
open RawFunctor {0ℓ} listFunctor  renaming (_<$>_ to _<$>ₗ_)

module BitML
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))
  where

open import Utilities.Lists
open import Types Participant _≟ₚ_ Honest

open SETₙ  using ()
  renaming ( _∈_ to _∈ₙ_; ∀∈ to ∀∈ₙ; _∈?_ to _∈?ₙ_; _∉?_ to _∉?ₙ_
           ; _⊆_ to _⊆ₙ_; _⊆?_ to _⊆?ₙ_ ; sound-⊆ to sound-⊆ₙ
           ; _≟ₗ_ to _≟ₙₛ_
           )
open SETₚ  using ()
  renaming ( _∈_ to _∈ₚ_; ∀∈ to ∀∈ₚ; _∈?_ to _∈?ₚ_; _∉?_ to _∉?ₚ_
           ; _⊆_ to _⊆ₚ_; _⊆?_ to _⊆?ₚ_ ; sound-⊆ to sound-⊆ₚ
           ; base-⊆ to base-⊆ₚ; keep-⊆ to keep-⊆ₚ; drop-⊆ to drop-⊆ₚ
           ; _≟ₗ_ to _≟ₚₛ_
           ; nodup to nodupₚ
           )
open SETₑ using ()
  renaming ( _∈_ to _∈ₑ_; ∀∈ to ∀∈ₑ; _∈?_ to _∈?ₑ_; _∉?_ to _∉?ₑ_
           ; _⊆_ to _⊆ₑ_; _⊆?_ to _⊆?ₑ_ ; sound-⊆ to sound-⊆ₑ
           ; _≟ₗ_ to _≟ₑₛ_
           )
open SETₑᵣ using ()
  renaming ( _∈_ to _∈ₑᵣ_; ∀∈ to ∀∈ₑᵣ; _∈?_ to _∈?ₑᵣ_; _∉?_ to _∉?ₑᵣ_
           ; _⊆_ to _⊆ₑᵣ_; _⊆?_ to _⊆?ₑᵣ_ ; sound-⊆ to sound-⊆ₑᵣ
           ; _≟ₗ_ to _≟ₑᵣₛ_
           )
open SETₛ  using ()
  renaming ( _∈_ to _∈ₛ_; ∀∈ to ∀∈ₛ; _∈?_ to _∈?ₛ_; _∉?_ to _∉?ₛ_
           ; _⊆_ to _⊆ₛ_; _⊆?_ to _⊆?ₛ_ ; sound-⊆ to sound-⊆ₛ
           ; _≟ₗ_ to _≟ₛₛ_
           )

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
                         × s′ ⊆ₛ s
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
  → .{p₂ : s′ ⊆?ₛ s}
  → .{p₃ : True (vs′′ ≟ₙₛ vs′ ++ vs)}
  → Contract v vs′′
(put vs &reveal s if p ⇒ c) {p₁} {p₂} {p₃} =
  put vs &reveal s if p ⇒ c
  ∶- (sound-put {p = p₁} , sound-⊆ₛ {p = p₂} , toWitness p₃)

-- Lists of contracts.
Contracts : Value → Values → Set
Contracts v vs = List (Contract v vs)

Contracts∃_←v_←vs_ : (v : Value) → (vs : Values) → (cs : Contracts v vs)
                   → ∃[ v′ ] ∃[ vs′ ] Contracts v′ vs′
Contracts∃ v ←v vs ←vs cs  = v , vs , cs

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

------------------------------------------------------------------------
-- Advertisements.

module _ where

  infix 2 ⟨_⟩_∶-_
  record Advertisement (v : Value) (vsᶜ vsᵍ : Values) : Set where
    constructor ⟨_⟩_∶-_

    field
      G : Precondition vsᵍ
      C : Contracts v vsᶜ

      .valid : -- 1. names in G are distinct
               -- *** correct by construction ***

               -- 2. each name in C appears in G
               vsᶜ ≾ vsᵍ

               -- 3. the names in put_&_ are distinct
               -- *** correct by construction ***

               -- 3'. secrets in `if ...` appear in `reveal ...`
               -- *** correct by construction ***

               -- 4. each participant has a persistent deposit in G
             × nodupₚ (participantsᵍ G ++ participantsᶜ C)
                 ⊆ₚ participant <$>ₗ persistentDepositsᵖ G

  open Advertisement public

-- Implicit-proof constructors.
infix 2 put_&reveal_if_⇒_∶-_
infixr 9 _&_

_&_ : ∀ {A B : Set} → A → B → A × B
_&_ = _,_

⟨_⟩_ : ∀ {v vsᶜ vsᵍ}
     → (g : Precondition vsᵍ)
     → (c : Contracts v vsᶜ)
     → {p₁ : vsᶜ ≾? vsᵍ}
     → {p₂ : nodupₚ (participantsᵍ g ++ participantsᶜ c)
               ⊆?ₚ participant <$>ₗ persistentDepositsᵖ g }
     → Advertisement v vsᶜ vsᵍ
(⟨ g ⟩ c) {p₁} {p₂} = ⟨ g ⟩ c ∶- (sound-≾ {p = p₁} , sound-⊆ₚ {p = p₂})

depositsᵃ : ∀ {v vsᶜ vsᵍ} → Advertisement v vsᶜ vsᵍ → List DepositRef
depositsᵃ ad = depositsᵖ (G ad)

------------------------------------------------------------------------
-- Example.

module AdvertisementExample where
  postulate A B : Participant

  ex-contracts₁ : Contracts 1 []
  ex-contracts₁ = withdraw A ∙

  ex-contracts₂ : Contracts 5 []
  ex-contracts₂ = (A ∶ withdraw A)
                ⊕ (put [] &reveal [] if `True ⇒ withdraw {5} A)
                ∙

  ex-contracts₃ : Contracts 5 [ 100 ]
  ex-contracts₃ = (put [ 100 ] &reveal [] if `True ⇒ withdraw {105} A) ∙

  ex-contracts₄ : Contracts 5 []
  ex-contracts₄ = (A ∶ withdraw {5} B)
                ⊕ (B ∶ split ( (2 ⊸ withdraw {2} A)
                             ⊕ (3 ⊸ after 100 ∶ withdraw {3} B)
                             ⊕ (0 ⊸ put [ 10 ]
                                    &reveal []
                                    if `True
                                    ⇒ (A ∶ withdraw {10} B)
                                    ∶- sound-put & sound-⊆ₛ & refl)
                             ∙))
                ∙

  ex-ad : Advertisement 5 [ 100 ] (200 ∷ 100 ∷ [])
  ex-ad = ⟨ B :! 200 ∣ A :! 100  ⟩ ex-contracts₃
        ∶- sound-≾ & sound-⊆ₚ {p = {!!}}
        -- keep-⊆ₚ {B} {[ A ]} {[ A ]} (keep-⊆ₚ {A} {[]} {[]} base-⊆ₚ)

------------------------------------------------------------------------
-- Decidable equalities.

import Data.Set' as SET

-- Contracts.
_≟ᶜˢ_ : ∀ {v vs} → Decidable {A = Contracts v vs} _≡_
_∃≟ᶜˢ_ : Decidable {A = ∃[ v ] ∃[ vs ] Contracts v vs} _≡_

-- NB: mutual recursion needed  here to satisfy the termination checker
_≟ᶜ_ : ∀ {v vs} → Decidable {A = Contract v vs} _≡_
_∃s≟ᶜ_ : Decidable {A = List (∃[ v ] ∃[ vs ] Contract v vs)} _≡_

[]                  ∃s≟ᶜ []                      = yes refl
[]                  ∃s≟ᶜ (_ ∷ _)                 = no λ ()
(_ ∷ _)             ∃s≟ᶜ []                      = no λ ()
((v , vs , c) ∷ cs) ∃s≟ᶜ ((v′ , vs′ , c′) ∷ cs′) with v ≟ v′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with vs ≟ₙₛ vs′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with c ≟ᶜ c′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with cs ∃s≟ᶜ cs′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl

put_&reveal_if_⇒_∶-_ {_} {v} {vss} {s′ = sᵖ} vs s p c _ ≟ᶜ
 put_&reveal_if_⇒_∶-_ {_} {v′} {vss′} {s′ = sᵖ′} vs′ s′ p′ c′ _
               with vs ≟ₙₛ vs′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with s ≟ₛₛ s′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with sᵖ ≟ₛₛ sᵖ′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with p ≟ₚᵣₑ p′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with v ≟ v′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with vss ≟ₙₛ vss′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with c ≟ᶜ c′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl
(put vs &reveal s if x ⇒ c ∶- x₁) ≟ᶜ withdraw _     = no λ ()
(put vs &reveal s if x ⇒ c ∶- x₁) ≟ᶜ (split _ ∶- _) = no λ ()
(put vs &reveal s if x ⇒ c ∶- x₁) ≟ᶜ (_ ∶ _)        = no λ ()
(put vs &reveal s if x ⇒ c ∶- x₁) ≟ᶜ (after _ ∶ _)  = no λ ()

withdraw x ≟ᶜ withdraw x′ with x ≟ₚ x′
... | no ¬p = no λ{refl → ¬p refl}
... | yes refl = yes refl
withdraw x ≟ᶜ (put _ &reveal _ if _ ⇒ _ ∶- _)       = no λ ()
withdraw x ≟ᶜ (split _ ∶- _)                        = no λ ()
withdraw x ≟ᶜ (_ ∶ _)                               = no λ ()
withdraw x ≟ᶜ (after _ ∶ _)                         = no λ ()

(split cs ∶- _) ≟ᶜ (split cs′ ∶- _) with cs ∃s≟ᶜ cs′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl
(split cs ∶- x) ≟ᶜ (put _ &reveal _ if _ ⇒ _ ∶- _)  = no λ ()
(split cs ∶- x) ≟ᶜ withdraw _                       = no λ ()
(split cs ∶- x) ≟ᶜ (_ ∶ _)                          = no λ ()
(split cs ∶- x) ≟ᶜ (after _ ∶ _)                    = no λ ()

(p ∶ c) ≟ᶜ (p′ ∶ c′) with p ≟ₚ p′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with c ≟ᶜ c′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl
(_ ∶ _) ≟ᶜ (put _ &reveal _  if _ ⇒ _ ∶- _)         = no λ ()
(_ ∶ _) ≟ᶜ withdraw _                               = no λ ()
(_ ∶ _) ≟ᶜ (split _ ∶- _)                           = no λ ()
(_ ∶ _) ≟ᶜ (after _ ∶ _)                            = no λ ()

(after t ∶ c) ≟ᶜ (after t′ ∶ c′) with t ≟ t′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with c ≟ᶜ c′
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl
(after t ∶ c) ≟ᶜ (put _ &reveal _ if _ ⇒ _ ∶- _)    = no λ ()
(after _ ∶ _) ≟ᶜ withdraw _                         = no λ ()
(after _ ∶ _) ≟ᶜ (split _ ∶- _)                     = no λ ()
(after _ ∶ _) ≟ᶜ (_ ∶ _)                            = no λ ()

_∃≟ᶜ_ : Decidable {A = ∃[ v ] ∃[ vs ] Contract v vs} _≡_
c ∃≟ᶜ c′ with [ c ] ∃s≟ᶜ [ c′ ]
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl

[] ≟ᶜˢ [] = yes refl
[] ≟ᶜˢ (_ ∷ _) = no λ ()
(_ ∷ _) ≟ᶜˢ [] = no λ ()
(x ∷ xs) ≟ᶜˢ (y ∷ ys) with x ≟ᶜ y
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with xs ≟ᶜˢ ys
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl

(v , vs , cs) ∃≟ᶜˢ (v′ , vs′ , cs′) with v ≟ v′
... | no ¬p = no λ{refl → ¬p refl}
... | yes refl with vs ≟ₙₛ vs′
... | no ¬p = no λ{refl → ¬p refl}
... | yes refl with cs ≟ᶜˢ cs′
... | no ¬p = no λ{refl → ¬p refl}
... | yes refl = yes refl

module SETᶜ = SET _∃≟ᶜˢ_

Set⟨Contracts⟩ : Set
Set⟨Contracts⟩ = Set'
  where open SETᶜ

-- Advertisements.
_≟ₐ_ : ∀ {v vsᶜ vsᵍ} → Decidable {A = Advertisement v vsᶜ vsᵍ} _≡_
(⟨ G₁ ⟩ C₁ ∶- _) ≟ₐ (⟨ G₂ ⟩ C₂ ∶- _) with G₁ ≟ₚᵣ G₂
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl with C₁ ≟ᶜˢ C₂
... | no ¬p    = no λ{refl → ¬p refl}
... | yes refl = yes refl

_∃≟ₐ_ : Decidable {A = ∃[ v ] ∃[ vsᶜ ] ∃[ vsᵍ ] Advertisement v vsᶜ vsᵍ} _≡_
(v , vsᶜ , vsᵍ , ad) ∃≟ₐ (v′ , vsᶜ′ , vsᵍ′ , ad′) with v ≟ v′
... | no ¬p = no λ{refl → ¬p refl}
... | yes refl with vsᶜ ≟ₙₛ vsᶜ′
... | no ¬p = no λ{refl → ¬p refl}
... | yes refl with vsᵍ ≟ₙₛ vsᵍ′
... | no ¬p = no λ{refl → ¬p refl}
... | yes refl with ad ≟ₐ ad′
... | no ¬p = no λ{refl → ¬p refl}
... | yes refl = yes refl

module SETₐ = SET _∃≟ₐ_

Set⟨Advertisement⟩ : Set
Set⟨Advertisement⟩ = Set'
  where open SETₐ
