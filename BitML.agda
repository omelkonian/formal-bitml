module BitML where

open import Function using (_on_; const; _∘_; id; _∋_)
open import Data.Unit using (tt; ⊤)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃₂; ∃-syntax; Σ; Σ-syntax)
  renaming (_,_ to _—→_)
open import Data.Bool using (T; true; false)
open import Data.List using (List; []; _∷_; [_]; _++_; map; concatMap; length; sum)

open import Data.Nat using (ℕ; _<_; _>_; _+_)
open import Data.Nat.Properties using (<-trans; <-cmp; +-identityʳ)

import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open Eq using (_≡_; refl; sym; trans; cong; cong₂)

open import Utilities.Lists using (_<$>_)
open import Utilities.Sets
open import Types
open import STO-Modules

-- Honest set of participants
module _ where
  open STO⟦Participant⟧
  
  postulate
    Honest : Σ[ s ∈ Set⟨Participant⟩ ] (∣ s ∣ > 0)
    
  Hon = proj₁ Honest

-- Arithmetic expressions
data Arith : Set where

  `_ : ℕ → Arith

  len : Secret → Arith
    
  _`+_ : Arith → Arith → Arith

  _`-_ : Arith → Arith → Arith
  

-- Predicates
data Predicate : Set where

  True : Predicate
  
  _/\_ : Predicate → Predicate → Predicate

  ~_ : Predicate → Predicate

  _==_ : Arith → Arith → Predicate

  _≺_ : Arith → Arith → Predicate

-- Contracts

postulate
  lookup : Identifier → Value

-- a contract is indexed by the monetary value it carries
data Contract (v : Value) : Set where

  -- collect deposits and secrets
  put_&reveal_if_⇒_ : ∀ {v′} 
                    → (xs : List Identifier)
                    → List Secret → Predicate
                    → Contract v′
                    → {_ : v′ ≡ v + sum (lookup <$> xs)}
                    → Contract v

  -- transfer the balance to <Participant>
  withdraw : Participant → Contract v

  -- split the balance
  split : ∀ (xs : List (Σ[ v ∈ Value ] Contract v))
        → v ≡ sum (proj₁ <$> xs)
        → Contract v
  
  -- wait for participant's authorization
  _∶_ : Participant → Contract v → Contract v

  -- wait until time <Time>
  after_∶_ : Time → Contract v → Contract v
  
infixr 9 _∶_

put_&reveal_⇒_ : ∀ {v}
               → (xs : List Identifier)
               → List Secret
               → {v′ : Value} → Contract v′
               → {_ : v′ ≡ v + sum (lookup <$> xs)}
               → Contract v
(put x &reveal s ⇒ C) {P} = (put x &reveal s if True ⇒ C) {P}

Contracts : ∀ (v : Value) → Set
Contracts v = List (Contract v)

infixr 5 _⊕_
_⊕_ : ∀ {A : Set} → A → List A → List A
_⊕_ = _∷_

_∙ : ∀ {A : Set} → A → List A
_∙ = [_]

example : Contracts 5
example =
    (A ∶ withdraw B)
  ⊕ (B ∶ split
        ( (2 —→ withdraw A)
        ⊕ (3 —→ after 100 ∶ withdraw B)
        ⊕ (0 —→ (put [ "x" ] &reveal [] ⇒ (A ∶ withdraw {10} B))
          {begin
             10
           ≡⟨ vx ⟩
             lookup "x"
           ≡⟨ sym (+-identityʳ (lookup "x")) ⟩
             lookup "x" + 0
           ∎
          })
        ∙
        ) refl)
  ∙
  where
    postulate vx : 10 ≡ lookup "x"

distinct : List Identifier → Set
distinct xs = length xs ≡ ∣ fromList xs ∣
  where open STO⟦Identifier⟧

names : ∀ {v} → Contracts v → List Identifier
names = concatMap names′
  where
    names′  : ∀ {v} → Contract v      → List Identifier
    names′′ : List (Σ Value Contract) → List Identifier

    names′ (put xs &reveal as if _ ⇒ c) = (xs ++ as) ++ names′ c
    names′ (withdraw _)                 = []
    names′ (split xs x)                 = names′′ xs
    names′ (_ ∶ c)                      = names′ c
    names′ (after _ ∶ c)                = names′ c

    names′′ []              = []
    names′′ ((_ —→ c) ∷ xs) = names′ c ++ names′′ xs

namesₚ : Precondition → List Identifier
namesₚ (_ :? _ ≙ x)  = [ x ]
namesₚ (_ :! _ ≙ x)  = [ x ]
namesₚ (_ :secret x) = [ x ]
namesₚ (p₁ ∣ p₂)     = namesₚ p₁ ++ namesₚ p₂

module _ where
  open STO⟦Identifier⟧
  
  nameset : ∀ {v} → Contracts v → Set⟨Identifier⟩ 
  nameset = fromList ∘ names

  namesetₚ : Precondition → Set⟨Identifier⟩ 
  namesetₚ = fromList ∘ namesₚ
  
participants : Precondition → Set⟨Participant⟩
participants = fromList ∘ participants′
  where
    open STO⟦Participant⟧

    participants′ : Precondition → List Participant
    participants′ (p :? _ ≙ _)  = [ p ]
    participants′ (p :! _ ≙ _)  = [ p ]
    participants′ (p :secret _) = [ p ]
    participants′ (p₁ ∣ p₂)     = participants′ p₁ ++ participants′ p₂

depositsᵖ : Precondition → Set⟨Deposit⟩
depositsᵖ = fromList ∘ deposits′
  where
    open STO⟦Deposit⟧

    deposits′ : Precondition → List Deposit
    deposits′ (p₁ ∣ p₂)     = deposits′ p₁ ++ deposits′ p₂
    deposits′ (a :! v ≙ x)  = [ a ∷ v ≙ x [ true ] ]
    deposits′ (a :? v ≙ x)  = [ a ∷ v ≙ x [ false ] ]
    deposits′ (_ :secret _) = []

putNames : ∀ {v} → Contracts v → List Identifier
putNames = concatMap putNames′ 
  where
    putNames′ : ∀ {v} → Contract v → List Identifier
    putNames′ (put xs &reveal _ if _ ⇒ _) = xs
    putNames′ _                           = []

record Advertisement {v : Value} : Set₁ where
  constructor ⟨_⟩_∶-_

  field
    G : Precondition
    C : Contracts v

    valid : -- names in G are distinct
            distinct (namesₚ G)
            -- each name in C appears in G
          × ∀[ x ∈ nameset C ]
             x ∈ namesetₚ G
            -- the names in put_&_ are distinct
          × distinct (putNames C)
            -- each participant has a persistent deposit in G
          × ∀[ p ∈ participants G ]
             ∃₂ λ x v →
               (A ∷ v ≙ x [ true ]) ∈ depositsᵖ G

open Advertisement public

depositsᵃ : ∀ {v} → Advertisement {v} → Set⟨Deposit⟩
depositsᵃ ad = depositsᵖ (G ad)
