module BitML where

open import Function using (_on_; const; _∘_; id; _∋_)
open import Data.Unit using (tt; ⊤)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃₂; ∃-syntax; Σ; Σ-syntax)
  renaming (_,_ to _—→_)
open import Data.Bool using (T)
open import Data.List using (List; []; _∷_; [_]; map; length; sum)
open import Data.String using (String)

open import Data.Nat using (ℕ; _<_; _>_; _+_)
open import Data.Nat.Properties using (<-trans; <-cmp; +-identityʳ)

import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary  using ( IsStrictTotalOrder; Transitive; Trichotomous
                                   ; tri<; tri≈; tri> )
import Relation.Binary.Construct.On as On
open IsStrictTotalOrder using (compare)
  renaming (trans to sto-trans)

open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open Eq using (_≡_; refl; sym; trans; cong; cong₂)
  renaming (isEquivalence to ≡-isEquivalence)

open import Utilities.Sets
open import Types
open import STO-Modules

-- Honest set of participants
module _ where
  open STO⟦Participant⟧
  postulate
    Honest : Σ[ s ∈ Set⟨Participant⟩ ] (∣ s ∣ > 0)

-- Arithmetic expressions
data Arith : Set where

  `_ : ℕ → Arith

  len : Secret → Arith
    
  _`+_ : Arith → Arith → Arith

  _`-_ : Arith → Arith → Arith
  

-- Predicates
data Predicate : Set where

  True : Predicate
  
  _∧_ : Predicate → Predicate → Predicate

  ¬_ : Predicate → Predicate

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
                    → {_ : v′ ≡ v + sum (map lookup xs)}
                    → Contract v

  -- transfer the balance to <Participant>
  withdraw : Participant → Contract v

  -- split the balance
  split : ∀ (xs : List (Σ[ v ∈ Value ] Contract v))
        → v ≡ sum (map proj₁ xs)
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
               → {_ : v′ ≡ v + sum (map lookup xs)}
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
names c = {!!}

namesₚ : Precondition → List Identifier
namesₚ p = {!!}

module _ where
  open STO⟦Identifier⟧
  
  nameset : ∀ {v} → Contracts v → Set⟨Identifier⟩ 
  nameset = fromList ∘ names

  namesetₚ : Precondition → Set⟨Identifier⟩ 
  namesetₚ = fromList ∘ namesₚ
  
participants : Precondition → Set⟨Participant⟩
participants p = {!!}

deposits : Precondition → Set⟨Precondition⟩
deposits p = {!!}

putNames : ∀ {v} → Contracts v → List Identifier
putNames c = {!!}

record Advertisement {v : Value} : Set₁ where
  constructor ⟨_⟩_⟦_⟧

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
               (A :! v ≙ x) ∈ deposits G
