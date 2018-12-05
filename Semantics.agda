module Semantics where

open import Function   using (_on_; const; _∘_; id; _∋_)
open import Data.Bool  using (T; Bool; true; false; _∧_)
open import Data.Maybe using (Maybe)
open import Data.Nat   using (ℕ; _+_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

open import Utilities.Sets
open import Types
open import STO-Modules
open import BitML

-------------------------------------------------------------------
-- Actions.

data Action : Set₁ where 

  -- commit secrets to stipulate {G}C
  ♯▷_ : ∀ {v} → Advertisement {v} → Action
  
  -- spend x to stipulate {G}C
  _▷ˢ_ : ∀ {v} → Identifier → Advertisement {v} → Action

  -- take branch
  _▷ᵇ_ : ∀ {v} → Identifier → Contract v → Action

  -- join deposits
  _,_▷⟨_,_⟩ : Identifier → Identifier → Participant → Value → Action

  -- divide a deposit
  _▷⟨_,_⟩,⟨_,_⟩ : Identifier → Participant → Value → Participant → Value → Action

  -- donate deposit to participant
  _▷_ : Identifier → Participant → Action

  -- destroy deposit
  -- _♯_▷_ : {!!}
  
-------------------------------------------------------------------
-- Configurations.

data Configuration : Set₁ where

  -- empty
  ∅ᶜ : Configuration

  -- contract advertisement
  `_ : ∀ {v} → Advertisement {v} → Configuration

  -- active contract
  ⟨_,_⟩contract=_ : ∀ {v} → Contracts v → Value → Identifier → Configuration

  -- deposit redeemable by a participant
  ⟨_,_⟩deposit=_ : Participant → Value → Identifier → Configuration

  -- authorization to perform an action
  _[_] : Participant → Action → Configuration

  -- commited secret
  ⟨_∶_♯_⟩ : Participant → Secret → (Maybe ℕ) → Configuration 

  -- revealed secret
  _∶_♯_ : Participant → Secret → ℕ → Configuration

  -- parallel composition
  _∣∣_ : Configuration → Configuration → Configuration
  
infixr 5 _∣∣_

module _ where
  open STO⟦Deposit⟧
  
  depositsᶜ : Configuration → Set⟨Deposit⟩
  depositsᶜ (` x)                 = depositsᵃ x
  depositsᶜ (⟨ a , v ⟩deposit= x) = singleton (a ∷ v ≙ x [ true ])
  depositsᶜ (c₁ ∣∣ c₂)            =  depositsᶜ c₁ ∪ depositsᶜ c₂
  depositsᶜ _                     = ∅

isInitial : Configuration → Bool
isInitial (⟨ _ , _ ⟩deposit= _) = true
isInitial (c₁ ∣∣ c₂)            = isInitial c₁ ∧ isInitial c₂
isInitial _                     = false

Initial : Configuration → Set
Initial = T ∘ isInitial
  
infix 4 _—→_
data _—→_ : Configuration → Configuration → Set₁ where

  -- i) Rules for deposits
  [DEP-AuthJoin] :
    ∀ {A : Participant} {v v′ : Value} {x y : Identifier} {Γ : Configuration}

      ----------------------------------------------------------------------------------
    → ⟨ A , v ⟩deposit= x ∣∣ ⟨ A , v′ ⟩deposit= y ∣∣ Γ
        —→
      ⟨ A , v ⟩deposit= x ∣∣ ⟨ A , v′ ⟩deposit= y ∣∣ A [  x , y ▷⟨ A , (v + v′) ⟩ ] ∣∣ Γ

  [DEP-Join] :
    ∀ {A : Participant} {v v′ : Value} {x y z : Identifier} {Γ Γ′ : Configuration}

    → Γ ≡ A [ x , y ▷⟨ A , v + v′ ⟩ ] ∣∣ A [ y , x ▷⟨ A , v + v′ ⟩ ] ∣∣ Γ′
      ---------------------------------------------------------------------
    → ⟨ A , v ⟩deposit= x ∣∣ ⟨ A , v′ ⟩deposit= y ∣∣ Γ
        —→
      ⟨ A , v + v′ ⟩deposit= z ∣∣ Γ′
    
  [DEP-AuthDivide] :
    ∀ {A : Participant} {v v′ : Value} {x : Identifier} {Γ Γ′ : Configuration}

      --------------------------------------------------------------
    → ⟨ A , v + v′ ⟩deposit= x ∣∣ Γ
        —→
      ⟨ A , v + v′ ⟩deposit= x ∣∣ A [ x ▷⟨ A , v ⟩,⟨ A , v ⟩ ] ∣∣ Γ
    
  [DEP-DIVIDE] :
    ∀ {A : Participant} {v v′ : Value} {x y y′ : Identifier} {Γ Γ′ : Configuration}

    → Γ ≡ A [ x ▷⟨ A , v ⟩,⟨ A , v′ ⟩ ] ∣∣  Γ′
      --------------------------------------------------
    →
      ⟨ A , v + v′ ⟩deposit= x ∣∣ Γ
        —→
      ⟨ A , v ⟩deposit= y ∣∣ ⟨ A , v′ ⟩deposit= y′ ∣∣ Γ′
    
  [DEP-AuthDonate] :
    ∀ {A B : Participant} {v : Value} {x : Identifier} {Γ : Configuration}

      ---------------------------------------------------------------------
    → ⟨ A , v ⟩deposit= x ∣∣ Γ
        —→
      ⟨ A , v ⟩deposit= x ∣∣ A [ x ▷ B ] ∣∣ Γ

  [DEP-Donate] :
    ∀ {A B : Participant} {v : Value} {x y : Identifier} {Γ Γ′ : Configuration}

    → Γ ≡ A [ x ▷ B ] ∣∣ Γ′
      --------------------------
    → ⟨ A , v ⟩deposit= x ∣∣ Γ
        —→
      ⟨ B , v ⟩deposit= y ∣∣ Γ′

  -- [DEP-AuthDestroy]
  -- [DEP-Destroy]
    
  -- ii) Rules for contract advertisements and stipulation

  [C-Advertise] :
    ∀ {A : Participant} {vᶜ : Value} {x : Identifier}
      {Ad : Advertisement {vᶜ}} {G : Precondition} {C : Contracts vᶜ}
      {_ : G ≡ Advertisement.G Ad} {_ : C ≡ Advertisement.C Ad}
      {Γ : Configuration}

    → ∃[ p ∈ participants G ] p ∈ Hon
    → ∀[ d ∈ depositsᵃ Ad ] d ∈ depositsᶜ Γ
    → ∀[ d ∈ depositsᵃ Ad ] record d { persistent = true } ∈ depositsᶜ Γ
      --------------------------------------------
    → Γ —→ ` Ad ∣∣ Γ

  -- [C-AuthCommit]
  -- [C-AuthInit]
  -- [C-Init]

  -- iii) Rules for executing active contracts

  -- [C-Split]
  -- [C-AuthRev]
  -- [C-PutRev]
  -- [C-Withdraw]
  -- [C-AuthControl]
  -- [C-Control]
   
  -- iv) Rules for handling time

  -- [Action]
  -- [Delay]
  -- [Timeout]
  
