------------------------------------------------------------------------
-- Symbolic strategies.
------------------------------------------------------------------------

open import Data.Maybe   using (nothing)
open import Data.Product using (∃; ∃-syntax; Σ; Σ-syntax; _×_; _,_)
open import Data.Nat     using (_>_)
open import Data.List    using (List; length; map)

open import Relation.Binary                       using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

module SymbolicModel.Strategy
  (Participant : Set)
  (_≟ₚ_ : Decidable {A = Participant} _≡_)
  (Honest : Σ[ ps ∈ List Participant ] (length ps > 0))
  where

open import Utilities.Lists
import Data.Set' as SET

open import Types                            Participant _≟ₚ_ Honest
open import BitML.Types                      Participant _≟ₚ_ Honest
open import BitML.DecidableEquality          Participant _≟ₚ_ Honest
open import Semantics.Actions.Types          Participant _≟ₚ_ Honest
open import Semantics.Configurations.Types   Participant _≟ₚ_ Honest
open import Semantics.Configurations.Helpers Participant _≟ₚ_ Honest
open import Semantics.InferenceRules         Participant _≟ₚ_ Honest
open import Semantics.Labels.Types           Participant _≟ₚ_ Honest

----------------------------------
-- Finite sets of actions.

open import Semantics.Actions.DecidableEquality Participant _≟ₚ_ Honest

----------------------------------
-- Symbolic runs.

{- Version 1: New list-like, labelled datatype with existential elements. -}

data SymbolicRun : Set where
  ∙ˢ     : SymbolicRun

  _∷ˢ⟦_⟧_ : ∃TimedConfiguration → Label → SymbolicRun → SymbolicRun


mapRun : (∃TimedConfiguration → ∃TimedConfiguration)
       → (Label → Label)
       → SymbolicRun → SymbolicRun
mapRun _ _ ∙ˢ             = ∙ˢ
mapRun f g (tc ∷ˢ⟦ a ⟧ s) = f tc ∷ˢ⟦ g a ⟧ mapRun f g s

{- Version 2: Using —↠ₜ directly.

SymbolicRun : Set
SymbolicRun =
  ∃[ ads₀ ] ∃[ cs₀ ] ∃[ ds₀ ]
  ∃[ adsₙ ] ∃[ csₙ ] ∃[ dsₙ ]
   (Σ[ Γ₀ ∈ Configuration ads₀ cs₀ ds₀ ]
    Σ[ Γₙ ∈ Configuration adsₙ csₙ dsₙ ]
    Σ[ tₙ ∈ Time ]
    Σ[ â  ∈ Labels ]
      ( Initial Γ₀
      × (Γ₀ at 0 —↠ₜ[ â ] Γₙ at tₙ)
      ))

mapRun : (∀ {ads cs ds} → Configuration ads cs ds → Configuration ads cs ds)
       → (Label → Label)
       → SymbolicRun → SymbolicRun
mapRun f g (ads₀ , cs₀ , ds₀ , adsₙ , csₙ , dsₙ , Γ₀ , Γₙ , tₙ , â , init , ((Γ at .0) ∎∎ₜ))
         = (ads₀ , cs₀ , ds₀ , adsₙ , csₙ , dsₙ , Γ₀ , Γₙ , tₙ , â , init , ((f Γ at .0) ∎∎ₜ))
mapRun f g (ads₀ , cs₀ , ds₀ , adsₙ , csₙ , dsₙ , Γ₀ , Γₙ , tₙ , â , init , ((Γ at .0) —→ₜ⟨ x ⟩ x₁ ⊢ tr))
         = (ads₀ , cs₀ , ds₀ , adsₙ , csₙ , dsₙ , Γ₀ , Γₙ , tₙ , â , init , ((Γ at .0) —→ₜ⟨ x ⟩ x₁ ⊢ tr))
mapRun f g (_ , _ , _ , _ , _ , _ , _ , _ , _ , _ , _ , (( at .0) —→ₜ⟨ x ⟩ x₁ ⊢ tr)) = {!!}

-}

-- Hide all committed secrets in a symbolic run.
strip : SymbolicRun → SymbolicRun
strip = mapRun (λ{ (ads , cs , ds , Γ at t) → (ads , cs , ds , stripSecrets Γ at t) }) stripLabel
  where
    stripSecrets : ∀ {ads cs ds} → Configuration ads cs ds → Configuration ads cs ds
    stripSecrets ⟨ p ∶ a ♯ _ ⟩ = ⟨ p ∶ a ♯ nothing ⟩
    stripSecrets c = c

    stripCommit : CommittedSecret → CommittedSecret
    stripCommit (p , s , _) = p , s , nothing

    stripLabel : Label → Label
    stripLabel auth-commit[ p , ad , ss ] = auth-commit[ p , ad , map stripCommit ss ]
    stripLabel a = a


----------------------------------
-- Symbolic strategies.

SymbolicStrategy : Set
SymbolicStrategy = SymbolicRun → Set⟨Action⟩

ValidStrategy : SymbolicStrategy → Set
ValidStrategy s = {!!} -- only self-authorizations
