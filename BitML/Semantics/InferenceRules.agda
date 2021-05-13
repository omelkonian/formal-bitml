-----------------------------------------------
-- Small-step semantics for the BitML calculus.
-----------------------------------------------
open import Prelude.Init
open import Prelude.Lists
open import Prelude.DecLists
open import Prelude.Membership
open import Prelude.DecEq
open import Prelude.Sets

open import BitML.BasicTypes
open import BitML.Predicate hiding (`; ∣_∣)

module BitML.Semantics.InferenceRules
  (Participant : Set)
  ⦃ _ : DecEq Participant ⦄
  (Honest : List⁺ Participant)
  where

open import BitML.Contracts Participant Honest
open import BitML.Semantics.Action Participant Honest
open import BitML.Semantics.Configurations.Types Participant Honest
open import BitML.Semantics.Configurations.Helpers Participant Honest
open import BitML.Semantics.Label Participant Honest
open import BitML.Semantics.Predicate Participant Honest

---------------------------------------------
-- Semantic rules for untimed configurations.

-- T0D0 fresh variables can be arbitrarily picked out, maybe that is wrong?
-- solve by requiring something like `fresh α ∉ fuv(Γ)`

infix -1 _—→[_]_
data _—→[_]_ : Configuration → Label → Configuration → Set where

  ------------------------------
  -- i) Rules for deposits

  [DEP-AuthJoin] :

      --——————————————————————————————————————————————————————————————————————
      ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at y ∣ Γ
        —→[ auth-join[ A , x ↔ y ] ]
      ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at y ∣ A auth[ x ↔ y ▷⟨ A , v + v′ ⟩ ] ∣ Γ


  [DEP-Join] :

      --——————————————————————————————————————————————————————————————————————
      ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at y ∣ A auth[ x ↔ y ▷⟨ A , v + v′ ⟩ ] ∣ Γ
        —→[ join[ x ↔ y ] ]
      ⟨ A has (v + v′) ⟩at z ∣ Γ


  [DEP-AuthDivide] :

      --——————————————————————————————————————————————————————————————————————
      ⟨ A has (v + v′) ⟩at x ∣ Γ
        —→[ auth-divide[ A , x ▷ v , v′ ] ]
      ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ] ∣ Γ


  [DEP-Divide] :

      --——————————————————————————————————————————————————————————————————————
      ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ] ∣ Γ
        —→[ divide[ x ▷ v , v′ ] ]
      ⟨ A has v ⟩at y ∣ ⟨ A has v′ ⟩at y′ ∣ Γ


  [DEP-AuthDonate] :

      --——————————————————————————————————————————————————————————————————————
      ⟨ A has v ⟩at x ∣ Γ
        —→[ auth-donate[ A , x ▷ᵈ B ] ]
      ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B ] ∣ Γ


  [DEP-Donate] :

      --——————————————————————————————————————————————————————————————————————
      ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B ] ∣ Γ
        —→[ donate[ x ▷ᵈ B ] ]
      ⟨ B has v ⟩at y ∣ Γ


  [DEP-AuthDestroy] :
    ∀ {ds : List (Participant × Value × Id)} {j : Index ds}

    → let xs = map (proj₂ ∘ proj₂) ds
          Aj = proj₁ (ds ‼ j)
          j′ = ‼-map {xs = ds} j
          Δ  = || map (λ{ (Ai , vi , xi) → ⟨ Ai has vi ⟩at xi }) ds
      in
      --——————————————————————————————————————————————————————————————————————
      Δ ∣ Γ
        —→[ auth-destroy[ Aj , xs , j′ ] ]
      Δ ∣ Aj auth[ xs , j′ ▷ᵈˢ y ] ∣ Γ


  [DEP-Destroy] :
    ∀ {ds : List (Participant × Value × Id)}

    → let xs = map (proj₂ ∘ proj₂) ds
          Δ  = || map (λ{ (i , Ai , vi , xi) → ⟨ Ai has vi ⟩at xi ∣ Ai auth[ xs , ‼-map {xs = ds} i ▷ᵈˢ y ] })
                      (enumerate ds)
      in
      --——————————————————————————————————————————————————————————————————————
      Δ ∣ Γ
        —→[ destroy[ xs ] ]
      Γ

  ------------------------------------------------------------
  -- ii) Rules for contract advertisements and stipulation

  [C-Advertise] : let ⟨ G ⟩ _ = ad in

      ValidAdvertisement ad              -- the advertisement is valid
    → Any (_∈ Hon) (participants G) -- at least one honest participant
    → deposits ad ⊆ deposits Γ           -- all persistent deposits in place
      --——————————————————————————————————————————————————————————————————————
    → Γ —→[ advertise[ ad ] ] ` ad ∣ Γ


  [C-AuthCommit] : let ⟨ G ⟩ _ = ad in
    ∀ {secrets : List (Secret × Maybe ℕ)}

    → let (as , ms) = unzip secrets
          Δ         = || map (λ{ (ai , Ni) → ⟨ A ∶ ai ♯ Ni ⟩}) secrets
      in

      as ≡ secretsOfᵖ A G         -- a₁..aₖ secrets of A in G
    → All (_∉ secretsOfᶜᶠ A Γ) as -- ∀i ∈ 1..k : ∄N : {A : aᵢ ♯ N} ∈ Γ
    → (A ∈ Hon → All Is-just ms)  -- honest participants commit to valid lengths
      --——————————————————————————————————————————————————————————————————————
    → ` ad ∣ Γ
        —→[ auth-commit[ A , ad , secrets ] ]
      ` ad ∣ Γ ∣ Δ ∣ A auth[ ♯▷ ad ]


  [C-AuthInit] : let ⟨ G ⟩ _ = ad; partG = nub-participants G in

      partG ⊆ committedParticipants Γ ad -- all participants have committed their secrets
    → (A , v , x) ∈ persistentDeposits G -- G = A :! v @ x | ...
      --——————————————————————————————————————————————————————————————————————
    → ` ad ∣ Γ
        —→[ auth-init[ A , ad , x ] ]
      ` ad ∣ Γ ∣ A auth[ x ▷ˢ ad ]


  [C-Init] : let ⟨ G ⟩ C = ad in

      -- all participants have committed their secrets (guaranteed from [C-AuthInit])

      let toSpend = persistentDeposits G
          vs      = map (proj₁ ∘ proj₂) toSpend
      in
      --——————————————————————————————————————————————————————————————————————
      ` ad ∣ Γ ∣ || map (λ{ (Ai , vi , xi) → ⟨ Ai has vi ⟩at xi ∣ Ai auth[ xi ▷ˢ ad ] }) toSpend
               ∣ || map (_auth[ ♯▷ ad ]) (nub-participants G)
        —→[ init[ G , C ] ]
      ⟨ C , sum vs ⟩at x ∣ Γ


  ---------------------------------------------------
  -- iii) Rules for executing active contracts

  [C-Split] :
    ∀ {vcis : List (Value × Contracts × Id)}

    → let (vs , cs , _) = unzip₃ vcis in
      --——————————————————————————————————————————————————————————————————————
      ⟨ [ split (zip vs cs) ] , sum vs ⟩at y ∣ Γ
        —→[ split[ y ] ]
      || map (λ{ (vi , ci , xi) → ⟨ ci , vi ⟩at xi }) vcis ∣ Γ


  [C-AuthRev] :

      --——————————————————————————————————————————————————————————————————————
      ⟨ A ∶ a ♯ just n ⟩ ∣ Γ
        —→[ auth-rev[ A , a ] ]
      A ∶ a ♯ n ∣ Γ


  [C-PutRev] :
    ∀ {ds : List (Participant × Value × Id)}
      {ss : List (Participant × Secret × ℕ)}

    → let (_ , vs , xs) = unzip₃ ds
          (_ , as , _)  = unzip₃ ss
          Γ = || map (λ{ (Ai , vi , xi) → ⟨ Ai has vi ⟩at xi }) ds
          Δ = || map (λ{ (Bi , ai , Ni) → Bi ∶ ai ♯ Ni       }) ss
      in

      ⟦ p ⟧ Δ ≡ just true -- predicate is true
      --——————————————————————————————————————————————————————————————————————
    → ⟨ [ put xs &reveal as if p ⇒ c ] , v ⟩at y ∣ Γ ∣ Δ ∣ Γ′
        —→[ put[ xs , as , y ] ]
      ⟨ c , v + sum vs ⟩at z ∣ Δ ∣ Γ′


  [C-Withdraw] :

      --——————————————————————————————————————————————————————————————————————
      ⟨ [ withdraw A ] , v ⟩at y ∣ Γ
        —→[ withdraw[ A , v , y ] ]
      ⟨ A has v ⟩at x ∣ Γ


  [C-AuthControl] :
    ∀ {i : Index c}

    → let d = c ‼ i in

      A ∈ authDecorations d -- D ≡ A : D′
      --——————————————————————————————————————————————————————————————————————
    → ⟨ c , v ⟩at x ∣ Γ
        —→[ auth-control[ A , x ▷ d ] ]
      ⟨ c , v ⟩at x ∣ A auth[ x ▷ d ] ∣ Γ


  -- T0D0 linearize, i.e. introduce new label and produce intermediate configuration:
  -- ⟨ c , v ⟩at x ∣ Δ ∣ Γ —→[ choice[c , i] ] ⟨ [ d′ ] , v ⟩at x ∣ Γ
  [C-Control] :
    ∀ {i : Index c}

    → let d  = c ‼ i
          d′ = removeTopDecorations d
      in

      ⟨ [ d′ ] , v ⟩at x ∣ Γ ≈ L
    → L —→[ α ] Γ′ -- T0D0 replace with _—↠_?
    → cv α ≡ just x
      --——————————————————————————————————————————————————————————————————————
    → ⟨ c , v ⟩at x ∣ || map _auth[ x ▷ d ] (nub (authDecorations d)) ∣ Γ
        —→[ α ]
      Γ′


-------------------------------------------
-- Semantic rules for timed configurations.

infix 3 _≈ₜ_
_≈ₜ_ : TimedConfiguration → TimedConfiguration → Set
c ≈ₜ c′ = (time c ≡ time c′) × (cfg c ≈ cfg c′)

infix -1 _—→ₜ[_]_
data _—→ₜ[_]_ : TimedConfiguration → Label → TimedConfiguration → Set where

  -- iv) Rules for handling time
  [Action] :

      Γ —→[ α ] Γ′
    → cv α ≡ nothing
      --——————————————————————————————————————————————————————————————————————
    → Γ at t —→ₜ[ α ] Γ′ at t


  [Delay] :

      δ > 0
      --——————————————————————————————————————————————————————————————————————
    → Γ at t —→ₜ[ delay[ δ ] ] Γ at (t + δ)


  [Timeout] :
    ∀ {i : Index c}

    → let d         = c ‼ i
          d′        = removeTopDecorations d
          (As , ts) = decorations d
      in

      As ≡ []                           -- no authorizations required to pick branch
    → All (_≤ t) ts                     -- all time constraints are satisfied
    → ⟨ [ d′ ] , v ⟩at x ∣ Γ —→[ α ] Γ′ -- resulting state if we pick branch
    → cv α ≡ just x
      --——————————————————————————————————————————————————————————————————————
    → (⟨ c , v ⟩at x ∣ Γ) at t —→ₜ[ α ] Γ′ at t
