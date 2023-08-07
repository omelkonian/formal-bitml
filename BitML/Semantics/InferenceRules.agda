-----------------------------------------------
-- Small-step semantics for the BitML calculus
-----------------------------------------------
open import Prelude.Init; open SetAsType
open L.Mem
open import Prelude.Lists
open import Prelude.Lists.Dec
open import Prelude.DecEq
open import Prelude.Sets
open import Prelude.Nary
open import Prelude.Setoid
open import Prelude.Ord
open import Prelude.General
open import Prelude.InferenceRules
open import Prelude.Split renaming (split to mkSplit)
open import Prelude.Null

open import BitML.BasicTypes
open import BitML.Predicate

module BitML.Semantics.InferenceRules (⋯ : ⋯) (let open ⋯ ⋯) where

open import BitML.Contracts ⋯ hiding (d; C; G)
open import BitML.Semantics.Action ⋯
open import BitML.Semantics.Configurations.Types ⋯
open import BitML.Semantics.Configurations.Helpers ⋯
open import BitML.Semantics.Label ⋯
open import BitML.Semantics.Predicate ⋯

---------------------------------------------
-- Semantic rules for untimed configurations.

-- T0D0 freshness conditions are not completely accurate
-- i.e. using `ids Γ` does not examine names in authorization

infix -1 _—[_]→_ _—[_]↛_
data _—[_]→_ : Cfg → Label → Cfg → Type where

  ------------------------------
  -- i) Rules for deposits

  [DEP-AuthJoin] :

    ────────────────────────────────────────────────────────────────────────
    ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at y ∣ Γ
      —[ auth-join⦅ A , x ↔ y ⦆ ]→
    ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at y ∣ A auth[ x ↔ y ▷⟨ A , v + v′ ⟩ ] ∣ Γ


  [DEP-Join] :

    z ∉ x ∷ y ∷ ids Γ -- z fresh
    ────────────────────────────────────────────────────────────────────────
    ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at y ∣ A auth[ x ↔ y ▷⟨ A , v + v′ ⟩ ] ∣ Γ
      —[ join⦅ x ↔ y ⦆ ]→
    ⟨ A has (v + v′) ⟩at z ∣ Γ


  [DEP-AuthDivide] :

    ────────────────────────────────────────────────────────
    ⟨ A has (v + v′) ⟩at x ∣ Γ
      —[ auth-divide⦅ A , x ▷ v , v′ ⦆ ]→
    ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ] ∣ Γ


  [DEP-Divide] :

    All (_∉ x ∷ ids Γ) [ y ⨾ y′ ] -- y, y′ fresh
    ────────────────────────────────────────────────────────
    ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ] ∣ Γ
      —[ divide⦅ x ▷ v , v′ ⦆ ]→
    ⟨ A has v ⟩at y ∣ ⟨ A has v′ ⟩at y′ ∣ Γ


  [DEP-AuthDonate] :

    ──────────────────────────────────────
    ⟨ A has v ⟩at x ∣ Γ
      —[ auth-donate⦅ A , x ▷ᵈ B ⦆ ]→
    ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B ] ∣ Γ


  [DEP-Donate] :

    y ∉ x ∷ ids Γ -- y fresh
    ──────────────────────────────────────
    ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B ] ∣ Γ
      —[ donate⦅ x ▷ᵈ B ⦆ ]→
    ⟨ B has v ⟩at y ∣ Γ


  [DEP-AuthDestroy] :
    ∀ {ds : DepositRefs} {j : Index ds} →

    let xs = map select₃ ds
        Aⱼ = (ds ‼ j) .proj₁
        j′ = ‼-map {xs = ds} j
        Δ  = || map (uncurry₃ ⟨_has_⟩at_) ds
    in

    y ∉ ids Γ -- y fresh (except in destroy authorizations for xs)
    ──────────────────────────────────────────────────────────────
    Δ ∣ Γ
      —[ auth-destroy⦅ Aⱼ , xs , j′ ⦆ ]→
    Δ ∣ Aⱼ auth[ xs , j′ ▷ᵈˢ y ] ∣ Γ


  [DEP-Destroy] :
    ∀ {ds : DepositRefs} →

    let
      xs = map select₃ ds
      Δ  = || map (λ (i , Aᵢ , vᵢ , xᵢ) →
                     ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xs , ‼-map {xs = ds} i ▷ᵈˢ y ]
                  ) (enumerate ds)
    in
    ─────────────────────────────────────────────────────────────────────────────
    Δ ∣ Γ
      —[ destroy⦅ xs ⦆ ]→
    Γ

  ------------------------------------------------------------
  -- ii) Rules for contract advertisements and stipulation

  [C-Advertise] : let open ∣AD ad in

    ∙ ValidAd ad               -- the advertisement is valid
    ∙ Any (_∈ Hon) partG       -- at least one honest participant
    ∙ deposits ad ⊆ deposits Γ -- all persistent deposits in place
      ────────────────────────────────────────────────────────────
      Γ —[ advertise⦅ ad ⦆ ]→ ` ad ∣ Γ


  [C-AuthCommit] : let open ∣AD ad in
    ∀ {secrets : List (Secret × Maybe ℕ)} →

    let (as , ms) = unzip secrets
        Δ         = || map (uncurry ⟨ A ∶_♯_⟩) secrets
    in

    ∙ as ≡ secretsOfᵖ A G         -- a₁..aₖ secrets of A in G
    ∙ All (_∉ secretsOfᶜᶠ A Γ) as -- ∀i ∈ 1..k : ∄N : {A : aᵢ ♯ N} ∈ Γ
    ∙ (A ∈ Hon → All Is-just ms)  -- honest participants commit to valid lengths
      ──────────────────────────────────────────────────────────────────────────
      ` ad ∣ Γ
        —[ auth-commit⦅ A , ad , secrets ⦆ ]→
      ` ad ∣ Γ ∣ Δ ∣ A auth[ ♯▷ ad ]


  [C-AuthInit] : let open ∣AD ad in

    ∙ partG ⊆ committedParticipants ad Γ -- all participants have committed their secrets
    ∙ (A , v , x) ∈ persistentDeposits G -- G = A :! v @ x | ...
      ───────────────────────────────────────────────────────────────────────────────────
      ` ad ∣ Γ
        —[ auth-init⦅ A , ad , x ⦆ ]→
      ` ad ∣ Γ ∣ A auth[ x ▷ˢ ad ]


  [C-Init] : let open ∣AD ad in

    -- all participants have committed their secrets (guaranteed from [C-AuthInit])

    let toSpend = persistentDeposits G
        vs      = map select₂ toSpend
        xs      = map select₃ toSpend
    in

    x ∉ xs ++ ids Γ -- x fresh
    ──────────────────────────────────────────────────────────────────────────────
    ` ad
    ∣ Γ
    ∣ || map (λ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ ad ]) toSpend
    ∣ || map _auth[ ♯▷ ad ] partG
      —[ init⦅ G , C ⦆ ]→
    ⟨ C , sum vs ⟩at x ∣ Γ

  ---------------------------------------------------
  -- iii) Rules for executing active contracts

  [C-Split] :
    ∀ {vcis : VIContracts} →

    let (vs , cs , ys) = unzip₃ vcis in

    All (_∉ y ∷ ids Γ) ys -- ys fresh
    ──────────────────────────────────────────
    ⟨ [ split (zip vs cs) ] , sum vs ⟩at y ∣ Γ
      —[ split⦅ y ⦆ ]→
    || map (uncurry₃ $ flip ⟨_,_⟩at_) vcis ∣ Γ


  [C-AuthRev] :

    ─────────────────────────
    ⟨ A ∶ a ♯ just n ⟩ ∣ Γ
      —[ auth-rev⦅ A , a ⦆ ]→
    A ∶ a ♯ n ∣ Γ


  [C-PutRev] :
    ∀ {ds : DepositRefs}
      {ss : List (Participant × Secret × ℕ)} →

    let (_ , vs , xs) = unzip₃ ds
        (_ , as , _)  = unzip₃ ss
        Γ = || map (uncurry₃ ⟨_has_⟩at_) ds
        Δ = || map (uncurry₃ _∶_♯_) ss
        ΔΓ′ = Δ ∣ Γ′
    in

    ∙ z ∉ y ∷ ids (Γ ∣ ΔΓ′) -- z fresh
    ∙ ⟦ p ⟧ᵖ Δ ≡ just true -- predicate is true
      ──────────────────────────────────────────────────────
      ⟨ [ put xs &reveal as if p ⇒ c ] , v ⟩at y ∣ (Γ ∣ ΔΓ′)
        —[ put⦅ xs , as , y ⦆ ]→
      ⟨ c , v + sum vs ⟩at z ∣ ΔΓ′


  [C-Withdraw] :

    x ∉ y ∷ ids Γ -- x fresh
    ──────────────────────────────
    ⟨ [ withdraw A ] , v ⟩at y ∣ Γ
      —[ withdraw⦅ A , v , y ⦆ ]→
    ⟨ A has v ⟩at x ∣ Γ


  [C-AuthControl] :
    ∀ {i : Index c} → let d = c ‼ i in

    A ∈ authDecorations d -- D ≡ A : D′
    ───────────────────────────────────
    ⟨ c , v ⟩at x ∣ Γ
      —[ auth-control⦅ A , x ▷ d ⦆ ]→
    ⟨ c , v ⟩at x ∣ A auth[ x ▷ d ] ∣ Γ


  -- T0D0 linearize, i.e. introduce new label and produce intermediate configuration:
  -- ⟨ c , v ⟩at x ∣ Δ ∣ Γ —[ choice⦅ c , i ⦆ ]→ ⟨ [ d∗ ] , v ⟩at x ∣ Γ
  [C-Control] :
    ∀ {i : Index c} → let open ∣SELECT c i in

    ∙ ¬Null (authDecorations d) ⊎ (length c > 1)
    ∙ Γ ≈ L
    ∙ ⟨ [ d∗ ] , v ⟩at x ∣ L —[ α ]→ Γ′ -- T0D0 replace with _—↠_?
    ∙ cv α ≡ just x
      ───────────────────────────────────────────────────────────────────
      ⟨ c , v ⟩at x ∣ || map _auth[ x ▷ d ] (nub $ authDecorations d) ∣ Γ
        —[ α ]→
      Γ′


-------------------------------------------
-- Semantic rules for timed configurations.

infix 3 _≈ₜ_
_≈ₜ_ : Cfgᵗ → Cfgᵗ → Type
c ≈ₜ c′ = (time c ≡ time c′) × (cfg c ≈ cfg c′)

infix -1 _—[_]→ₜ_
data _—[_]→ₜ_ : Cfgᵗ → Label → Cfgᵗ → Type where

  -- iv) Rules for handling time
  [Action] :

    ∙ Γ —[ α ]→ Γ′
    ∙ cv α ≡ nothing
      ───────────────────────
      Γ at t —[ α ]→ₜ Γ′ at t


  [Delay] :

    δ > 0
    ─────────────────────────────────────
    Γ at t —[ delay⦅ δ ⦆ ]→ₜ Γ at (t + δ)


  [Timeout] :
    ∀ {i : Index c} → let open ∣SELECT c i; As , ts = decorations d in

    ∙ Null As                           -- no authorizations required to pick branch
    ∙ All (_≤ t) ts                     -- all time constraints are satisfied
    ∙ ⟨ [ d∗ ] , v ⟩at x ∣ Γ —[ α ]→ Γ′ -- resulting state if we pick branch
    ∙ cv α ≡ just x
      ──────────────────────────────────────────────────────────────────────────────
      (⟨ c , v ⟩at x ∣ Γ) at t —[ α ]→ₜ Γ′ at t


_—[_]↛_ : Cfg → Label → Cfg → Type
Γ —[ α ]↛ Γ′ = ¬ (Γ —[ α ]→ Γ′)

_—[_]↛ₜ_ : Cfgᵗ → Label → Cfgᵗ → Type
Γₜ —[ α ]↛ₜ Γₜ′ = ¬ (Γₜ —[ α ]→ₜ Γₜ′)

-----------------------------------------------------------------------------------
-- Derive the reflexive transitive closure for of _—→_ and _—→ₜ_.

open import Prelude.Closures
open UpToLabelledReflexiveTransitiveClosure _—[_]→_ public
open UpToLabelledReflexiveTransitiveClosure _—[_]→ₜ_ public
  renaming ( begin_ to beginₜ_; _∎ to _∎ₜ
           ; _—→⟨_⟩_⊢_ to _—→ₜ⟨_⟩_⊢_; _—→⟨_⟩_ to _—→ₜ⟨_⟩_; _`—→⟨_⟩_⊢_ to _`—→ₜ⟨_⟩_⊢_
           ; _—→_ to _—→ₜ_
           ; _—[_]↠_ to _—[_]↠ₜ_; _—↠_ to _—↠ₜ_
           ; _—[_]↠⁺_ to _—[_]↠⁺ₜ_; _—↠⁺_ to _—↠⁺ₜ_
           ; _⟨_⟩←—_⊢_ to _⟨_⟩←—ₜ_⊢_; _⟨_⟩←—_ to _⟨_⟩←—ₜ_; _`⟨_⟩←—_⊢_ to _`⟨_⟩←—ₜ_⊢_
           ; _←[_]—_ to _←[_]—ₜ_; _←—_ to _←—ₜ_
           ; _↞[_]—_ to _↞[_]—ₜ_; _↞—_ to _↞—ₜ_
           ; _⁺↞[_]—_ to _⁺↞[_]—ₜ_; _⁺↞—_ to _⁺↞—ₜ_
           ; viewLeft to viewLeftₜ; viewRight to viewRightₜ; view↔ to view↔ₜ
           )
