open import Prelude.Init; open SetAsType
open import Prelude.Maybes
open import Prelude.Lists
open import Prelude.Membership
open import Prelude.DecEq
open import Prelude.Nary hiding (⟦_⟧)
open import Prelude.Ord
open import Prelude.General
open import Prelude.InferenceRules
open import Prelude.Split renaming (split to mkSplit)

open import BitML.BasicTypes
open import BitML.Predicate hiding (`; ∣_∣)

module BitML.Semantics.RuleMatching (⋯ : ⋯) (let open ⋯ ⋯) where

open import BitML.Contracts ⋯ hiding (d)
open import BitML.Semantics.Action ⋯
open import BitML.Semantics.Configurations.Types ⋯
open import BitML.Semantics.Configurations.Helpers ⋯
open import BitML.Semantics.Label ⋯
open import BitML.Semantics.Predicate ⋯
open import BitML.Semantics.InferenceRules ⋯


-- ** types of steps

isControl isWithdraw isPut isSplit : Pred₀ (Γ —[ α ]→ Γ′)
isControl = λ where
  ([C-Control] _ _ _ _) → ⊤
  _ → ⊥
isWithdraw = λ where
  ([C-Withdraw] _) → ⊤
  _ → ⊥
isPut = λ where
  ([C-PutRev] _ _) → ⊤
  _ → ⊥
isSplit = λ where
  ([C-Split] _) → ⊤
  _ → ⊥

isAction isDelay isTimeout : Pred₀ (Γₜ —[ α ]→ₜ Γₜ′)
isDelay = λ where
  ([Delay] _) → ⊤
  _ → ⊥
isAction = λ where
  ([Action] _ _) → ⊤
  _ → ⊥
isTimeout = λ where
  ([Timeout] _ _ _ _) → ⊤
  _ → ⊥

isWithdraw⇒¬isControl : ∀ (st : Γ —[ α ]→ Γ′) → isWithdraw st → ¬ isControl st
isWithdraw⇒¬isControl ([C-Withdraw] _) tt ()

isPut⇒¬isControl : ∀ (st : Γ —[ α ]→ Γ′) → isPut st → ¬ isControl st
isPut⇒¬isControl ([C-PutRev] _ _) tt ()

isSplit⇒¬isControl : ∀ (st : Γ —[ α ]→ Γ′) → isSplit st → ¬ isControl st
isSplit⇒¬isControl ([C-Split] _) tt ()

isControl⇒cv≡ : ∀ (st : Γ —[ α ]→ Γ′) → {isControl st} → Is-just (cv α)
isControl⇒cv≡ ([C-Control] _ _ _ cv≡) = mk-Is-just cv≡

cv≡⇒st :
  ∀ (st : Γ —[ α ]→ Γ′) →
  ∙ Is-just (cv α)
    ─────────────────
    isWithdraw st
  ⊎ isPut st
  ⊎ isSplit st
  ⊎ isControl st
cv≡⇒st ([C-Withdraw] _) _ = inj₁ tt
cv≡⇒st ([C-PutRev] _ _) _ = inj₂ $ inj₁ tt
cv≡⇒st ([C-Split] _) _ = inj₂ $ inj₂ $ inj₁ tt
cv≡⇒st ([C-Control] _ _ _ _) _ = inj₂ $ inj₂ $ inj₂ tt

¬delay : ¬ (Γ —[ delay⦅ δ ⦆ ]→ Γ′)
¬delay ([C-Control] _ _ _ ())

-- ** extracting inner subexpressions from a rule

innerL : (st : Γ —[ α ]→ Γ′) → {isControl st} → Cfg
innerL ([C-Control] {c}{L = L}{v}{x} {i = i} _ _ _ _) =
  ⟨ [ removeTopDecorations (c ‼ i) ] , v ⟩at x ∣ L

innerStep : (st : Γ —[ α ]→ Γ′) → {p : isControl st} → innerL st {p} —[ α ]→ Γ′
innerStep ([C-Control] _ _ L→ _) = L→

innerCI : (st : Γ —[ α ]→ Γ′) → {isControl st} → ∃ λ (c : Contract) → Index c
innerCI ([C-Control] {c = c} {i = i} _ _ _ _) = c , i

innerLₜ : (stₜ : Γₜ —[ α ]→ₜ Γₜ′) → {isTimeout stₜ} → Cfg
innerLₜ ([Timeout] {c = c} {v = v} {x = x} {Γ = Γ} {i = i} _ _ _ _) =
  ⟨ [ removeTopDecorations (c ‼ i) ] , v ⟩at x ∣ Γ

innerStepₜ : (stₜ : Γₜ —[ α ]→ₜ (Γ′ at t′)) → {p : isTimeout stₜ} →
  innerLₜ stₜ {p} —[ α ]→ Γ′
innerStepₜ ([Timeout] _ _ Γ→ _) = Γ→

innerCIₜ : (stₜ : Γₜ —[ α ]→ₜ Γₜ′) → {isTimeout stₜ} → ∃ λ (c : Contract) → Index c
innerCIₜ ([Timeout] {c = c} {i = i} _ _ _ _) = c , i

innerDₜ : (stₜ : Γₜ —[ α ]→ₜ Γₜ′) → {isTimeout stₜ} → Branch
innerDₜ st {isT} = let c , i = innerCIₜ st {isT}; open ∣SELECT c i in d

innerVₜ : (stₜ : Γₜ —[ α ]→ₜ Γₜ′) → {isTimeout stₜ} → Value
innerVₜ ([Timeout] {v = v} _ _ _ _) = v

innerXₜ : (stₜ : Γₜ —[ α ]→ₜ Γₜ′) → {isTimeout stₜ} → Id
innerXₜ ([Timeout] {x = x} _ _ _ _) = x

innerΓₜ : (stₜ : Γₜ —[ α ]→ₜ Γₜ′) → {isTimeout stₜ} → Cfg
innerΓₜ ([Timeout] {Γ = Γ} _ _ _ _) = Γ

-- ** splitting a step into source and target configuration
instance
  Split-step : (Γ —[ α ]→ Γ′) -splitsInto- Cfg
  Split-step {Γ = Γ} {Γ′ = Γ′} .mkSplit _ = Γ , Γ′

  Split-stepₜ : (Γₜ —[ α ]→ₜ Γₜ′) -splitsInto- Cfgᵗ
  Split-stepₜ {Γₜ = Γₜ} {Γₜ′ = Γₜ′} .mkSplit _ = Γₜ , Γₜ′

isControl⇒IsComposite :
  ∀ (st : Γ —[ α ]→ Γ′) →
  ∙ isControl st
    ──────────────────────
    IsComposite (st ∙left)
isControl⇒IsComposite ([C-Control] _ _ _ _) tt = tt

timeout∙left-base :
  ∀ (stₜ : Γₜ —[ α ]→ₜ Γₜ′) →
  ∀ (isT : isTimeout stₜ) →
  let st = innerStepₜ stₜ {isT} in
  ∀ (isC : isControl st) →
  ────────────────────────────────────────────────────────
  IsBase $ (st ∙left , isControl⇒IsComposite st isC) ∙left
timeout∙left-base ([Timeout] _ _ _ _) tt isC = tt

control∙left-composite :
  ∀ (st : Γ —[ α ]→ Γ′) →
  ∀ (isC : isControl st) →
    ────────────────────────────────────────────────────────────
    IsComposite $ (st ∙left , isControl⇒IsComposite st isC) ∙left
control∙left-composite ([C-Control] _ _ _ _) tt = tt

timeout⇒¬control :
  ∀ (stₜ : Γₜ —[ α ]→ₜ Γₜ′) →
  ∀ (p : isTimeout stₜ) →
    ────────────────────────────────
    ¬ isControl (innerStepₜ stₜ {p})
timeout⇒¬control stₜ@([Timeout] _ _ Γ→ _) isT@tt isC =
  ¬base×composite
    ((Γ→ ∙left , isControl⇒IsComposite Γ→ isC) ∙left)
    ( timeout∙left-base stₜ isT isC
    , control∙left-composite Γ→ isC )

-- **

match-withdraw :
  ∀ (step : Γ —[ withdraw⦅ A , v , y ⦆ ]→ Γ′) →
  ∙ ¬ isControl step
    ───────────────────────────────────────────
  ∃ λ Γ₀ → ∃ λ x →
    (Γ  ≡ ⟨ [ withdraw A ] , v ⟩at y ∣ Γ₀)
  × (Γ′ ≡ ⟨ A has v ⟩at x ∣ Γ₀)
  × (x ∉ y L.∷ ids Γ₀)
match-withdraw ([C-Withdraw] x∉) _ = -, -, refl , refl , x∉
match-withdraw ([C-Control] _ _ _ _) ¬ctrl = ⊥-elim $ ¬ctrl tt

match-put :
  ∀ (step : Γ —[ put⦅ xs , as , y ⦆ ]→ Γ′) →
  ∙ ¬ isControl step
    ───────────────────────────────────────────
  ∃ λ ds → ∃ λ ss → ∃ λ p → ∃ λ c → ∃ λ v → ∃ λ Γ₀ → ∃ λ z →
  let (_ , vs , _xs) = unzip₃ ds
      (_ , _as , _)  = unzip₃ ss
      _Γ = || map (uncurry₃ ⟨_has_⟩at_) ds
      Δ = || map (uncurry₃ _∶_♯_) ss
      ΔΓ′ = Δ ∣ Γ₀
  in (Γ  ≡ ⟨ [ put xs &reveal as if p ⇒ c ] , v ⟩at y ∣ (_Γ ∣ ΔΓ′))
   × (Γ′ ≡ ⟨ c , v + sum vs ⟩at z ∣ ΔΓ′)
   × (xs ≡ _xs)
   × (as ≡ _as)
   × (z ∉ y L.∷ ids (_Γ ∣ ΔΓ′))
   × (⟦ p ⟧ Δ ≡ just true)
match-put ([C-PutRev] {ds = ds}{ss} fresh-z p≡) _ =
  ds , ss , -, -, -, -, -, refl , refl , refl , refl , fresh-z , p≡
match-put ([C-Control] _ _ _ _) ¬ctrl = ⊥-elim $ ¬ctrl tt

match-split :
  ∀ (step : Γ —[ split⦅ y ⦆ ]→ Γ′) →
  ∙ ¬ isControl step
    ───────────────────────────────────────────
  ∃ λ vcis → ∃ λ Γ₀ → ∃ λ y →
  let vs , cs , ys = unzip₃ vcis
  in (Γ  ≡ ⟨ [ split (zip vs cs) ] , sum vs ⟩at y ∣ Γ₀)
   × (Γ′ ≡ || map (uncurry₃ $ flip ⟨_,_⟩at_) vcis ∣ Γ₀)
   × All (_∉ y L.∷ ids Γ₀) ys
match-split ([C-Split] {vcis = vcis} fresh-ys) _ =
  vcis , -, -, refl , refl , fresh-ys
match-split ([C-Control] _ _ _ _) ¬ctrl = ⊥-elim $ ¬ctrl tt

match-authDestroy : ∀ {j′ : Index xs} →
  Γ —[ auth-destroy⦅ A , xs , j′ ⦆ ]→ Γ′
  ───────────────────────────────────────────
  ∃ λ ds → ∃ λ Γ₀ → ∃ λ y → ∃ λ (j : Index ds) →
  let _xs = map select₃ ds
      _Aⱼ = proj₁ (ds ‼ j)
      _j′ = ‼-map {xs = ds} j
      Δ  = || map (uncurry₃ ⟨_has_⟩at_) ds
  in (Γ  ≡ Δ ∣ Γ₀)
   × (Γ′ ≡ Δ ∣ _Aⱼ auth[ _xs , _j′ ▷ᵈˢ y ] ∣ Γ₀)
   × (A ≡ _Aⱼ)
   × ∃ λ (xs≡ : xs ≡ _xs)
   → (j′ ≡ subst Index (sym xs≡) _j′)
   × (y ∉ ids Γ₀)
match-authDestroy ([DEP-AuthDestroy] {Γ = Γ₀} {ds = ds}{j} fresh-y) =
  ds , -, -, j , refl , refl , refl , refl , refl , fresh-y

⟨⟩∘∣-injective : ∀ {d d′} →
  ⟨ [ d ] , v ⟩at x ∣ Γ ≡ ⟨ [ d′ ] , v′ ⟩at x′ ∣ Γ′
  ─────────────────────────────────────────────────
  (d ≡ d′) × (v ≡ v′) × (x ≡ x′) × (Γ ≡ Γ′)
⟨⟩∘∣-injective refl = refl , refl , refl , refl

match-withdrawₜ :
  ∀ (stepₜ : Γ at t —[ withdraw⦅ A , v , y ⦆ ]→ₜ Γ′ at t) →
  ∀ (isT : isTimeout stepₜ) →
    ────────────────────────────────────────────────────────
  let d = innerDₜ stepₜ {isT} in
  ∃ λ Γ₀ → ∃ λ x →
    (d ≡⋯∶ withdraw A)
  × (innerVₜ stepₜ {isT} ≡ v)
  × (innerXₜ stepₜ {isT} ≡ y)
  × (innerΓₜ stepₜ {isT} ≡ Γ₀)
  × (Γ′ ≡ ⟨ A has v ⟩at x ∣ Γ₀)
  × (x ∉ y L.∷ ids Γ₀)
match-withdrawₜ stepₜ@([Timeout] {c = c} {i = i} As≡∅ ∀t≤ Γ→ refl) tt
  with Γ₀ , x , Γ≡ , ⋯⋯ ← match-withdraw Γ→ (timeout⇒¬control stepₜ tt)
  with d≡ , v≡ , x≡ , Γ≡′ ← ⟨⟩∘∣-injective Γ≡
  = Γ₀ , x , d≡ , v≡ , x≡ , Γ≡′ , ⋯⋯

match-putₜ :
  ∀ (stepₜ : Γ at t —[ put⦅ xs , as , y ⦆ ]→ₜ Γ′ at t) →
  ∀ (isT : isTimeout stepₜ) →
    ────────────────────────────────────────────────────────
  let d = innerDₜ stepₜ {isT} in
  ∃ λ ds → ∃ λ ss → ∃ λ p → ∃ λ c → ∃ λ v → ∃ λ Γ₀ → ∃ λ z →
  let (_ , vs , _xs) = unzip₃ ds
      (_ , _as , _)  = unzip₃ ss
      _Γ = || map (uncurry₃ ⟨_has_⟩at_) ds
      Δ = || map (uncurry₃ _∶_♯_) ss
      ΔΓ′ = Δ ∣ Γ₀
  in
    (d ≡⋯∶ put xs &reveal as if p ⇒ c)
  × (innerVₜ stepₜ {isT} ≡ v)
  × (innerXₜ stepₜ {isT} ≡ y)
  × (innerΓₜ stepₜ {isT} ≡ (_Γ ∣ ΔΓ′))
  × (Γ′ ≡ ⟨ c , v + sum vs ⟩at z ∣ ΔΓ′)
  × (xs ≡ _xs)
  × (as ≡ _as)
  × (z ∉ y L.∷ ids (_Γ ∣ ΔΓ′))
  × (⟦ p ⟧ Δ ≡ just true)
match-putₜ stepₜ@([Timeout] {c = c} {i = i} As≡∅ ∀t≤ Γ→ refl) tt
  with ds , ss , p , c , v , Γ₀ , z , Γ≡ , ⋯⋯ ← match-put Γ→ (timeout⇒¬control stepₜ tt)
  with d≡ , v≡ , x≡ , Γ≡′ ← ⟨⟩∘∣-injective Γ≡
  = ds , ss , p , c , v , Γ₀ , z , d≡ , v≡ , x≡ , Γ≡′ , ⋯⋯

match-splitₜ :
  ∀ (stepₜ : Γ at t —[ split⦅ y ⦆ ]→ₜ Γ′ at t) →
  ∀ (isT : isTimeout stepₜ) →
    ────────────────────────────────────────────────────────
  let d = innerDₜ stepₜ {isT} in
  ∃ λ vcis → ∃ λ Γ₀ → ∃ λ y →
  let vs , cs , ys = unzip₃ vcis in
    (d ≡⋯∶ split (zip vs cs))
  × (innerVₜ stepₜ {isT} ≡ sum vs)
  × (innerXₜ stepₜ {isT} ≡ y)
  × (innerΓₜ stepₜ {isT} ≡ Γ₀)
  × (Γ′ ≡ || map (uncurry₃ $ flip ⟨_,_⟩at_) vcis ∣ Γ₀)
  × All (_∉ y L.∷ ids Γ₀) ys
match-splitₜ stepₜ@([Timeout] {c = c} {i = i} _ _ Γ→ refl) tt
  with vcis , Γ₀ , y , Γ≡ , ⋯⋯ ← match-split Γ→ (timeout⇒¬control stepₜ tt)
  with d≡ , v≡ , x≡ , Γ≡′ ← ⟨⟩∘∣-injective Γ≡
  = vcis , Γ₀ , y , d≡ , v≡ , x≡ , Γ≡′ , ⋯⋯

-- T0D0: complete view that is convenient for analysis
