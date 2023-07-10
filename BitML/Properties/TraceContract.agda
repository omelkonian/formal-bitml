open import Prelude.Init; open SetAsType
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Membership
open L.Mem using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺)
open import Prelude.Bifunctor
open import Prelude.Nary hiding (⟦_⟧)
open import Prelude.Lists
open import Prelude.Lists.Dec
open import Prelude.Validity
open import Prelude.Setoid
open import Prelude.General hiding (_⊢_)
open import Prelude.ToN
open import Prelude.Traces
open import Prelude.InferenceRules

open import BitML.BasicTypes

module BitML.Properties.TraceContract (⋯ : ⋯) (let open ⋯ ⋯) where

open import BitML.Predicate using (p)
open import BitML.Contracts ⋯ hiding (d)
open import BitML.Semantics ⋯
open import BitML.Properties.Helpers ⋯
open import BitML.Properties.TraceInit ⋯

-- ℍ[Contract]⦅ Γ —[ α ]↝ Γ′ ⦆⦅ c ⦆: Contract `c` is created by a transition `Γ —[ α ]→ Γ′`
data ℍ[Contract]⦅_—[_]↝_⦆⦅_⦆ : Cfg → Label → Cfg → Contract → Type where

  base :

      ` (⟨ g ⟩ c) ∈ᶜ Γ
    → Γ —[ init⦅ g , c ⦆ ]→ Γ′
      ───────────────────────────────────────────────────
      ℍ[Contract]⦅ Γ —[ init⦅ g , c ⦆ ]↝ Γ′ ⦆⦅ c ⦆

  step-put :

    ──────────────────────────────────────────────────────────────────────────────────────────────────────
    ℍ[Contract]⦅ ⟨ [ put xs &reveal as if p ⇒ c ] , v ⟩at y ∣ Γ —[ put⦅ xs , as , y ⦆ ]↝ Γ′ ⦆⦅ c ⦆

  step-split :

    c ∈ map proj₂ vcs
    ─────────────────────────────────────────────────────────────────────────
    ℍ[Contract]⦅ ⟨ [ split vcs ] , v ⟩at y ∣ Γ —[ split⦅ y ⦆ ]↝ Γ′ ⦆⦅ c ⦆

  step-control : ∀ {i : Index c′} → let open ∣SELECT c′ i in

      Γ ≈ L
    → cv α ≡ just x
    → ℍ[Contract]⦅ ⟨ [ d∗ ] , v ⟩at x ∣ L —[ α ]↝ Γ′ ⦆⦅ c ⦆
      ───────────────────────────────────────────────────────────────────────────────────────
      ℍ[Contract]⦅ ⟨ c′ , v ⟩at x ∣ || map _auth[ x ▷ d ] (nub $ authDecorations d) ∣ Γ
                   —[ α ]↝ Γ′ ⦆⦅ c ⦆

  step-timeout : ∀ {i : Index c′} → let open ∣SELECT c′ i in
      cv α ≡ just x
    → ℍ[Contract]⦅ ⟨ [ d∗ ] , v ⟩at x ∣ Γ —[ α ]↝ Γ′ ⦆⦅ c ⦆
      ────────────────────────────────────────────────────────
      ℍ[Contract]⦅ ⟨ c′ , v ⟩at x ∣ Γ —[ α ]↝ Γ′ ⦆⦅ c ⦆

open import BitML.Contracts ⋯ using (d)

d∗≢auth : removeTopDecorations d ≢ A ⇒ d′
d∗≢auth {_ ⇒ d}       eq = d∗≢auth {d} eq
d∗≢auth {after _ ⇒ d} eq = d∗≢auth {d} eq

d∗≢time : removeTopDecorations d ≢ after t ⇒ d′
d∗≢time {_ ⇒ d}       eq = d∗≢time {d} eq
d∗≢time {after _ ⇒ d} eq = d∗≢time {d} eq

private
  ¬AuthControl :
      ⟨ c , v ⟩at x ∉ᶜ Γ
    → Γ —[ auth-control⦅ A , x′ ▷ d ⦆ ]→ Γ′
      ────────────────────────────────────
      ⟨ c , v ⟩at x ∉ᶜ Γ′
  ¬AuthControl c∉ ([C-AuthControl] {c}{A}{v}{x}{Γ}{i} _) =
    let d = c ‼ i in
    ∈-++⁻ (cfgToList $ ⟨ c , v ⟩at x ∣ A auth[ x ▷ d ]) >≡>
    Sum.[ (λ{ (here refl) → ⊥-elim $ c∉ (here refl); (there (here ())) })
        , c∉ ∘ ∈-++⁺ʳ [ ⟨ c , v ⟩at x ]
        ]

  ¬AuthRev :
      ⟨ c , v ⟩at x ∉ᶜ Γ
    → Γ —[ auth-rev⦅ A , a ⦆ ]→ Γ′
      ────────────────────────────
      ⟨ c , v ⟩at x ∉ᶜ Γ′
  ¬AuthRev c∉ ([C-AuthRev] {A}{a}{n}{Γ}) =
    ∈-++⁻ [ A ∶ a ♯ n ] >≡>
    Sum.[ (λ{ (here ()) })
        , c∉ ∘ ∈-++⁺ʳ [ ⟨ A ∶ a ♯ just n ⟩ ]
        ]

  ¬AuthJoin :
      ⟨ c , v ⟩at y ∉ᶜ Γ
    → Γ —[ auth-join⦅ B , x ↔ y′ ⦆ ]→ Γ′
      --————————————————————————————————————
    → ⟨ c , v ⟩at y ∉ᶜ Γ′
  ¬AuthJoin c∉ ([DEP-AuthJoin] {A}{v}{x}{v′}{y}{Γ}) c∈
    with ∈-++⁻ (cfgToList $ ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at y ∣ A auth[ x ↔ y ▷⟨ A , v + v′ ⟩ ]) c∈
  ... | inj₁ c∈ˡ = contradict c∈ˡ
  ... | inj₂ c∈Γ = c∉ $ ∈-++⁺ʳ
    (cfgToList $ ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at y) c∈Γ


  ¬Join :
      ⟨ c , v ⟩at x ∉ᶜ Γ
    → Γ —[ join⦅ x′ ↔ y ⦆ ]→ Γ′
      --————————————————————————————————————
    → ⟨ c , v ⟩at x ∉ᶜ Γ′
  ¬Join c∉ ([DEP-Join] {z}{x}{y}{Γ}{A}{v}{v′} _) c∈
    with ∈-++⁻ [ ⟨ A has v + v′ ⟩at z ] c∈
  ... | inj₁ (here ())
  ... | inj₂ c∈Γ = c∉ $ ∈-++⁺ʳ (cfgToList $ ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at y ∣ A auth[ x ↔ y ▷⟨ A , v + v′ ⟩ ]) c∈Γ

  ¬AuthDivide :
      ⟨ c , v ⟩at x ∉ᶜ Γ
    → Γ —[ auth-divide⦅ A , x′ ▷ v″ , v′ ⦆ ]→ Γ′
      --————————————————————————————————————
    → ⟨ c , v ⟩at x ∉ᶜ Γ′
  ¬AuthDivide c∉ ([DEP-AuthDivide] {A}{v}{v′}{x}{Γ}) c∈
    with ∈-++⁻ (cfgToList $ ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ]) c∈
  ... | inj₁ c∈ˡ = case c∈ˡ of λ where
    (here ())
    (there (here ()))
  ... | inj₂ c∈Γ = c∉ $ ∈-++⁺ʳ (cfgToList $ ⟨ A has (v + v′) ⟩at x) c∈Γ

  ¬Divide :
      ⟨ c , v ⟩at x ∉ᶜ Γ
    → Γ —[ divide⦅ x′ ▷ v″ , v′ ⦆ ]→ Γ′
      --————————————————————————————————————
    → ⟨ c , v ⟩at x ∉ᶜ Γ′
  ¬Divide c∉ ([DEP-Divide] {x}{Γ}{y}{y′}{A}{v}{v′} _) c∈
    with ∈-++⁻ (cfgToList $ ⟨ A has v ⟩at y ∣ ⟨ A has v′ ⟩at y′) c∈
  ... | inj₁ c∈ˡ = case c∈ˡ of λ where
    (here ())
    (there (here ()))
  ... | inj₂ c∈Γ = c∉ $ ∈-++⁺ʳ (cfgToList $ ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ]) c∈Γ

  ¬AuthDonate :
      ⟨ c , v ⟩at x ∉ᶜ Γ
    → Γ —[ auth-donate⦅ A , x′ ▷ᵈ B ⦆ ]→ Γ′
      --————————————————————————————————————
    → ⟨ c , v ⟩at x ∉ᶜ Γ′
  ¬AuthDonate c∉ ([DEP-AuthDonate] {A}{v}{x}{Γ}{B}) =
    ∈-++⁻ (cfgToList $ ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B ]) >≡>
    Sum.[ (λ{ (here ()); (there (here ())) })
        , c∉ ∘ ∈-++⁺ʳ [ ⟨ A has v ⟩at x ]
        ]

  ¬Donate :
      ⟨ c , v ⟩at x ∉ᶜ Γ
    → Γ —[ donate⦅ x′ ▷ᵈ B ⦆ ]→ Γ′
      --————————————————————————————————————
    → ⟨ c , v ⟩at x ∉ᶜ Γ′
  ¬Donate c∉ ([DEP-Donate] {y}{x}{Γ}{A}{v}{B} _) =
    ∈-++⁻ [ ⟨ B has v ⟩at y ] >≡>
    Sum.[ (λ{ (here ()) })
        , c∉ ∘ ∈-++⁺ʳ (cfgToList $ ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B ])
        ]

  ¬AuthDestroy : ∀ {xs} {j′ : Index xs}
    → ⟨ c , v ⟩at x ∉ᶜ Γ
    → Γ —[ auth-destroy⦅ A , xs , j′ ⦆ ]→ Γ′
      --————————————————————————————————————
    → ⟨ c , v ⟩at x ∉ᶜ Γ′
  ¬AuthDestroy c∉ ([DEP-AuthDestroy] {y}{Γ}{ds}{j} _) =
    let xs = map select₃ ds
        Aj = proj₁ (ds ‼ j)
        j′ = ‼-map {xs = ds} j
        Δ  = || map (uncurry₃ ⟨_has_⟩at_) ds
    in
    ∈ᶜ-++⁻ (Δ ∣ Aj auth[ xs , j′ ▷ᵈˢ y ]) Γ >≡>
    Sum.[ (∈ᶜ-++⁻ Δ (Aj auth[ xs , j′ ▷ᵈˢ y ]) >≡>
          Sum.[ c∉ ∘ ∈ᶜ-++⁺ˡ Δ Γ
              , (λ{ (here ()) })
              ])
        , c∉ ∘ ∈ᶜ-++⁺ʳ Δ Γ
        ]

  ¬Destroy :
      ⟨ c , v ⟩at x ∉ᶜ Γ
    → Γ —[ destroy⦅ xs ⦆ ]→ Γ′
      --————————————————————————————————————
    → ⟨ c , v ⟩at x ∉ᶜ Γ′
  ¬Destroy c∉ ([DEP-Destroy] {y}{Γ}{ds}) =
    let xs = map select₃ ds
        Δ  = || map (λ{ (i , Ai , vi , xi) → ⟨ Ai has vi ⟩at xi ∣ Ai auth[ xs , ‼-map {xs = ds} i ▷ᵈˢ y ] })
                    (enumerate ds)
    in c∉ ∘ ∈ᶜ-++⁺ʳ Δ Γ

  ¬Advertise :
      ⟨ c , v ⟩at x ∉ᶜ Γ
    → Γ —[ advertise⦅ ad ⦆ ]→ Γ′
      --————————————————————————————————————
    → ⟨ c , v ⟩at x ∉ᶜ Γ′
  ¬Advertise {ad = ad} c∉ ([C-Advertise] {ad = .ad}{Γ} vad hon⁺ d⊆) =
    ∈ᶜ-++⁻ (` ad) Γ >≡>
    Sum.[ contradict
        , c∉
        ]

  ¬AuthCommit : ∀ {secrets : List (Secret × Maybe ℕ)}
    → ⟨ c , v ⟩at x ∉ᶜ Γ
    → Γ —[ auth-commit⦅ A , ad , secrets ⦆ ]→ Γ′
      --————————————————————————————————————
    → ⟨ c , v ⟩at x ∉ᶜ Γ′
  ¬AuthCommit c∉ ([C-AuthCommit] {ad}{A}{Γ}{secrets} _ _ _) =
    let (as , ms) = unzip secrets
        Δ         = || map (uncurry ⟨ A ∶_♯_⟩) secrets
    in
    ∈ᶜ-++⁻ (` ad ∣ Γ ∣ Δ) (A auth[ ♯▷ ad ]) >≡>
    Sum.[ ∈ᶜ-++⁻ (` ad ∣ Γ) Δ >≡>
          Sum.[ c∉
              , ∉ᶜ-|| {f = uncurry ⟨ A ∶_♯_⟩} (λ{ (here ()); (there ())}) secrets
              ]
        , (λ{ (here ()) })
        ]

  ¬AuthInit :
      ⟨ c , v ⟩at x ∉ᶜ Γ
    → Γ —[ auth-init⦅ A , ad , x′ ⦆ ]→ Γ′
      --————————————————————————————————————
    → ⟨ c , v ⟩at x ∉ᶜ Γ′
  ¬AuthInit c∉ ([C-AuthInit] {ad}{Γ}{A}{x = x} _ _) =
    ∈ᶜ-++⁻ (` ad ∣ Γ) (A auth[ x ▷ˢ ad ]) >≡>
    Sum.[ c∉
        , (λ{ (here ()) })
        ]

  ¬Init :
      ⟨ c , v ⟩at x ∉ᶜ Γ
    → c ≢ c′
    → Γ —[ init⦅ g , c′ ⦆ ]→ Γ′
      --————————————————————————————————————
    → ⟨ c , v ⟩at x ∉ᶜ Γ′
  ¬Init c∉ ¬eq ([C-Init] {ad}{x}{Γ} _) = let ⟨ G ⟩ C = ad; partG = nub-participants G in
    let toSpend = persistentDeposits G
        vs      = map (proj₁ ∘ proj₂) toSpend
        Δ₁ = || map (λ{ (Ai , vi , xi) → ⟨ Ai has vi ⟩at xi ∣ Ai auth[ xi ▷ˢ ad ] }) toSpend
        Δ₂ = || map _auth[ ♯▷ ad ] partG
    in
    ∈-++⁻ [ ⟨ C , sum vs ⟩at x ] >≡>
    Sum.[ (λ{ (here refl) → ¬eq refl })
        , c∉ ∘ ∈ᶜ-++⁺ˡ (` ad ∣ Γ ∣ Δ₁) Δ₂
             ∘ ∈ᶜ-++⁺ˡ (` ad ∣ Γ) Δ₁
             ∘ ∈ᶜ-++⁺ʳ (` ad) Γ
        ]

  ¬Withdraw-helper : ∀ {i : Index c}
    → (step : ⟨ [ removeTopDecorations (c ‼ i) ] , v ⟩at x ∣ L —[ withdraw⦅ A , v′ , x ⦆ ]→ Γ′)
      --————————————————————————————
    → ∃ λ y → Γ′ ≡ ⟨ A has v′ ⟩at y ∣ L
  ¬Withdraw-helper {c}{i = i} step with removeTopDecorations (c ‼ i) | step
  ... | withdraw _ | [C-Withdraw] _ = -, refl

  ¬Withdraw :
      ⟨ c , v ⟩at x ∉ᶜ Γ
    → Γ —[ withdraw⦅ A , v′ , y ⦆ ]→ Γ′
      --————————————————————————————————————
    → ⟨ c , v ⟩at x ∉ᶜ Γ′
  ¬Withdraw c∉ ([C-Withdraw] {x}{y}{Γ}{A}{v} _) =
    ∈-++⁻ [ ⟨ A has v ⟩at x ] >≡>
    Sum.[ (λ{ (here ()) })
        , c∉ ∘ ∈-++⁺ʳ [ ⟨ [ withdraw A ] , v ⟩at y ]
        ]
  ¬Withdraw {c₀}{v₀}{x₀}
    {Γ = .(⟨ c , v ⟩at x ∣ || map _auth[ x ▷ (c ‼ i) ] (nub $ authDecorations (c ‼ i)) ∣ Γ)}
    {A}{v′}{y}
    {Γ′}
    c∉ ([C-Control] {c}{Γ}{L}{v}{x}{.(withdraw⦅ A , v′ , y ⦆)}{.Γ′}{i} p ≈L L→Γ′ refl)
    = c∉Γ′
    where
      d_ = c ‼ i
      d∗ = removeTopDecorations d_

      S₀ = ⟨ c , v ⟩at x ∣ || map _auth[ x ▷ d_ ] (nub $ authDecorations d_)
      S  = S₀ ∣ Γ
      S′ = Γ′

      c∉Γ : ⟨ c₀ , v₀ ⟩at x₀ ∉ᶜ Γ
      c∉Γ ad∈Γ = c∉ $ ∈ᶜ-++⁺ʳ S₀ Γ ad∈Γ

      c∉L : ⟨ c₀ , v₀ ⟩at x₀ ∉ᶜ L
      c∉L = ∉ᶜ-resp-≈ {Γ}{L} ≈L c∉Γ

      c∉Γ′ : ⟨ c₀ , v₀ ⟩at x₀ ∉ᶜ Γ′
      c∉Γ′ c∈
        rewrite proj₂ $ ¬Withdraw-helper {c}{v}{x}{i = i} L→Γ′
        = case c∈ of λ where
            (here ())
            (there c∈′) → c∉L c∈′

  HELP : let ⟨C,v⟩ₓ = ⟨ [ d ] , v ⟩at x in
      ⟨C,v⟩ₓ ∉ᶜ L
    → cv α ≡ just x
    → ⟨C,v⟩ₓ ∣ L —[ α ]→ Γ′
    → ⟨C,v⟩ₓ ∉ᶜ Γ′
  HELP c∉ cv≡ ([C-Split] {y}{Γ}{vcis} fresh-ys) c∈ =
    let (vs , cs , ys) = unzip₃ vcis in
    case ∈ᶜ-++⁻ (|| map (uncurry₃ $ flip ⟨_,_⟩at_) vcis) Γ c∈ of λ where
      (inj₁ c∈Δ) → L.All.lookup fresh-ys (x∈vcis⇒¬fresh {vcis = vcis} c∈Δ) (here refl)
      (inj₂ c∈Γ) → c∉ c∈Γ
  HELP c∉ cv≡ ([C-PutRev] {Γ′ = Γ′} {ds = ds}{ss} _ _) (there c∈) =
    let Γ = || map (uncurry₃ ⟨_has_⟩at_) ds
        Δ = || map (uncurry₃ _∶_♯_) ss
        ΔΓ′ = Δ ∣ Γ′
    in c∉ $ ∈ᶜ-++⁺ʳ Γ ΔΓ′ c∈
  HELP c∉ cv≡ ([C-Withdraw] _) (there c∈) = c∉ c∈

  h :
      ⟨ c , v ⟩at y ∉ᶜ Γ
    → ⟨ c , v ⟩at y ∈ᶜ Γ′
    → Γ —[ α ]→ Γ′
      --——————————————————————————————————————
    → ℍ[Contract]⦅ Γ —[ α ]↝ Γ′ ⦆⦅ c ⦆
  h {c₀}{v₀}{y₀}{Γ}{Γ′}{α = α} c∉ c∈ step
    with α | step
  ... | advertise⦅ _ ⦆               | st = ⊥-elim $ ¬Advertise c∉ st c∈
  ... | auth-join⦅ _ , _ ↔ _ ⦆       | st = ⊥-elim $ ¬AuthJoin c∉ st c∈
  ... | join⦅ _ ↔ _ ⦆                | st = ⊥-elim $ ¬Join c∉ st c∈
  ... | auth-divide⦅ _ , _ ▷ _ , _ ⦆ | st = ⊥-elim $ ¬AuthDivide c∉ st c∈
  ... | divide⦅ _ ▷ _ , _ ⦆          | st = ⊥-elim $ ¬Divide c∉ st c∈
  ... | auth-donate⦅ _ , _ ▷ᵈ _ ⦆    | st = ⊥-elim $ ¬AuthDonate c∉ st c∈
  ... | donate⦅ _ ▷ᵈ _ ⦆             | st = ⊥-elim $ ¬Donate c∉ st c∈
  ... | auth-destroy⦅ _ , _ , _ ⦆    | st = ⊥-elim $ ¬AuthDestroy c∉ st c∈
  ... | destroy⦅ _ ⦆                 | st = ⊥-elim $ ¬Destroy c∉ st c∈
  ... | auth-commit⦅ _ , _ , _ ⦆     | st = ⊥-elim $ ¬AuthCommit c∉ st c∈
  ... | auth-init⦅ _ , _ , _ ⦆       | st = ⊥-elim $ ¬AuthInit c∉ st c∈
  ... | auth-rev⦅ _ , _ ⦆            | st = ⊥-elim $ ¬AuthRev c∉ st c∈
  ... | withdraw⦅ _ , _ , _ ⦆        | st = ⊥-elim $ ¬Withdraw c∉ st c∈
  ... | auth-control⦅ _ , _ ▷ _ ⦆    | st = ⊥-elim $ ¬AuthControl c∉ st c∈
  ... | delay⦅ _ ⦆                   | st = ⊥-elim $ ¬Delay st
  ... | put⦅ xs , as , y ⦆ | [C-PutRev] {Γ′}{z}{.y}{p}{c′}{v′} {ds = ds}{ss} fresh-z _
      = case c∈ of λ where
      (here refl) →
        step-put
      (there c∈′) →
        let
          (_ , vs , xs) = unzip₃ ds
          (_ , as , _)  = unzip₃ ss
          Γ = || map (uncurry₃ ⟨_has_⟩at_) ds
          Δ = || map (uncurry₃ _∶_♯_) ss
          ΔΓ′ = Δ ∣ Γ′
        in
          ⊥-elim $ c∉ $ there $′ ∈ᶜ-++⁺ʳ Γ ΔΓ′ c∈′

  ... | split⦅ y ⦆ | [C-Split] {.y}{Γ}{vcis} _
      = let
          (vs , cs , _) = unzip₃ vcis
          vcs = zip vs cs
        in
        case ∈ᶜ-++⁻ (|| map (uncurry₃ $ flip ⟨_,_⟩at_) vcis) Γ c∈ of λ where
          (inj₁ c∈Δ) → step-split {vcs = vcs} (c∈vcis⇒′ {vcis = vcis} c∈Δ)
          (inj₂ c∈Γ) → ⊥-elim $ c∉ $ there $ c∈Γ


  ... | _ | [C-Control] {c}{Γ}{L}{v}{x}{α}{Γ′}{i} p Γ≈ Γ→ cv≡
      = let d = c ‼ i; d∗ = removeTopDecorations d

            c∉L : ⟨ c₀ , v₀ ⟩at y₀ ∉ᶜ L
            c∉L = c∉ ∘ ∈ᶜ-++⁺ʳ (⟨ c , v ⟩at x ∣ || map _auth[ x ▷ d ] (nub $ authDecorations d)) Γ
                     ∘ ∈ᶜ-resp-≈ {L}{Γ} (↭-sym Γ≈)
        in
        step-control Γ≈ cv≡ $ h (∈ᶜ-++⁻ (⟨ [ d∗ ] , v ⟩at x) L >≡>
          Sum.[ (λ{ (here refl) → HELP c∉L cv≡ Γ→ c∈ })
              , c∉L
              ]) c∈ Γ→

  ... | init⦅ g , c′ ⦆ | st@([C-Init] _)
      = case ¿ c₀ ≡ c′ ¿ of λ where
          (no ¬eq)   → ⊥-elim $ ¬Init c∉ ¬eq st c∈
          (yes refl) → base (here refl) st

  hᵗ :
      ⟨ c , v ⟩at y ∉ᶜ Γ
    → ⟨ c , v ⟩at y ∈ᶜ Γ′
    → Γ at t —[ α ]→ₜ Γ′ at t′
      --———————————————————————————————
    → ℍ[Contract]⦅ Γ —[ α ]↝ Γ′ ⦆⦅ c ⦆
  hᵗ c∉ c∈ ([Action] Γ→ _) = h c∉ c∈ Γ→
  hᵗ {Γ = Γ} c∉ c∈ ([Delay] _) = ⊥-elim $ c∉ c∈
  hᵗ {c₀}{v₀}{x₀} c∉ c∈ ([Timeout] {c}{t}{v}{x}{Γ}{α}{Γ′}{i} As≡[] _ Γ→ cv≡) =
    step-timeout cv≡ $ h c∉′ c∈ Γ→
    where
      d_ = c ‼ i
      d∗ = removeTopDecorations d_

      c∉Γ : ⟨ c₀ , v₀ ⟩at x₀ ∉ᶜ Γ
      c∉Γ = c∉ ∘ ∈ᶜ-++⁺ʳ (⟨ c , v ⟩at x) Γ

      c∉′ : ⟨ c₀ , v₀ ⟩at x₀ ∉ᶜ ⟨ [ d∗ ] , v ⟩at x ∣ Γ
      c∉′ = λ where
        (here refl) → HELP c∉Γ cv≡ Γ→ c∈
        (there c∈Γ) → c∉Γ c∈Γ

map⦅proj₁⦆∘zip : ∀ {A B : Type} {xs : List A} {ys : List B} →
  map proj₁ (zip xs ys) ⊆ xs
map⦅proj₁⦆∘zip {xs = _ ∷ _ }{_ ∷ _} = λ where
  (here refl) → here refl
  (there x∈)  → there (map⦅proj₁⦆∘zip x∈)

map⦅proj₂⦆∘zip : ∀ {A B : Type} {xs : List A} {ys : List B} →
  map proj₂ (zip xs ys) ⊆ ys
map⦅proj₂⦆∘zip {xs = _ ∷ _ }{_ ∷ _} = λ where
  (here refl) → here refl
  (there x∈)  → there (map⦅proj₂⦆∘zip x∈)

∃ℍ[Contract]⦅_↝_⦆⦅_⦆ : Cfg → Cfg → Contract → Type
∃ℍ[Contract]⦅ Γ ↝ Γ′ ⦆⦅ c ⦆ = ∃ ℍ[Contract]⦅ Γ —[_]↝ Γ′ ⦆⦅ c ⦆

traceContractₜ :
    ⟨ c , v ⟩at y ∉ᶜ Γ₀
  → ⟨ c , v ⟩at y ∈ᶜ Γ
  → (tr : Γ₀ at t —[ αs ]↠ₜ Γ at t′)
    --———————————————————————————————
  → ∃[ tr ∋ ∃ℍ[Contract]⦅_↝_⦆⦅ c ⦆ ]
traceContractₜ {Γ₀ = Γ} c∉ c∈ (_ ∎ₜ) = ⊥-elim $ c∉ c∈
traceContractₜ {c}{v}{y}{Γ₀}{Γ}{t}{α ∷ αs}{t′} c∉ c∈
  (_—→ₜ⟨_⟩_⊢_ .(Γ₀ at t) {Γ₀′ at _}{M at _}{M′ at _}{Γ at t′} Γ₀→M ((refl , Γ₀≈) , (refl , M≈)) M↠)
  with ¿ ⟨ c , v ⟩at y ∈ᶜ M′ ¿
... | yes c∈M′
    = Γ₀ , Γ₀′ , M , M′ , here refl , (Γ₀≈ , M≈)
    , α , hᵗ (∉ᶜ-resp-≈ {Γ₀}{Γ₀′} Γ₀≈ c∉) c∈M′ Γ₀→M
... | no  c∉M′ =
  let _ , _ , _ , _ , xy∈ , H = traceContractₜ (∉ᶜ-resp-≈ {M′}{M} (↭-sym M≈) c∉M′) c∈ M↠
  in -, -, -, -, there xy∈ , H

open import BitML.Properties.Lifetime ⋯

Ancestor⦅_↝_⦆ : Ad → Contract → Rel₀ Cfg
Ancestor⦅ ad ↝ c ⦆ Γ Γ′ =
    ℍ[C-Init]⦅ Γ ↝ Γ′ ⦆⦅ ad ⦆
  × (ad ∙↝∗ c)

ℍ⇒Lifetime : ∀ {i : Index c′} → let open ∣SELECT c′ i in
  ℍ[Contract]⦅ ⟨ [ d∗ ] , v ⟩at x ∣ Γ —[ α ]↝ Γ′ ⦆⦅ c ⦆
  ──────────────────
  c′ ↝ c
ℍ⇒Lifetime {c′}{v}{x}{Γ}{α}{Γ′}{c} {i = i} H
  with ∣SELECT.d∗ c′ i in d≡ | H
... | put _ &reveal _ if _ ⇒ _ | step-put
    = put↝ d≡
... | split _                  | step-split c∈
    = split↝ d≡ c∈
... | _                        | step-timeout {i = 0F} _ H′
  rewrite
      sym d≡
    | removeTopDecorations-idemp (c′ ‼ i)
    = ℍ⇒Lifetime H′

module _ {Γ₀ t₀} (init : Initial Γ₀) (t₀≡0 : t₀ ≡ 0) where

  open import Prelude.Measurable

  traceContract∗ :
      ⟨ c , v ⟩at y ∈ᶜ Γ
    → (tr : Γ₀ at t₀ —[ αs ]↠ₜ Γ at t)
      --———————————————————————————————
    → ∃ λ ad → ∃[ tr ∋ Ancestor⦅ ad ↝ c ⦆ ]
  traceContract∗ c∈₀ tr₀ = go _ (Nat.Ind.<-wellFounded ∣ tr₀ ∣) c∈₀ tr₀ refl
    where
      open ⊆-Reasoning Contract renaming (begin_ to begin⊆_; _∎ to _⊆∎)

      go : ∀ n → Acc Nat._<_ n
        → ⟨ c , v ⟩at y ∈ᶜ Γ
        → (tr : Γ₀ at t₀ —[ αs ]↠ₜ Γ at t)
        → n ≡ ∣ tr ∣
        → ∃ λ ad → ∃[ tr ∋ Ancestor⦅ ad ↝ c ⦆ ]
      go {c₀}{v₀}{y₀}{Γ′}{αs}{t′} _ (acc rec) c∈ Γ↠ refl
        with x , x′ , y , y′ , xy∈ , xy≈@(x≈ , y≈) , α , H ← traceContractₜ (Initial⇒∉ init) c∈ Γ↠
        with tᵢ , _ , xy∈ᵗ ← ×∈⇒×∈ᵗ Γ↠ xy∈
        with Γ≺   ← ≺-splitTraceˡ Γ↠ xy∈ᵗ
        with ∃↑   ← (λ ad {x}{x′} → ∃-splitTraceˡ {P = λ c → Ancestor⦅ ad ↝ c ⦆ } Γ↠ xy∈ᵗ {x}{x′})
        with Γ↠ᵢ  ← splitTraceˡ {Γ₀ at t₀}{αs}{Γ′ at t′}{x at tᵢ} Γ↠ xy∈ᵗ
        with ∈ᶜ↑_ ← (λ {z} → ∈ᶜ-resp-≈ {x′}{x}{z} (↭-sym x≈))
        with H
      ... | base {g}{c} _ Γ→
          = (⟨ g ⟩ c) , x , x′ , y , y′ , xy∈ , xy≈ , init⇒ Γ→ , base
      ... | step-put
          = let ad , H = go _ (rec _ Γ≺) (∈ᶜ↑ here refl) Γ↠ᵢ refl
            in  ad , ∃↑ ad (λ where (H , ⊆ad) → H , step˘ ⊆ad (put↝ {i = 0F} refl)) H
      ... | step-split {vcs = vcs} c∈
          = let ad , H = go _ (rec _ Γ≺) (∈ᶜ↑ here refl) Γ↠ᵢ refl
            in  ad , ∃↑ ad (λ where (H , ⊆ad) → H , step˘ ⊆ad (split↝ {i = 0F} refl c∈)) H
      ... | step-control {c′} _ _ ℍ
          = let ad , H = go _ (rec _ Γ≺) (∈ᶜ↑ here refl) Γ↠ᵢ refl
            in  ad , ∃↑ ad (λ where (H , ⊆ad) → H , step˘ ⊆ad (ℍ⇒Lifetime ℍ)) H
      ... | step-timeout {c′} _ ℍ
          = let ad , H = go _ (rec _ Γ≺) (∈ᶜ↑ here refl) Γ↠ᵢ refl
            in  ad , ∃↑ ad (λ where (H , ⊆ad) → H , step˘ ⊆ad (ℍ⇒Lifetime ℍ)) H
