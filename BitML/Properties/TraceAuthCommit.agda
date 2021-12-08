open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Membership
open import Prelude.Bifunctor
open import Prelude.Nary
open import Prelude.Lists
open import Prelude.DecLists
open import Prelude.Validity
open import Prelude.Setoid
open import Prelude.Traces

module BitML.Properties.TraceAuthCommit
  (Participant : Set) ⦃ _ : DecEq Participant ⦄ (Honest : List⁺ Participant)
  where

open import BitML.BasicTypes
open import BitML.Contracts Participant Honest
open import BitML.Semantics Participant Honest
open import BitML.Properties.Helpers Participant Honest

private
  ¬Control :
      A auth[ ♯▷ ad ] ∉ᶜ Γ
    → (step : Γ —[ α ]→ Γ′)
    → {ctrl : isControl step}
      --————————————————————————————————————
    → A auth[ ♯▷ ad ] ∉ᶜ innerL step {ctrl}
  ¬Control {A}{ad}
    {Γ = .(⟨ c , v ⟩at x ∣ || map _auth[ x ▷ (c ‼ i) ] (nub $ authDecorations (c ‼ i)) ∣ Γ)}
    {α}{Γ′}
    ad∉ ([C-Control] {c}{Γ}{L}{v}{x}{.α}{.Γ′}{i} _ ≈L _ _)
    = ∈ᶜ-++⁻ (⟨ [ removeTopDecorations d_ ] , v ⟩at x) L >≡>
      Sum.[ (λ where (here ()))
          , ∉ᶜ-resp-≈ {Γ}{L} ≈L (ad∉ ∘ ∈ᶜ-++⁺ʳ S₀ Γ)
          ]
    where
      d_ = c ‼ i
      S₀ = ⟨ c , v ⟩at x ∣ || map _auth[ x ▷ d_ ] (nub $ authDecorations d_)

  ¬AuthJoin :
      A auth[ ♯▷ ad ] ∉ᶜ Γ
    → Γ —[ auth-join⦅ B , x ↔ y ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ ♯▷ ad ] ∉ᶜ Γ′
  ¬AuthJoin ad∉ ([DEP-AuthJoin] {A}{v}{x}{v′}{y}{Γ}) ad∈
    with L.Mem.∈-++⁻ (cfgToList $ ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at y ∣ A auth[ x ↔ y ▷⟨ A , v + v′ ⟩ ]) ad∈
  ... | inj₁ ad∈ˡ = case ad∈ˡ of λ where
    (here ())
    (there (here ()))
    (there (there (here ())))
  ... | inj₂ ad∈Γ = ad∉ $ L.Mem.∈-++⁺ʳ (cfgToList $ ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at y) ad∈Γ

  ¬Join :
      A auth[ ♯▷ ad ] ∉ᶜ Γ
    → Γ —[ join⦅ x ↔ y ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ ♯▷ ad ] ∉ᶜ Γ′
  ¬Join ad∉ ([DEP-Join] {z}{x}{y}{Γ}{A}{v}{v′} _) ad∈
    with L.Mem.∈-++⁻ [ ⟨ A has v + v′ ⟩at z ] ad∈
  ... | inj₁ (here ())
  ... | inj₂ ad∈Γ = ad∉ $ L.Mem.∈-++⁺ʳ (cfgToList $ ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at y ∣ A auth[ x ↔ y ▷⟨ A , v + v′ ⟩ ]) ad∈Γ

  ¬AuthDivide :
      A auth[ ♯▷ ad ] ∉ᶜ Γ
    → Γ —[ auth-divide⦅ B , x ▷ v , v′ ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ ♯▷ ad ] ∉ᶜ Γ′
  ¬AuthDivide ad∉ ([DEP-AuthDivide] {A}{v}{v′}{x}{Γ}) ad∈
    with L.Mem.∈-++⁻ (cfgToList $ ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ]) ad∈
  ... | inj₁ ad∈ˡ = case ad∈ˡ of λ where
    (here ())
    (there (here ()))
  ... | inj₂ ad∈Γ = ad∉ $ L.Mem.∈-++⁺ʳ (cfgToList $ ⟨ A has (v + v′) ⟩at x) ad∈Γ

  ¬Divide :
      A auth[ ♯▷ ad ] ∉ᶜ Γ
    → Γ —[ divide⦅ x ▷ v , v′ ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ ♯▷ ad ] ∉ᶜ Γ′
  ¬Divide ad∉ ([DEP-Divide] {x}{Γ}{y}{y′}{A}{v}{v′} _) ad∈
    with L.Mem.∈-++⁻ (cfgToList $ ⟨ A has v ⟩at y ∣ ⟨ A has v′ ⟩at y′) ad∈
  ... | inj₁ ad∈ˡ = case ad∈ˡ of λ where
    (here ())
    (there (here ()))
  ... | inj₂ ad∈Γ = ad∉ $ L.Mem.∈-++⁺ʳ (cfgToList $ ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ]) ad∈Γ

  ¬AuthDonate :
      A auth[ ♯▷ ad ] ∉ᶜ Γ
    → Γ —[ auth-donate⦅ A′ , x ▷ᵈ B ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ ♯▷ ad ] ∉ᶜ Γ′
  ¬AuthDonate ad∉ ([DEP-AuthDonate] {A}{v}{x}{Γ}{B}) =
    L.Mem.∈-++⁻ (cfgToList $ ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B ]) >≡>
    Sum.[ (λ{ (here ()); (there (here ())) })
        , ad∉ ∘ L.Mem.∈-++⁺ʳ [ ⟨ A has v ⟩at x ]
        ]

  ¬Donate :
      A auth[ ♯▷ ad ] ∉ᶜ Γ
    → Γ —[ donate⦅ x ▷ᵈ B ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ ♯▷ ad ] ∉ᶜ Γ′
  ¬Donate ad∉ ([DEP-Donate] {y}{x}{Γ}{A}{v}{B} _) =
    L.Mem.∈-++⁻ [ ⟨ B has v ⟩at y ] >≡>
    Sum.[ (λ{ (here ()) })
        , ad∉ ∘ L.Mem.∈-++⁺ʳ (cfgToList $ ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B ])
        ]

  ¬AuthDestroy : ∀ {xs} {j′ : Index xs}
    → A auth[ ♯▷ ad ] ∉ᶜ Γ
    → Γ —[ auth-destroy⦅ B , xs , j′ ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ ♯▷ ad ] ∉ᶜ Γ′
  ¬AuthDestroy ad∉ ([DEP-AuthDestroy] {y}{Γ}{ds}{j} _) =
    let xs = map select₃ ds
        Aj = proj₁ (ds ‼ j)
        j′ = ‼-map {xs = ds} j
        Δ  = || map (uncurry₃ ⟨_has_⟩at_) ds
    in
    ∈ᶜ-++⁻ (Δ ∣ Aj auth[ xs , j′ ▷ᵈˢ y ]) Γ >≡>
    Sum.[ (∈ᶜ-++⁻ Δ (Aj auth[ xs , j′ ▷ᵈˢ y ]) >≡>
          Sum.[ ad∉ ∘ ∈ᶜ-++⁺ˡ Δ Γ
              , (λ{ (here ()) })
              ])
        , ad∉ ∘ ∈ᶜ-++⁺ʳ Δ Γ
        ]

  ¬Destroy :
      A auth[ ♯▷ ad ] ∉ᶜ Γ
    → Γ —[ destroy⦅ xs ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ ♯▷ ad ] ∉ᶜ Γ′
  ¬Destroy ad∉ ([DEP-Destroy] {y}{Γ}{ds}) =
    let xs = map select₃ ds
        Δ  = || map (λ{ (i , Ai , vi , xi) → ⟨ Ai has vi ⟩at xi ∣ Ai auth[ xs , ‼-map {xs = ds} i ▷ᵈˢ y ] })
                    (enumerate ds)
    in ad∉ ∘ ∈ᶜ-++⁺ʳ Δ Γ

  ¬Advertise :
      A auth[ ♯▷ ad ] ∉ᶜ Γ
    → Γ —[ advertise⦅ ad′ ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ ♯▷ ad ] ∉ᶜ Γ′
  ¬Advertise {ad′ = ad′} ad∉ ([C-Advertise] {ad = .ad′}{Γ} vad hon⁺ d⊆) =
    ∈ᶜ-++⁻ (` ad′) Γ >≡>
    Sum.[ contradict
        , ad∉
        ]

  ¬AuthCommit : ∀ {secrets : List (Secret × Maybe ℕ)}
    → A auth[ ♯▷ ad ] ∉ᶜ Γ
    → ¬ ((A′ ≡ A) × (ad′ ≡ ad))
    → Γ —[ auth-commit⦅ A′ , ad′ , secrets ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ ♯▷ ad ] ∉ᶜ Γ′
  ¬AuthCommit ad∉ ¬eq ([C-AuthCommit] {ad}{A}{Γ}{secrets} _ _ _) =
    let (as , ms) = unzip secrets
        Δ         = || map (uncurry ⟨ A ∶_♯_⟩) secrets
    in
    ∈ᶜ-++⁻ (` ad ∣ Γ ∣ Δ) (A auth[ ♯▷ ad ]) >≡>
    Sum.[ ∈ᶜ-++⁻ (` ad ∣ Γ) Δ >≡>
          Sum.[ ad∉
              , ∉ᶜ-|| {f = uncurry ⟨ A ∶_♯_⟩} (λ{ (here ()); (there ())}) secrets
              ]
        , (λ{ (here refl) → ⊥-elim $ ¬eq (refl , refl) })
        ]

  ¬AuthInit :
      A auth[ ♯▷ ad ] ∉ᶜ Γ
    → Γ —[ auth-init⦅ B , ad′ , x ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ ♯▷ ad ] ∉ᶜ Γ′
  ¬AuthInit ad∉ ([C-AuthInit] {ad}{Γ}{A}{x = x} _ _) =
    ∈ᶜ-++⁻ (` ad ∣ Γ) (A auth[ x ▷ˢ ad ]) >≡>
    Sum.[ ad∉
        , (λ{ (here ()) })
        ]

  ¬Init : let ⟨ G ⟩ C = ad′ in
      A auth[ ♯▷ ad ] ∉ᶜ Γ
    → Γ —[ init⦅ G , C ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ ♯▷ ad ] ∉ᶜ Γ′
  ¬Init ad∉ ([C-Init] {ad}{x}{Γ} _) =
    let toSpend = persistentDeposits $ G ad
        vs      = map (proj₁ ∘ proj₂) toSpend

        Δ₁ = || map (λ{ (Ai , vi , xi) → ⟨ Ai has vi ⟩at xi ∣ Ai auth[ xi ▷ˢ ad ] }) toSpend
        Δ₂ = || map _auth[ ♯▷ ad ] (nub-participants $ ad .G)
    in
    L.Mem.∈-++⁻ [ ⟨ C ad , sum vs ⟩at x ] >≡>
    Sum.[ (λ{ (here ()) })
        , ad∉ ∘ ∈ᶜ-++⁺ˡ (` ad ∣ Γ ∣ Δ₁) Δ₂
              ∘ ∈ᶜ-++⁺ˡ (` ad ∣ Γ) Δ₁
              ∘ ∈ᶜ-++⁺ʳ (` ad) Γ
        ]

  ¬Split :
      A auth[ ♯▷ ad ] ∉ᶜ Γ
    → Γ —[ split⦅ y ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ ♯▷ ad ] ∉ᶜ Γ′
  ¬Split ad∉ step@([C-Control] _ _ L→Γ′ _) = ¬Split (¬Control ad∉ step) L→Γ′
  ¬Split ad∉ ([C-Split] {y}{Γ}{vcis} _) =
    let (vs , cs , _) = unzip₃ vcis in
    ∈ᶜ-++⁻ (|| map (uncurry₃ $ flip ⟨_,_⟩at_) vcis) Γ >≡>
    Sum.[ ∉ᶜ-|| {f = uncurry₃ $ flip ⟨_,_⟩at_} (λ{ (here ()) }) vcis
        , ad∉ ∘ L.Mem.∈-++⁺ʳ [ ⟨ [ split (zip vs cs) ] , sum vs ⟩at y ]
        ]

  ¬AuthRev :
      A auth[ ♯▷ ad ] ∉ᶜ Γ
    → Γ —[ auth-rev⦅ B , a ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ ♯▷ ad ] ∉ᶜ Γ′
  ¬AuthRev ad∉ ([C-AuthRev] {A}{a}{n}{Γ}) =
    L.Mem.∈-++⁻ [ A ∶ a ♯ n ] >≡>
    Sum.[ (λ{ (here ()) })
        , ad∉ ∘ L.Mem.∈-++⁺ʳ [ ⟨ A ∶ a ♯ just n ⟩ ]
        ]

  ¬PutRev :
      A auth[ ♯▷ ad ] ∉ᶜ Γ
    → Γ —[ put⦅ xs , as , y ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ ♯▷ ad ] ∉ᶜ Γ′
  ¬PutRev ad∉ step@([C-Control] _ _ L→Γ′ _) = ¬PutRev (¬Control ad∉ step) L→Γ′
  ¬PutRev ad∉ ([C-PutRev] {Γ′}{z}{y}{p}{c}{v} {ds}{ss} _ _) =
    let (_ , vs , xs) = unzip₃ ds
        (_ , as , _)  = unzip₃ ss
        Γ = || map (uncurry₃ ⟨_has_⟩at_) ds
        Δ = || map (uncurry₃ _∶_♯_) ss
        ΔΓ′ = Δ ∣ Γ′
    in
    L.Mem.∈-++⁻ [ ⟨ c , v + sum vs ⟩at z ] >≡>
    Sum.[ (λ{ (here ()) })
        , ad∉ ∘ L.Mem.∈-++⁺ʳ [ ⟨ [ put xs &reveal as if p ⇒ c ] , v ⟩at y ] ∘ ∈ᶜ-++⁺ʳ Γ ΔΓ′
        ]

  ¬Withdraw :
      A auth[ ♯▷ ad ] ∉ᶜ Γ
    → Γ —[ withdraw⦅ B , v , y ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ ♯▷ ad ] ∉ᶜ Γ′
  ¬Withdraw ad∉ step@([C-Control] _ _ L→Γ′ _) = ¬Withdraw (¬Control ad∉ step) L→Γ′
  ¬Withdraw ad∉ ([C-Withdraw] {x}{y}{Γ}{A}{v} _) =
    L.Mem.∈-++⁻ [ ⟨ A has v ⟩at x ] >≡>
    Sum.[ (λ{ (here ()) })
        , ad∉ ∘ L.Mem.∈-++⁺ʳ [ ⟨ [ withdraw A ] , v ⟩at y ]
        ]

  ¬AuthControl :
      A auth[ ♯▷ ad ] ∉ᶜ Γ
    → Γ —[ auth-control⦅ B , x ▷ d ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ ♯▷ ad ] ∉ᶜ Γ′
  ¬AuthControl ad∉ ([C-AuthControl] {c}{A}{v}{x}{Γ}{i} _) =
    let d = c ‼ i in
    L.Mem.∈-++⁻ (cfgToList $ ⟨ c , v ⟩at x ∣ A auth[ x ▷ d ]) >≡>
    Sum.[ (λ{ (here ()); (there (here ())) })
        , ad∉ ∘ L.Mem.∈-++⁺ʳ [ ⟨ c , v ⟩at x ]
        ]

  h :
      A auth[ ♯▷ ad ] ∉ᶜ Γ
    → A auth[ ♯▷ ad ] ∈ᶜ Γ′
    → Γ —[ α ]→ Γ′
      --——————————————————————————————————————
    → ∃ λ Δ → α ≡ auth-commit⦅ A , ad , Δ ⦆
  h {A}{ad}{Γ}{Γ′}{α} ad∉ ad∈ step
    with α
  ... | auth-join⦅ _ , _ ↔ _ ⦆       = ⊥-elim $ ¬AuthJoin ad∉ step ad∈
  ... | join⦅ _ ↔ _ ⦆                = ⊥-elim $ ¬Join ad∉ step ad∈
  ... | auth-divide⦅ _ , _ ▷ _ , _ ⦆ = ⊥-elim $ ¬AuthDivide ad∉ step ad∈
  ... | divide⦅ _ ▷ _ , _ ⦆          = ⊥-elim $ ¬Divide ad∉ step ad∈
  ... | auth-donate⦅ _ , _ ▷ᵈ _ ⦆    = ⊥-elim $ ¬AuthDonate ad∉ step ad∈
  ... | donate⦅ _ ▷ᵈ _ ⦆             = ⊥-elim $ ¬Donate ad∉ step ad∈
  ... | auth-destroy⦅ _ , _ , _ ⦆    = ⊥-elim $ ¬AuthDestroy ad∉ step ad∈
  ... | destroy⦅ _ ⦆                 = ⊥-elim $ ¬Destroy ad∉ step ad∈
  ... | advertise⦅ _ ⦆               = ⊥-elim $ ¬Advertise ad∉ step ad∈
  ... | auth-init⦅ _ , _ , _ ⦆       = ⊥-elim $ ¬AuthInit ad∉ step ad∈
  ... | init⦅ _ , _ ⦆                = ⊥-elim $ ¬Init ad∉ step ad∈
  ... | split⦅ _ ⦆                   = ⊥-elim $ ¬Split ad∉ step ad∈
  ... | auth-rev⦅ _ , _ ⦆            = ⊥-elim $ ¬AuthRev ad∉ step ad∈
  ... | put⦅ _ , _ , _ ⦆             = ⊥-elim $ ¬PutRev ad∉ step ad∈
  ... | withdraw⦅ _ , _ , _ ⦆        = ⊥-elim $ ¬Withdraw ad∉ step ad∈
  ... | auth-control⦅ _ , _ ▷ _ ⦆    = ⊥-elim $ ¬AuthControl ad∉ step ad∈
  ... | delay⦅ _ ⦆                   = ⊥-elim $ ¬Delay step
  ... | auth-commit⦅ A′ , ad′ , Δ ⦆
    with ¿ (A′ ≡ A) × (ad′ ≡ ad) ¿
  ... | no ¬eq
      = ⊥-elim $ ¬AuthCommit ad∉ ¬eq step ad∈
  ... | yes (refl , refl)
      = case step of λ{ ([C-AuthCommit] {ad = .ad} {A = .A} {secrets = Δ} _ _ _) → Δ , refl }

  hᵗ :
      A auth[ ♯▷ ad ] ∉ᶜ Γ
    → A auth[ ♯▷ ad ] ∈ᶜ Γ′
    → Γ at t —[ α ]→ₜ Γ′ at t′
      --——————————————————————————————————————
    → ∃ λ Δ → α ≡ auth-commit⦅ A , ad , Δ ⦆
  hᵗ auth∉ auth∈ ([Action] Γ→ _) = h auth∉ auth∈ Γ→
  hᵗ auth∉ auth∈ ([Delay] _) = ⊥-elim $ auth∉ auth∈
  hᵗ auth∉ auth∈ ([Timeout] {c}{t}{v}{x}{Γ}{α}{Γ′}{i} _ _ Γ→ _) =
    h (λ where (there auth∈′) → auth∉ (∈ᶜ-++⁺ʳ (⟨ c , v ⟩at x) Γ auth∈′)) auth∈ Γ→

traceAuthCommit :
    A auth[ ♯▷ ad ] ∉ᶜ Γ₀
  → A auth[ ♯▷ ad ] ∈ᶜ Γ
  → Γ₀ at t —[ αs ]↠ₜ Γ at t′
    --————————————————————————————
  → ∃ λ Δ → auth-commit⦅ A , ad , Δ ⦆ ∈ αs
traceAuthCommit auth∉ auth∈ (_ ∎ₜ) = ⊥-elim $ auth∉ auth∈
traceAuthCommit {A}{ad}{Γ₀}{Γ}{t}{α ∷ αs}{t′} auth∉ auth∈
  (_—→ₜ⟨_⟩_⊢_ .(Γ₀ at t) {Γ₀′ at _}{M at _}{M′ at _}{Γ at t′} Γ₀→M ((refl , Γ₀≈) , (refl , M≈)) M↠)
  = case ¿ A auth[ ♯▷ ad ] ∈ᶜ M′ ¿ of λ where
      (yes auth∈M′) → map₂′ (λ{ refl → here refl }) $ hᵗ (∉ᶜ-resp-≈ {Γ₀}{Γ₀′} Γ₀≈ auth∉) auth∈M′ Γ₀→M
      (no  auth∉M′) → map₂′ there $ traceAuthCommit (auth∉M′ ∘ ∈ᶜ-resp-≈ {M}{M′} M≈) auth∈ M↠

ℍ[C-AuthCommit]⦅_↝_⦆⦅_⦆ : Cfg → Cfg → Ad × Participant × List (Secret × Maybe ℕ) → Set
ℍ[C-AuthCommit]⦅ Γ ↝ Γ′ ⦆⦅ ad , A , secrets ⦆ = ∃ λ Γ₁ →
  let ⟨ G ⟩ _ = ad; (as , ms) = unzip secrets; Δ = || map (uncurry ⟨ A ∶_♯_⟩) secrets in
    (Γ ≡ ` ad ∣ Γ₁)
  × (Γ′ ≡ ` ad ∣ Γ₁ ∣ Δ ∣ A auth[ ♯▷ ad ])
    --
  × as ≡ secretsOfᵖ A G          -- a₁..aₖ secrets of A in G
  × All (_∉ secretsOfᶜᶠ A Γ₁) as -- ∀i ∈ 1..k : ∄N : {A : aᵢ ♯ N} ∈ Γ
  × (A ∈ Hon → All Is-just ms)   -- honest participants commit to valid lengths

auth-commit⇒ : ∀ {secrets : List (Secret × Maybe ℕ)}
  → Γ —[ auth-commit⦅ A , ad , secrets ⦆ ]→ Γ′
    --—————————————————————————————————————————————————
  → ℍ[C-AuthCommit]⦅ Γ ↝ Γ′ ⦆⦅ ad , A , secrets ⦆
auth-commit⇒ ([C-AuthCommit] {Γ = Γ} as≡ as∉ hon→) = Γ , refl , refl , as≡ , as∉ , hon→

auth-commit⇒∗ : ∀ {Δ : List (Secret × Maybe ℕ)}
  → (tr : Γₜ —[ αs ]↠ₜ Γₜ′)
  → auth-commit⦅ A , ad , Δ ⦆ ∈ αs
    --———————————————————————————————————————————
  → ∃[ tr ∋ ℍ[C-AuthCommit]⦅_↝_⦆⦅ ad , A ,  Δ ⦆ ]
auth-commit⇒∗ Γ↠ α∈
  with _ , _ , _ , _ , xy∈ , ((_ , x≈) , (_ , y≈)) , [Action] Γ→ refl ← zoom Γ↠ α∈
     = -, -, -, -, L.Mem.∈-map⁺ (map₁₂ cfg) xy∈ , (x≈ , y≈) , auth-commit⇒ Γ→

traceAuthCommit∗ :
    Initial Γ₀
  → A auth[ ♯▷ ad ] ∈ᶜ Γ
  → (tr : Γ₀ at t —[ αs ]↠ₜ Γ at t′)
    --———————————————————————————————————————————
  → ∃ λ Δ → ∃[ tr ∋ ℍ[C-AuthCommit]⦅_↝_⦆⦅ ad , A , Δ ⦆ ]
traceAuthCommit∗ init ad∈ Γ↠ = map₂′ (auth-commit⇒∗ Γ↠) $ traceAuthCommit (Initial⇒∉ init) ad∈ Γ↠
