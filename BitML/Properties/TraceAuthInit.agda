open import Prelude.Init
open L.Mem using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺)
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Membership
open import Prelude.Bifunctor
open import Prelude.Nary
open import Prelude.Validity
open import Prelude.Setoid
open import Prelude.Traces
open import Prelude.Sets
open import Prelude.Indexable
open import Prelude.Lists hiding (_‼_)

module BitML.Properties.TraceAuthInit
  (Participant : Set) ⦃ _ : DecEq Participant ⦄ (Honest : List⁺ Participant)
  where

open import BitML.BasicTypes
open import BitML.Contracts Participant Honest
open import BitML.Semantics Participant Honest
open import BitML.Properties.Helpers Participant Honest

private
  ¬Control :
      A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → (step : Γ —[ α ]→ Γ′)
    → {ctrl : isControl step}
      --————————————————————————————————————
    → A auth[ x ▷ˢ ad ] ∉ᶜ innerL step {ctrl}
  ¬Control {A}{y}{ad}
    {Γ = .(⟨ c , v ⟩at x
       ∣ ||ˢ mapˢ _auth[ x ▷ (c ‼ i) ] (authDecorations (c ‼ i)) ∣ Γ)}
    {α}{Γ′}
    ad∉ ([C-Control] {c}{Γ}{L}{v}{x}{.α}{.Γ′}{i} _ ≈L _ _)
    = ∈ᶜ-∪⁻ (⟨ [ removeTopDecorations d_ ] , v ⟩at x) L >≡>
      Sum.[ (λ where (here ()))
          , ∉ᶜ-resp-≈ {Γ}{L} ≈L (ad∉ ∘ ∈ᶜ-∪⁺ʳ S₀ Γ)
          ]
    where
      d_ = c ‼ i
      S₀ = ⟨ c , v ⟩at x ∣ ||ˢ mapˢ _auth[ x ▷ d_ ] (authDecorations d_)

  ¬AuthJoin :
      A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → Γ —[ auth-join⦅ B , x′ ↔ y ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ′
  ¬AuthJoin ad∉ ([DEP-AuthJoin] {A}{v}{x}{v′}{y}{Γ}) ad∈
    with ∈-++⁻ (cfgToList $ ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at y
                          ∣ A auth[ x ↔ y ▷⟨ A , v + v′ ⟩ ]) ad∈
  ... | inj₁ ad∈ˡ = case ad∈ˡ of λ where
    (here ())
    (there (here ()))
    (there (there (here ())))
  ... | inj₂ ad∈Γ =
    ad∉ $ ∈-++⁺ʳ (cfgToList $ ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at y) ad∈Γ

  ¬Join :
      A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → Γ —[ join⦅ x′ ↔ y ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ′
  ¬Join ad∉ ([DEP-Join] {z}{x}{y}{Γ}{A}{v}{v′} _) ad∈
    with ∈-++⁻ [ ⟨ A has v + v′ ⟩at z ] ad∈
  ... | inj₁ (here ())
  ... | inj₂ ad∈Γ =
    ad∉ $ ∈-++⁺ʳ (cfgToList $ ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at y
                            ∣ A auth[ x ↔ y ▷⟨ A , v + v′ ⟩ ]) ad∈Γ

  ¬AuthDivide :
      A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → Γ —[ auth-divide⦅ B , x′ ▷ v , v′ ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ′
  ¬AuthDivide ad∉ ([DEP-AuthDivide] {A}{v}{v′}{x}{Γ}) ad∈
    with ∈-++⁻ (cfgToList $ ⟨ A has (v + v′) ⟩at x
                          ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ]) ad∈
  ... | inj₁ ad∈ˡ = case ad∈ˡ of λ where
    (here ())
    (there (here ()))
  ... | inj₂ ad∈Γ = ad∉ $ ∈-++⁺ʳ (cfgToList $ ⟨ A has (v + v′) ⟩at x) ad∈Γ

  ¬Divide :
      A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → Γ —[ divide⦅ x′ ▷ v , v′ ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ′
  ¬Divide ad∉ ([DEP-Divide] {x}{Γ}{y}{y′}{A}{v}{v′} _) ad∈
    with ∈-++⁻ (cfgToList $ ⟨ A has v ⟩at y ∣ ⟨ A has v′ ⟩at y′) ad∈
  ... | inj₁ ad∈ˡ = case ad∈ˡ of λ where
    (here ())
    (there (here ()))
  ... | inj₂ ad∈Γ =
    ad∉ $ ∈-++⁺ʳ (cfgToList $ ⟨ A has (v + v′) ⟩at x
                            ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ]) ad∈Γ

  ¬AuthDonate :
      A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → Γ —[ auth-donate⦅ A′ , x′ ▷ᵈ B ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ′
  ¬AuthDonate ad∉ ([DEP-AuthDonate] {A}{v}{x}{Γ}{B}) =
    ∈-++⁻ (cfgToList $ ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B ]) >≡>
    Sum.[ (λ{ (here ()); (there (here ())) })
        , ad∉ ∘ ∈-++⁺ʳ [ ⟨ A has v ⟩at x ]
        ]

  ¬Donate :
      A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → Γ —[ donate⦅ x′ ▷ᵈ B ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ′
  ¬Donate ad∉ ([DEP-Donate] {y}{x}{Γ}{A}{v}{B} _) =
    ∈-++⁻ [ ⟨ B has v ⟩at y ] >≡>
    Sum.[ (λ{ (here ()) })
        , ad∉ ∘ ∈-++⁺ʳ (cfgToList $ ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B ])
        ]

  ¬AuthDestroy : ∀ {j′ : Ix xs}
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → Γ —[ auth-destroy⦅ B , xs , j′ ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ′
  ¬AuthDestroy ad∉ ([DEP-AuthDestroy] {y}{Γ}{xs}{get-ds}{j} _) =
    let Aⱼ = get-ds j .proj₁
        ds = mapWithIxˢ xs λ x i → let A , v = get-ds i in  A , v , x
        Δ  = || map (uncurry₃ ⟨_has_⟩at_) ds
    in
    ∈ᶜ-∪⁻ (Δ ∣ Aⱼ auth[ xs , j ▷ᵈˢ y ]) Γ >≡>
    Sum.[ (∈ᶜ-∪⁻ Δ (Aⱼ auth[ xs , j ▷ᵈˢ y ]) >≡>
          Sum.[ ad∉ ∘ ∈ᶜ-∪⁺ˡ Δ Γ
              , (λ{ (here ()) })
              ])
        , ad∉ ∘ ∈ᶜ-∪⁺ʳ Δ Γ
        ]

  ¬Destroy :
      A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → Γ —[ destroy⦅ xs ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ′
  ¬Destroy ad∉ ([DEP-Destroy] {y}{Γ}{xs}{get-ds}{j}) =
    let Δ = || mapWithIxˢ xs λ xᵢ i → let Aᵢ , vᵢ = get-ds i in
                 ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xs , i ▷ᵈˢ y ]
    in ad∉ ∘ ∈ᶜ-∪⁺ʳ Δ Γ

  ¬Advertise :
      A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → Γ —[ advertise⦅ ad′ ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ′
  ¬Advertise {ad′ = ad′} ad∉ ([C-Advertise] {ad = .ad′}{Γ} vad hon⁺ d⊆) =
    ∈ᶜ-∪⁻ (` ad′) Γ >≡>
    Sum.[ contradict
        , ad∉
        ]

  ¬AuthInit :
      A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → ¬ ((A′ ≡ A) × (ad′ ≡ ad) × (x′ ≡ x))
    → Γ —[ auth-init⦅ A′ , ad′ , x′ ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ′
  ¬AuthInit ad∉ ¬eq ([C-AuthInit] {ad}{Γ}{A}{v}{x} _ _) =
    ∈ᶜ-∪⁻ (` ad ∣ Γ) (A auth[ x ▷ˢ ad ]) >≡>
    Sum.[ ad∉
        , (λ{ (here refl) → ⊥-elim $ ¬eq (refl , refl , refl) })
        ]

  ¬AuthCommit : ∀ {secrets : List (Secret × Maybe ℕ)}
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → Γ —[ auth-commit⦅ B , ad′ , secrets ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ′
  ¬AuthCommit ad∉ ([C-AuthCommit] {ad}{A}{Γ}{get-n} _ _) =
    let as      = secretsOfᵖ A (ad .G)
        secrets = mapWithIxˢ as λ a i → a , get-n i
        Δ       = || map (uncurry ⟨ A ∶_♯_⟩) secrets
    in
    ∈ᶜ-∪⁻ (` ad ∣ Γ ∣ Δ) (A auth[ ♯▷ ad ]) >≡>
    Sum.[ ∈ᶜ-∪⁻ (` ad ∣ Γ) Δ >≡>
          Sum.[ ad∉
              , ∉ᶜ-|| {f = uncurry ⟨ A ∶_♯_⟩} (λ{ (here ()); (there ())}) secrets
              ]
        , (λ{ (here ()) })
        ]

  ¬Init : let ⟨ G ⟩ C = ad′ in
      A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → Γ —[ init⦅ G , C ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ′
  ¬Init ad∉ ([C-Init] {ad@(⟨ G ⟩ C)}{x}{Γ} _) =
    let
      toSpend = persistentDeposits G
      vs = mapˢ select₂ toSpend
      Δ₁ = ||ˢ mapˢ (λ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ ad ]) toSpend
      Δ₂ = ||ˢ mapˢ _auth[ ♯▷ ad ] (participants G)
    in
    ∈-++⁻ [ ⟨ C , sumˢ vs ⟩at x ] >≡>
    Sum.[ (λ{ (here ()) })
        , ad∉ ∘ ∈ᶜ-∪⁺ˡ (` ad ∣ Γ ∣ Δ₁) Δ₂
              ∘ ∈ᶜ-∪⁺ˡ (` ad ∣ Γ) Δ₁
              ∘ ∈ᶜ-∪⁺ʳ (` ad) Γ
        ]

  ¬Split :
      A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → Γ —[ split⦅ y ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ′
  ¬Split ad∉ step@([C-Control] _ _ L→Γ′ _) = ¬Split (¬Control ad∉ step) L→Γ′
  ¬Split ad∉ ([C-Split] {y}{Γ}{vcis} _) =
    let (vs , cs , _) = unzip₃ vcis in
    ∈ᶜ-∪⁻ (|| map (uncurry₃ $ flip ⟨_,_⟩at_) vcis) Γ >≡>
    Sum.[ ∉ᶜ-|| {f = uncurry₃ $ flip ⟨_,_⟩at_} (λ{ (here ()) }) vcis
        , ad∉ ∘ ∈-++⁺ʳ [ ⟨ [ split (zip vs cs) ] , sum vs ⟩at y ]
        ]

  ¬AuthRev :
      A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → Γ —[ auth-rev⦅ B , a ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ′
  ¬AuthRev ad∉ ([C-AuthRev] {A}{a}{n}{Γ}) =
    ∈-++⁻ [ A ∶ a ♯ n ] >≡>
    Sum.[ (λ{ (here ()) })
        , ad∉ ∘ ∈-++⁺ʳ [ ⟨ A ∶ a ♯ just n ⟩ ]
        ]

  ¬PutRev :
      A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → Γ —[ put⦅ xs , as , y ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ′
  ¬PutRev ad∉ step@([C-Control] _ _ L→Γ′ _) = ¬PutRev (¬Control ad∉ step) L→Γ′
  ¬PutRev ad∉ ([C-PutRev] {Γ′}{z}{y}{p}{c}{v} {xs}{as}{get-ds}{get-ss} _ _) =
    let ds = mapWithIxˢ xs λ x i → let A , v = get-ds i in A , v , x
        ss = mapWithIxˢ as λ a i → let A , n = get-ss i in A , a , n
        (_ , vs , _) = unzip₃ ds
        Γ = || map (uncurry₃ ⟨_has_⟩at_) ds
        Δ = || map (uncurry₃ _∶_♯_) ss
        ΔΓ′ = Δ ∣ Γ′
    in
    ∈-++⁻ [ ⟨ c , v + sum vs ⟩at z ] >≡>
    Sum.[ (λ{ (here ()) })
        , ad∉ ∘ ∈-++⁺ʳ [ ⟨ [ put xs &reveal as if p ⇒ c ] , v ⟩at y ] ∘ ∈ᶜ-∪⁺ʳ Γ ΔΓ′
        ]

  ¬Withdraw :
      A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → Γ —[ withdraw⦅ B , v , y ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ′
  ¬Withdraw ad∉ step@([C-Control] _ _ L→Γ′ _) = ¬Withdraw (¬Control ad∉ step) L→Γ′
  ¬Withdraw ad∉ ([C-Withdraw] {x}{y}{Γ}{A}{v} _) =
    ∈-++⁻ [ ⟨ A has v ⟩at x ] >≡>
    Sum.[ (λ{ (here ()) })
        , ad∉ ∘ ∈-++⁺ʳ [ ⟨ [ withdraw A ] , v ⟩at y ]
        ]

  ¬AuthControl :
      A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → Γ —[ auth-control⦅ B , x′ ▷ d ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ′
  ¬AuthControl ad∉ ([C-AuthControl] {c}{A}{v}{x}{Γ}{i} _) =
    let d = c ‼ i in
    ∈-++⁻ (cfgToList $ ⟨ c , v ⟩at x ∣ A auth[ x ▷ d ]) >≡>
    Sum.[ (λ{ (here ()); (there (here ())) })
        , ad∉ ∘ ∈-++⁺ʳ [ ⟨ c , v ⟩at x ]
        ]

  h :
      A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → A auth[ x ▷ˢ ad ] ∈ᶜ Γ′
    → Γ —[ α ]→ Γ′
      --——————————————————————————————————————
    → α ≡ auth-init⦅ A , ad , x ⦆
  h {A}{x}{ad}{Γ}{Γ′}{α} ad∉ ad∈ step
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
  ... | auth-commit⦅ _ , _ , _ ⦆     = ⊥-elim $ ¬AuthCommit ad∉ step ad∈
  ... | init⦅ _ , _ ⦆                = ⊥-elim $ ¬Init ad∉ step ad∈
  ... | split⦅ _ ⦆                   = ⊥-elim $ ¬Split ad∉ step ad∈
  ... | auth-rev⦅ _ , _ ⦆            = ⊥-elim $ ¬AuthRev ad∉ step ad∈
  ... | put⦅ _ , _ , _ ⦆             = ⊥-elim $ ¬PutRev ad∉ step ad∈
  ... | withdraw⦅ _ , _ , _ ⦆        = ⊥-elim $ ¬Withdraw ad∉ step ad∈
  ... | auth-control⦅ _ , _ ▷ _ ⦆    = ⊥-elim $ ¬AuthControl ad∉ step ad∈
  ... | delay⦅ _ ⦆                   = ⊥-elim $ ¬Delay step
  ... | auth-init⦅ A′ , ad′ , x′ ⦆
    with ¿ (A′ ≡ A) × (ad′ ≡ ad) × (x′ ≡ x) ¿
  ... | no ¬eq = ⊥-elim $ ¬AuthInit ad∉ ¬eq step ad∈
  ... | yes (refl , refl , refl) = refl

  hᵗ :
      A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → A auth[ x ▷ˢ ad ] ∈ᶜ Γ′
    → Γ at t —[ α ]→ₜ Γ′ at t′
      --——————————————————————————————————————
    → α ≡ auth-init⦅ A , ad , x ⦆
  hᵗ auth∉ auth∈ ([Action] Γ→ _) = h auth∉ auth∈ Γ→
  hᵗ auth∉ auth∈ ([Delay] _) = ⊥-elim $ auth∉ auth∈
  hᵗ auth∉ auth∈ ([Timeout] {c}{t}{v}{x}{Γ}{α}{Γ′}{i} _ _ Γ→ _) =
    h (λ where (there auth∈′) → auth∉ (∈ᶜ-∪⁺ʳ (⟨ c , v ⟩at x) Γ auth∈′)) auth∈ Γ→

traceAuthInit :
    A auth[ x ▷ˢ ad ] ∉ᶜ Γ₀
  → A auth[ x ▷ˢ ad ] ∈ᶜ Γ
  → Γ₀ at t —[ αs ]↠ₜ Γ at t′
    --————————————————————————————
  → auth-init⦅ A , ad , x ⦆ ∈ αs
traceAuthInit auth∉ auth∈ (_ ∎ₜ) = ⊥-elim $ auth∉ auth∈
traceAuthInit {A}{x}{ad}{Γ₀}{Γ}{t}{α ∷ αs}{t′} auth∉ auth∈
  (_—→ₜ⟨_⟩_⊢_ .(Γ₀ at t) {Γ₀′ at _}{M at _}{M′ at _}{Γ at t′} Γ₀→M ((refl , Γ₀≈) , (refl , M≈)) M↠)
  = case ¿ A auth[ x ▷ˢ ad ] ∈ᶜ M′ ¿ of λ where
      (yes auth∈M′) → (λ{ refl → here refl }) $ hᵗ (∉ᶜ-resp-≈ {Γ₀}{Γ₀′} Γ₀≈ auth∉) auth∈M′ Γ₀→M
      (no  auth∉M′) → there $ traceAuthInit (auth∉M′ ∘ ∈ᶜ-resp-≈ {M}{M′} M≈) auth∈ M↠

ℍ[C-AuthInit]⦅_↝_⦆⦅_⦆ : Cfg → Cfg → Participant × Ad × Id → Set
ℍ[C-AuthInit]⦅ Γ ↝ Γ′ ⦆⦅ A , ad , x ⦆ =
  ∃ λ Γ₁ → Σ Value λ v → let ⟨ G ⟩ _ = ad; partG = participants G in
    (Γ ≡ ` ad ∣ Γ₁)
  × (Γ′ ≡ ` ad ∣ Γ₁ ∣ A auth[ x ▷ˢ ad ])
    --
  × partG ⊆ˢ committedParticipants ad Γ₁ -- all participants have committed their secrets
  × (A , v , x) ∈ˢ persistentDeposits G  -- G = A :! v @ x | ...

auth-init⇒ :
    Γ —[ auth-init⦅ A , ad , x ⦆ ]→ Γ′
    --—————————————————————————————————
  → ℍ[C-AuthInit]⦅ Γ ↝ Γ′ ⦆⦅ A , ad , x ⦆
auth-init⇒ ([C-AuthInit] {Γ = Γ} {v = v} p⊆ A∈) = Γ , v , refl , refl , p⊆ , A∈

auth-init⇒∗ :
    (tr : Γₜ —[ αs ]↠ₜ Γₜ′)
  → auth-init⦅ A , ad , z ⦆ ∈ αs
    --————————————————————————————————————————
  → ∃[ tr ∋ ℍ[C-AuthInit]⦅_↝_⦆⦅ A , ad , z ⦆ ]
auth-init⇒∗ Γ↠ α∈
  with _ , _ , _ , _ , xy∈ , ((_ , x≈) , (_ , y≈)) , [Action] Γ→ refl ← zoom Γ↠ α∈
     = -, -, -, -, ∈-map⁺ (map₁₂ cfg) xy∈ , (x≈ , y≈) , auth-init⇒ Γ→

traceAuthInit∗ :
    Initial Γ₀
  → A auth[ x ▷ˢ ad ] ∈ᶜ Γ
  → (tr : Γ₀ at t —[ αs ]↠ₜ Γ at t′)
    --———————————————————————————————
  → ∃[ tr ∋ ℍ[C-AuthInit]⦅_↝_⦆⦅ A , ad , x ⦆ ]
traceAuthInit∗ init ad∈ Γ↠ = auth-init⇒∗ Γ↠ $ traceAuthInit (Initial⇒∉ init) ad∈ Γ↠
