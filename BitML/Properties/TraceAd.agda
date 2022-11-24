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

module BitML.Properties.TraceAd
  (Participant : Set) ⦃ _ : DecEq Participant ⦄ (Honest : List⁺ Participant)
  where

open import BitML.BasicTypes
open import BitML.Contracts Participant Honest
open import BitML.Semantics Participant Honest
open import BitML.Properties.Helpers Participant Honest

private
  ¬Control :
      ` ad ∉ᶜ Γ
    → (step : Γ —[ α ]→ Γ′)
    → {ctrl : isControl step}
      --————————————————————————————————————
    → ` ad ∉ᶜ innerL step {ctrl}
  ¬Control {ad}
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
      ` ad ∉ᶜ Γ
    → Γ —[ auth-join⦅ A , x ↔ y ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∉ᶜ Γ′
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
      ` ad ∉ᶜ Γ
    → Γ —[ join⦅ x ↔ y ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∉ᶜ Γ′
  ¬Join ad∉ ([DEP-Join] {z}{x}{y}{Γ}{A}{v}{v′} _) ad∈
    with ∈-++⁻ [ ⟨ A has v + v′ ⟩at z ] ad∈
  ... | inj₁ (here ())
  ... | inj₂ ad∈Γ =
    ad∉ $ ∈-++⁺ʳ (cfgToList $ ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at y
                            ∣ A auth[ x ↔ y ▷⟨ A , v + v′ ⟩ ]) ad∈Γ

  ¬AuthDivide :
      ` ad ∉ᶜ Γ
    → Γ —[ auth-divide⦅ A , x ▷ v , v′ ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∉ᶜ Γ′
  ¬AuthDivide ad∉ ([DEP-AuthDivide] {A}{v}{v′}{x}{Γ}) ad∈
    with ∈-++⁻ (cfgToList $ ⟨ A has (v + v′) ⟩at x
                          ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ]) ad∈
  ... | inj₁ ad∈ˡ = case ad∈ˡ of λ where
    (here ())
    (there (here ()))
  ... | inj₂ ad∈Γ = ad∉ $ ∈-++⁺ʳ (cfgToList $ ⟨ A has (v + v′) ⟩at x) ad∈Γ

  ¬Divide :
      ` ad ∉ᶜ Γ
    → Γ —[ divide⦅ x ▷ v , v′ ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∉ᶜ Γ′
  ¬Divide ad∉ ([DEP-Divide] {x}{Γ}{y}{y′}{A}{v}{v′} _) ad∈
    with ∈-++⁻ (cfgToList $ ⟨ A has v ⟩at y ∣ ⟨ A has v′ ⟩at y′) ad∈
  ... | inj₁ ad∈ˡ = case ad∈ˡ of λ where
    (here ())
    (there (here ()))
  ... | inj₂ ad∈Γ =
    ad∉ $ ∈-++⁺ʳ (cfgToList $ ⟨ A has (v + v′) ⟩at x
                            ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ]) ad∈Γ

  ¬AuthDonate :
      ` ad ∉ᶜ Γ
    → Γ —[ auth-donate⦅ A , x ▷ᵈ B ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∉ᶜ Γ′
  ¬AuthDonate ad∉ ([DEP-AuthDonate] {A}{v}{x}{Γ}{B}) =
    ∈-++⁻ (cfgToList $ ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B ]) >≡>
    Sum.[ (λ{ (here ()); (there (here ())) })
        , ad∉ ∘ ∈-++⁺ʳ [ ⟨ A has v ⟩at x ]
        ]

  ¬Donate :
      ` ad ∉ᶜ Γ
    → Γ —[ donate⦅ x ▷ᵈ B ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∉ᶜ Γ′
  ¬Donate ad∉ ([DEP-Donate] {y}{x}{Γ}{A}{v}{B} _) =
    ∈-++⁻ [ ⟨ B has v ⟩at y ] >≡>
    Sum.[ (λ{ (here ()) })
        , ad∉ ∘ ∈-++⁺ʳ (cfgToList $ ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B ])
        ]

  ¬AuthDestroy : ∀ {xs} {j′ : Ix xs}
    → ` ad ∉ᶜ Γ
    → Γ —[ auth-destroy⦅ A , xs , j′ ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∉ᶜ Γ′
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
      ` ad ∉ᶜ Γ
    → Γ —[ destroy⦅ xs ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∉ᶜ Γ′
  ¬Destroy ad∉ ([DEP-Destroy] {y}{Γ}{xs}{get-ds}{j}) =
    let Δ = || mapWithIxˢ xs λ xᵢ i → let Aᵢ , vᵢ = get-ds i in
                 ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xs , i ▷ᵈˢ y ]
    in ad∉ ∘ ∈ᶜ-∪⁺ʳ Δ Γ

  ¬Advertise :
      ` ad ∉ᶜ Γ
    → ad ≢ ad′
    → Γ —[ advertise⦅ ad′ ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∉ᶜ Γ′
  ¬Advertise {ad′ = ad′} ad∉ ¬eq ([C-Advertise] {ad = .ad′}{Γ} vad hon⁺ d⊆) =
    ∈ᶜ-∪⁻ (` ad′) Γ >≡>
    Sum.[ (λ{ (here refl) → ⊥-elim $ ¬eq refl })
        , ad∉
        ]

  ¬AuthCommit : ∀ {secrets : List (Secret × Maybe ℕ)}
    → ` ad ∉ᶜ Γ
    → Γ —[ auth-commit⦅ A , ad′ , secrets ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∉ᶜ Γ′
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

  ¬AuthInit :
      ` ad ∉ᶜ Γ
    → Γ —[ auth-init⦅ A , ad′ , x ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∉ᶜ Γ′
  ¬AuthInit ad∉ ([C-AuthInit] {ad}{Γ}{A}{x = x} _ _) =
    ∈ᶜ-∪⁻ (` ad ∣ Γ) (A auth[ x ▷ˢ ad ]) >≡>
    Sum.[ ad∉
        , (λ{ (here ()) })
        ]

  ¬Init : let ⟨ G ⟩ C = ad′ in
      ` ad ∉ᶜ Γ
    → Γ —[ init⦅ G , C ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∉ᶜ Γ′
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
      ` ad ∉ᶜ Γ
    → Γ —[ split⦅ y ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∉ᶜ Γ′
  ¬Split ad∉ step@([C-Control] _ _ L→Γ′ _) = ¬Split (¬Control ad∉ step) L→Γ′
  ¬Split ad∉ ([C-Split] {y}{Γ}{vcis} _) =
    let (vs , cs , _) = unzip₃ vcis in
    ∈ᶜ-∪⁻ (|| map (uncurry₃ $ flip ⟨_,_⟩at_) vcis) Γ >≡>
    Sum.[ ∉ᶜ-|| {f = uncurry₃ $ flip ⟨_,_⟩at_} (λ{ (here ()) }) vcis
        , ad∉ ∘ ∈-++⁺ʳ [ ⟨ [ split (zip vs cs) ] , sum vs ⟩at y ]
        ]

  ¬AuthRev :
      ` ad ∉ᶜ Γ
    → Γ —[ auth-rev⦅ A , a ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∉ᶜ Γ′
  ¬AuthRev ad∉ ([C-AuthRev] {A}{a}{n}{Γ}) =
    ∈-++⁻ [ A ∶ a ♯ n ] >≡>
    Sum.[ (λ{ (here ()) })
        , ad∉ ∘ ∈-++⁺ʳ [ ⟨ A ∶ a ♯ just n ⟩ ]
        ]

  ¬PutRev :
      ` ad ∉ᶜ Γ
    → Γ —[ put⦅ xs , as , y ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∉ᶜ Γ′
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
      ` ad ∉ᶜ Γ
    → Γ —[ withdraw⦅ A , v , y ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∉ᶜ Γ′
  ¬Withdraw ad∉ step@([C-Control] _ _ L→Γ′ _) = ¬Withdraw (¬Control ad∉ step) L→Γ′
  ¬Withdraw ad∉ ([C-Withdraw] {x}{y}{Γ}{A}{v} _) =
    ∈-++⁻ [ ⟨ A has v ⟩at x ] >≡>
    Sum.[ (λ{ (here ()) })
        , ad∉ ∘ ∈-++⁺ʳ [ ⟨ [ withdraw A ] , v ⟩at y ]
        ]

  ¬AuthControl :
      ` ad ∉ᶜ Γ
    → Γ —[ auth-control⦅ A , x ▷ d ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∉ᶜ Γ′
  ¬AuthControl ad∉ ([C-AuthControl] {c}{A}{v}{x}{Γ}{i} _) =
    let d = c ‼ i in
    ∈-++⁻ (cfgToList $ ⟨ c , v ⟩at x ∣ A auth[ x ▷ d ]) >≡>
    Sum.[ (λ{ (here ()); (there (here ())) })
        , ad∉ ∘ ∈-++⁺ʳ [ ⟨ c , v ⟩at x ]
        ]

  h :
      ` ad ∉ᶜ Γ
    → ` ad ∈ᶜ Γ′
    → Γ —[ α ]→ Γ′
      --————————————————————————————
    → (α ≡ advertise⦅ ad ⦆)
  h {ad}{Γ}{Γ′}{α} ad∉ ad∈ step
    with α
  ... | auth-join⦅ _ , _ ↔ _ ⦆       = ⊥-elim $ ¬AuthJoin ad∉ step ad∈
  ... | join⦅ _ ↔ _ ⦆                = ⊥-elim $ ¬Join ad∉ step ad∈
  ... | auth-divide⦅ _ , _ ▷ _ , _ ⦆ = ⊥-elim $ ¬AuthDivide ad∉ step ad∈
  ... | divide⦅ _ ▷ _ , _ ⦆          = ⊥-elim $ ¬Divide ad∉ step ad∈
  ... | auth-donate⦅ _ , _ ▷ᵈ _ ⦆    = ⊥-elim $ ¬AuthDonate ad∉ step ad∈
  ... | donate⦅ _ ▷ᵈ _ ⦆             = ⊥-elim $ ¬Donate ad∉ step ad∈
  ... | auth-destroy⦅ _ , _ , _ ⦆    = ⊥-elim $ ¬AuthDestroy ad∉ step ad∈
  ... | destroy⦅ _ ⦆                 = ⊥-elim $ ¬Destroy ad∉ step ad∈
  ... | auth-commit⦅ _ , _ , _ ⦆     = ⊥-elim $ ¬AuthCommit ad∉ step ad∈
  ... | auth-init⦅ _ , _ , _ ⦆       = ⊥-elim $ ¬AuthInit ad∉ step ad∈
  ... | init⦅ _ , _ ⦆                = ⊥-elim $ ¬Init ad∉ step ad∈
  ... | split⦅ _ ⦆                   = ⊥-elim $ ¬Split ad∉ step ad∈
  ... | auth-rev⦅ _ , _ ⦆            = ⊥-elim $ ¬AuthRev ad∉ step ad∈
  ... | put⦅ _ , _ , _ ⦆             = ⊥-elim $ ¬PutRev ad∉ step ad∈
  ... | withdraw⦅ _ , _ , _ ⦆        = ⊥-elim $ ¬Withdraw ad∉ step ad∈
  ... | auth-control⦅ _ , _ ▷ _ ⦆    = ⊥-elim $ ¬AuthControl ad∉ step ad∈
  ... | delay⦅ _ ⦆                   = ⊥-elim $ ¬Delay step
  ... | advertise⦅ ad′ ⦆
    with ad ≟ ad′
  ... | no  ad≢  = ⊥-elim $ ¬Advertise ad∉ ad≢ step ad∈
  ... | yes refl = refl

  hᵗ :
      ` ad ∉ᶜ Γ
    → ` ad ∈ᶜ Γ′
    → Γ at t —[ α ]→ₜ Γ′ at t′
      --————————————————————————————
    → (α ≡ advertise⦅ ad ⦆)
  hᵗ ad∉ ad∈ ([Action] Γ→ _) = h ad∉ ad∈ Γ→
  hᵗ ad∉ ad∈ ([Delay] _) = ⊥-elim $ ad∉ ad∈
  hᵗ ad∉ ad∈ ([Timeout] {c}{t}{v}{x}{Γ}{α}{Γ′}{i} _ _ Γ→ _) =
    h (λ where (there ad∈′) → ad∉ (∈ᶜ-∪⁺ʳ (⟨ c , v ⟩at x) Γ ad∈′)) ad∈ Γ→

traceAd :
    ` ad ∉ᶜ Γ₀
  → ` ad ∈ᶜ Γ
  → Γ₀ at t —[ αs ]↠ₜ Γ at t′
    --————————————————————————————
  → (advertise⦅ ad ⦆ ∈ αs)
traceAd ad∉ ad∈ (_ ∎ₜ) = ⊥-elim $ ad∉ ad∈
traceAd {ad}{Γ₀}{Γ}{t}{α ∷ αs}{t′} ad∉ ad∈
  (_—→ₜ⟨_⟩_⊢_ .(Γ₀ at t) {Γ₀′ at _}{M at _}{M′ at _}{Γ at t′} Γ₀→M ((refl , Γ₀≈) , (refl , M≈)) M↠)
  = case ¿ ` ad ∈ᶜ M′ ¿ of λ where
      (yes ad∈M′) → here $ sym $ hᵗ (∉ᶜ-resp-≈ {Γ₀}{Γ₀′} Γ₀≈ ad∉) ad∈M′ Γ₀→M
      (no  ad∉M′) → there $ traceAd (ad∉M′ ∘ ∈ᶜ-resp-≈ {M}{M′} M≈) ad∈ M↠

ℍ[C-Advertise]⦅_↝_⦆⦅_⦆ : Cfg → Cfg → Ad → Set
ℍ[C-Advertise]⦅ Γ ↝ Γ′ ⦆⦅ ad ⦆ = let ⟨ G ⟩ _ = ad; partG = participants G in
    (Γ′ ≡ ` ad ∣ Γ)
    --
  × ValidAdvertisement ad     -- the advertisement is valid
  × Anyˢ (_∈ Hon) partG       -- at least one honest participant
  × deposits ad ⊆ˢ deposits Γ -- all persistent deposits in place

advertise⇒ :
    Γ —[ advertise⦅ ad ⦆ ]→ Γ′
    --—————————————————————————
  → ℍ[C-Advertise]⦅ Γ ↝ Γ′ ⦆⦅ ad ⦆
advertise⇒ ([C-Advertise] vad hon⁺ d⊆) = refl , vad , hon⁺ , d⊆

advertise⇒∗ :
    (tr : Γₜ —[ αs ]↠ₜ Γₜ′)
  → advertise⦅ ad ⦆ ∈ αs
    --————————————————————————————————————
  → ∃[ tr ∋ ℍ[C-Advertise]⦅_↝_⦆⦅ ad ⦆ ]
advertise⇒∗ Γ↠ α∈
  with _ , _ , _ , _ , xy∈ , ((_ , x≈) , (_ , y≈)) , [Action] Γ→ refl ← zoom Γ↠ α∈
    = -, -, -, -, ∈-map⁺ (map₁₂ cfg) xy∈ , (x≈ , y≈) , advertise⇒ Γ→

traceAd∗ :
    Initial Γ₀
  → ` ad ∈ᶜ Γ
  → (tr : Γ₀ at t —[ αs ]↠ₜ Γ at t′)
    --———————————————————————————————
  → ∃[ tr ∋ ℍ[C-Advertise]⦅_↝_⦆⦅ ad ⦆ ]
traceAd∗ init ad∈ Γ↠ = advertise⇒∗ Γ↠ $ traceAd (Initial⇒∉ init) ad∈ Γ↠
