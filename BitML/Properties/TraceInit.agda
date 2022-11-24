open import Prelude.Init
open L.Mem using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Membership
open import Prelude.Bifunctor
open import Prelude.Nary
open import Prelude.Validity
open import Prelude.Setoid
open import Prelude.Traces
open import Prelude.ToN
open import Prelude.Sets
open import Prelude.Indexable
open import Prelude.Lists hiding (_‼_)
open import Prelude.DecLists
open import Prelude.ToList

module BitML.Properties.TraceInit
  (Participant : Set) ⦃ _ : DecEq Participant ⦄ (Honest : List⁺ Participant)
  where

open import BitML.BasicTypes
open import BitML.Contracts Participant Honest
open import BitML.Semantics Participant Honest
open import BitML.Properties.Helpers Participant Honest


private
  ¬Control :
      ` ad ∈ᶜ Γ
    → (step : Γ —[ α ]→ Γ′)
    → {ctrl : isControl step}
      --————————————————————————————————————
    → ` ad ∈ᶜ innerL step {ctrl}
  ¬Control {ad}
    {Γ = .(⟨ c , v ⟩at x ∣ ||ˢ mapˢ _auth[ x ▷ (c ‼ i) ] (authDecorations (c ‼ i)) ∣ Γ)}
    {α}{Γ′}
    ad∈ ([C-Control] {c}{Γ}{L}{v}{x}{.α}{.Γ′}{i} _ ≈L _ _)
    = ∈ᶜ-∪⁺ʳ (⟨ [ removeTopDecorations d_ ] , v ⟩at x) L
    $ ∈ᶜ-resp-≈ {Γ}{L} ≈L ad∈Γ
    where
      d_ = c ‼ i
      S₀₀ = ⟨ c , v ⟩at x
      S₀₁ = ||ˢ mapˢ _auth[ x ▷ d_ ] (authDecorations d_)
      S₀ = S₀₀ ∣ S₀₁

      ad∈Γ : ` ad ∈ᶜ Γ
      ad∈Γ = case ∈ᶜ-∪⁻ S₀ Γ ad∈ of λ where
        (inj₂ ad∈Γ′) → ad∈Γ′
        (inj₁ ad∈S₀) → case ∈ᶜ-∪⁻ S₀₀ S₀₁ ad∈S₀ of λ where
          (inj₁ ad∈ₗ) → contradict ad∈ₗ
          (inj₂ ad∈ᵣ) → ⊥-elim $
            ∉ᶜ-||ˢ (λ where refl → refl)
                   (λ where (here ()); (there ()))
                   (authDecorations d_) ad∈ᵣ

  ¬AuthJoin :
      ` ad ∈ᶜ Γ
    → Γ —[ auth-join⦅ B , x′ ↔ y ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∈ᶜ Γ′
  ¬AuthJoin ad∈ ([DEP-AuthJoin] {A}{v}{x}{v′}{y}{Γ})
    with ∈-++⁻ (cfgToList $ ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at y) ad∈
  ... | inj₁ ad∈ˡ = contradict ad∈ˡ
  ... | inj₂ ad∈Γ = ∈-++⁺ʳ
    (cfgToList $ ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at y ∣ A auth[ x ↔ y ▷⟨ A , v + v′ ⟩ ]) ad∈Γ

  ¬Join :
      ` ad ∈ᶜ Γ
    → Γ —[ join⦅ x′ ↔ y ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∈ᶜ Γ′
  ¬Join ad∈ ([DEP-Join] {z}{x}{y}{Γ}{A}{v}{v′} _)
    with ∈ᶜ-∪⁻ (⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at y ∣ A auth[ x ↔ y ▷⟨ A , v + v′ ⟩ ]) Γ ad∈
  ... | inj₁ ad∈ˡ = contradict ad∈ˡ
  ... | inj₂ ad∈Γ = ∈ᶜ-∪⁺ʳ (⟨ A has v + v′ ⟩at z) Γ ad∈Γ

  ¬AuthDivide :
      ` ad ∈ᶜ Γ
    → Γ —[ auth-divide⦅ B , x′ ▷ v , v′ ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∈ᶜ Γ′
  ¬AuthDivide ad∈ ([DEP-AuthDivide] {A}{v}{v′}{x}{Γ})
    with ∈ᶜ-∪⁻ (⟨ A has (v + v′) ⟩at x) Γ ad∈
  ... | inj₁ ad∈ˡ = contradict ad∈ˡ
  ... | inj₂ ad∈Γ = ∈-++⁺ʳ (cfgToList $ ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ]) ad∈Γ

  ¬Divide :
      ` ad ∈ᶜ Γ
    → Γ —[ divide⦅ x′ ▷ v , v′ ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∈ᶜ Γ′
  ¬Divide ad∈ ([DEP-Divide] {x}{Γ}{y}{y′}{A}{v}{v′} _)
    with ∈ᶜ-∪⁻ (⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ]) Γ ad∈
  ... | inj₁ ad∈ˡ = contradict ad∈ˡ
  ... | inj₂ ad∈Γ = ∈-++⁺ʳ (cfgToList $ ⟨ A has v ⟩at y ∣ ⟨ A has v′ ⟩at y′) ad∈Γ

  ¬AuthDonate :
      ` ad ∈ᶜ Γ
    → Γ —[ auth-donate⦅ A′ , x′ ▷ᵈ B ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∈ᶜ Γ′
  ¬AuthDonate ad∈ ([DEP-AuthDonate] {A}{v}{x}{Γ}{B})
    with ∈ᶜ-∪⁻ (⟨ A has v ⟩at x) Γ ad∈
  ... | inj₁ ad∈ˡ = contradict ad∈ˡ
  ... | inj₂ ad∈Γ = ∈-++⁺ʳ (cfgToList $ ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B ]) ad∈Γ

  ¬Donate :
      ` ad ∈ᶜ Γ
    → Γ —[ donate⦅ x′ ▷ᵈ B ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∈ᶜ Γ′
  ¬Donate ad∈ ([DEP-Donate] {y}{x}{Γ}{A}{v}{B} _)
    with ∈-++⁻ (cfgToList $ ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B ]) ad∈
  ... | inj₁ ad∈ˡ = contradict ad∈ˡ
  ... | inj₂ ad∈Γ = ∈-++⁺ʳ (cfgToList $ ⟨ B has v ⟩at y) ad∈Γ
    -- = ∈-++⁻ (cfgToList $ ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B ]) ad∈ >≡>
    -- Sum.[ (λ{ (here ()); (there (here ())) })
    --     , ∈-++⁺ʳ (cfgToList $ ⟨ B has v ⟩at y)
    --     ]

  ¬AuthDestroy : ∀ {xs} {j′ : Ix xs}
    → ` ad ∈ᶜ Γ
    → Γ —[ auth-destroy⦅ B , xs , j′ ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∈ᶜ Γ′
  ¬AuthDestroy ad∈ ([DEP-AuthDestroy] {y}{Γ}{xs}{get-ds}{j} _) =
    let Aⱼ = get-ds j .proj₁
        ds = mapWithIxˢ xs λ x i → let A , v = get-ds i in  A , v , x
        Δ  = || map (uncurry₃ ⟨_has_⟩at_) ds
    in
    Sum.[ ∈ᶜ-∪⁺ˡ (Δ ∣ Aⱼ auth[ xs , j ▷ᵈˢ y ]) Γ
        ∘ ∈ᶜ-∪⁺ˡ Δ (Aⱼ auth[ xs , j ▷ᵈˢ y ])
        , ∈ᶜ-∪⁺ʳ (Δ ∣ Aⱼ auth[ xs , j ▷ᵈˢ y ]) Γ
        ] (∈ᶜ-∪⁻ Δ Γ ad∈)

  ¬Destroy :
      ` ad ∈ᶜ Γ
    → Γ —[ destroy⦅ xs ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∈ᶜ Γ′
  ¬Destroy ad∈ ([DEP-Destroy] {y}{Γ}{xs}{get-ds}{j}) =
    let Δ = || mapWithIxˢ xs λ xᵢ i → let Aᵢ , vᵢ = get-ds i in
                 ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xs , i ▷ᵈˢ y ]
    in
    case ∈ᶜ-∪⁻ Δ Γ ad∈ of λ where
      (inj₁ ad∈Δ) → ⊥-elim $
        ∉ᶜ-|| (λ{ (here ()); (there (here ())) })
              (enumerate $ xs ∙toList) ad∈Δ
      (inj₂ ad∈Γ) → ad∈Γ

  ¬Advertise :
      ` ad ∈ᶜ Γ
    → Γ —[ advertise⦅ ad′ ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∈ᶜ Γ′
  ¬Advertise {ad′ = ad′} ad∈ ([C-Advertise] {ad = .ad′}{Γ} vad hon⁺ d⊆) =
    ∈-++⁺ʳ [ ` ad′ ] ad∈

  ¬AuthCommit : ∀ {secrets : List (Secret × Maybe ℕ)}
    → ` ad ∈ᶜ Γ
    → Γ —[ auth-commit⦅ B , ad′ , secrets ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∈ᶜ Γ′
  ¬AuthCommit ad∈ ([C-AuthCommit] {ad}{A}{Γ}{get-n} _ _) =
    let as      = secretsOfᵖ A (ad .G)
        secrets = mapWithIxˢ as λ a i → a , get-n i
        Δ       = || map (uncurry ⟨ A ∶_♯_⟩) secrets
    in
    ∈ᶜ-∪⁺ˡ (` ad ∣ Γ ∣ Δ) (A auth[ ♯▷ ad ]) $ ∈ᶜ-∪⁺ˡ (` ad ∣ Γ) Δ ad∈

  ¬AuthInit :
      ` ad ∈ᶜ Γ
    → Γ —[ auth-init⦅ A , ad′ , x ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∈ᶜ Γ′
  ¬AuthInit ad∈ ([C-AuthInit] {ad}{Γ}{A}{v}{x} _ _) =
    ∈ᶜ-∪⁺ˡ (` ad ∣ Γ) (A auth[ x ▷ˢ ad ]) ad∈

  ¬Init :
      ` ad ∈ᶜ Γ
    → ¬ ((g ≡ ad .G) × (c ≡ ad .C))
    → Γ —[ init⦅ g , c ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∈ᶜ Γ′
  ¬Init ad∈ ¬eq ([C-Init] {ad}{x}{Γ} _) = let ⟨ G ⟩ C = ad; partG = participants G in
    let
      toSpend = persistentDeposits G
      vs = mapˢ select₂ toSpend
      Δ₁ = ||ˢ mapˢ (λ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ ad ]) toSpend
      Δ₂ = ||ˢ mapˢ _auth[ ♯▷ ad ] (participants G)
    in
    case ∈ᶜ-∪⁻ (` ad ∣ Γ ∣ Δ₁) Δ₂ ad∈ of λ where
      (inj₂ ad∈Δ₂) → ⊥-elim $
        ∉ᶜ-||ˢ (λ where refl → refl)
               (λ where (here ()); (there ()))
               partG ad∈Δ₂
      (inj₁ ad∈′)  →
        case ∈ᶜ-∪⁻ (` ad ∣ Γ) Δ₁ ad∈′ of λ where
          (inj₂ ad∈Δ₁) → ⊥-elim $
            ∉ᶜ-||ˢ (λ where refl → refl)
                   (λ where (there (here ())); (there (there ())))
                   toSpend ad∈Δ₁
          (inj₁ ad∈″)  →
            case ∈ᶜ-∪⁻ (` ad) Γ ad∈″ of λ where
              (inj₂ ad∈Γ)  → ∈-++⁺ʳ [ ⟨ C , sumˢ vs ⟩at x ] ad∈Γ
              (inj₁ (here refl)) → ⊥-elim $ ¬eq (refl , refl)

  ¬Split :
      ` ad ∈ᶜ Γ
    → Γ —[ split⦅ y ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∈ᶜ Γ′
  ¬Split ad∈ step@([C-Control] _ _ L→Γ′ _) = ¬Split (¬Control ad∈ step) L→Γ′
  ¬Split ad∈ ([C-Split] {y}{Γ}{vcis} _) =
    let (vs , cs , _) = unzip₃ vcis in
    case ∈ᶜ-∪⁻ (⟨ [ split (zip vs cs) ] , sum vs ⟩at y) Γ ad∈ of λ where
      (inj₁ ad∈ˡ) → contradict ad∈ˡ
      (inj₂ ad∈Γ) → ∈ᶜ-∪⁺ʳ (|| map (uncurry₃ $ flip ⟨_,_⟩at_) vcis) Γ ad∈Γ

  ¬AuthRev :
      ` ad ∈ᶜ Γ
    → Γ —[ auth-rev⦅ B , a ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∈ᶜ Γ′
  ¬AuthRev ad∈ ([C-AuthRev] {A}{a}{n}{Γ}) =
    case ∈ᶜ-∪⁻ (⟨ A ∶ a ♯ just n ⟩) Γ ad∈ of λ where
      (inj₁ ad∈ˡ) → contradict ad∈ˡ
      (inj₂ ad∈Γ) → ∈ᶜ-∪⁺ʳ (A ∶ a ♯ n) Γ ad∈Γ

  ¬PutRev :
      ` ad ∈ᶜ Γ
    → Γ —[ put⦅ xs , as , y ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∈ᶜ Γ′
  ¬PutRev ad∈ step@([C-Control] _ _ L→Γ′ _) = ¬PutRev (¬Control ad∈ step) L→Γ′
  ¬PutRev ad∈ ([C-PutRev] {Γ′}{z}{y}{p}{c}{v} {xs}{as}{get-ds}{get-ss} _ _) =
    let ds = mapWithIxˢ xs λ x i → let A , v = get-ds i in A , v , x
        ss = mapWithIxˢ as λ a i → let A , n = get-ss i in A , a , n
        (_ , vs , _) = unzip₃ ds
        Γ = || map (uncurry₃ ⟨_has_⟩at_) ds
        Δ = || map (uncurry₃ _∶_♯_) ss
        ΔΓ′ = Δ ∣ Γ′
    in
    case ∈ᶜ-∪⁻ (⟨ [ put xs &reveal as if p ⇒ c ] , v ⟩at y) (Γ ∣ ΔΓ′) ad∈ of λ where
      (inj₁ ad∈ˡ) → contradict ad∈ˡ
      (inj₂ ad∈′) →
        case ∈ᶜ-∪⁻ Γ ΔΓ′ ad∈′ of λ where
          (inj₁ ad∈Γ) → ⊥-elim $ ∉ᶜ-|| (λ{ (here ())}) ds ad∈Γ
          (inj₂ ad∈ΔΓ′) → ∈ᶜ-∪⁺ʳ (⟨ c , v + sum vs ⟩at z) ΔΓ′ ad∈ΔΓ′

  ¬Withdraw :
      ` ad ∈ᶜ Γ
    → Γ —[ withdraw⦅ B , v , y ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∈ᶜ Γ′
  ¬Withdraw ad∈ step@([C-Control] _ _ L→Γ′ _) = ¬Withdraw (¬Control ad∈ step) L→Γ′
  ¬Withdraw ad∈ ([C-Withdraw] {x}{y}{Γ}{A}{v} _) =
    case ∈ᶜ-∪⁻ (⟨ [ withdraw A ] , v ⟩at y) Γ ad∈ of λ where
      (inj₁ ad∈ˡ) → contradict ad∈ˡ
      (inj₂ ad∈Γ) → ∈ᶜ-∪⁺ʳ (⟨ A has v ⟩at x) Γ ad∈Γ

  ¬AuthControl :
      ` ad ∈ᶜ Γ
    → Γ —[ auth-control⦅ B , x′ ▷ d ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∈ᶜ Γ′
  ¬AuthControl ad∈ ([C-AuthControl] {c}{A}{v}{x}{Γ}{i} _) =
    let d = c ‼ i in
    case ∈ᶜ-∪⁻ (⟨ c , v ⟩at x) Γ ad∈ of λ where
      (inj₁ ad∈ˡ) → ∈ᶜ-∪⁺ˡ (⟨ c , v ⟩at x ∣ A auth[ x ▷ d ]) Γ $ ∈ᶜ-∪⁺ˡ (⟨ c , v ⟩at x) (A auth[ x ▷ d ]) ad∈ˡ
      (inj₂ ad∈Γ) → ∈ᶜ-∪⁺ʳ (⟨ c , v ⟩at x ∣ A auth[ x ▷ d ]) Γ ad∈Γ


  h :
      ` ad ∈ᶜ Γ
    → ` ad ∉ᶜ Γ′
    → Γ —[ α ]→ Γ′
      --——————————————————————————————————————
    → α ≡ init⦅ ad .G , ad .C ⦆
  h {ad}{Γ}{Γ′}{α} ad∈ ad∉′ step
    with α
  ... | auth-join⦅ _ , _ ↔ _ ⦆       = ⊥-elim $ ad∉′ $ ¬AuthJoin ad∈ step
  ... | join⦅ _ ↔ _ ⦆                = ⊥-elim $ ad∉′ $ ¬Join ad∈ step
  ... | auth-divide⦅ _ , _ ▷ _ , _ ⦆ = ⊥-elim $ ad∉′ $ ¬AuthDivide ad∈ step
  ... | divide⦅ _ ▷ _ , _ ⦆          = ⊥-elim $ ad∉′ $ ¬Divide ad∈ step
  ... | auth-donate⦅ _ , _ ▷ᵈ _ ⦆    = ⊥-elim $ ad∉′ $ ¬AuthDonate ad∈ step
  ... | donate⦅ _ ▷ᵈ _ ⦆             = ⊥-elim $ ad∉′ $ ¬Donate ad∈ step
  ... | auth-destroy⦅ _ , _ , _ ⦆    = ⊥-elim $ ad∉′ $ ¬AuthDestroy ad∈ step
  ... | destroy⦅ _ ⦆                 = ⊥-elim $ ad∉′ $ ¬Destroy ad∈ step
  ... | advertise⦅ _ ⦆               = ⊥-elim $ ad∉′ $ ¬Advertise ad∈ step
  ... | auth-commit⦅ _ , _ , _ ⦆     = ⊥-elim $ ad∉′ $ ¬AuthCommit ad∈ step
  ... | auth-init⦅ _ , _ , _ ⦆       = ⊥-elim $ ad∉′ $ ¬AuthInit ad∈ step
  ... | split⦅ _ ⦆                   = ⊥-elim $ ad∉′ $ ¬Split ad∈ step
  ... | auth-rev⦅ _ , _ ⦆            = ⊥-elim $ ad∉′ $ ¬AuthRev ad∈ step
  ... | put⦅ _ , _ , _ ⦆             = ⊥-elim $ ad∉′ $ ¬PutRev ad∈ step
  ... | withdraw⦅ _ , _ , _ ⦆        = ⊥-elim $ ad∉′ $ ¬Withdraw ad∈ step
  ... | auth-control⦅ _ , _ ▷ _ ⦆    = ⊥-elim $ ad∉′ $ ¬AuthControl ad∈ step
  ... | delay⦅ _ ⦆                   = ⊥-elim $ ¬Delay step
  ... | init⦅ g , c ⦆
    with ¿ (g ≡ ad .G) × (c ≡ ad .C) ¿
  ... | no ¬eq = ⊥-elim $ ad∉′ (¬Init ad∈ ¬eq step)
  ... | yes (refl , refl) = refl

  hᵗ :
      ` ad ∈ᶜ Γ
    → ` ad ∉ᶜ Γ′
    → Γ at t —[ α ]→ₜ Γ′ at t′
      --——————————————————————————————————————
    → α ≡ init⦅ ad .G , ad .C ⦆
  hᵗ ad∈ ad∉ ([Action] Γ→ _) = h ad∈ ad∉ Γ→
  hᵗ ad∈ ad∉ ([Delay] _) = ⊥-elim $ ad∉ ad∈
  hᵗ ad∈ ad∉ ([Timeout] {c}{t}{v}{x}{Γ}{α}{Γ′}{i} _ _ Γ→ _) = let d = c ‼ i; d∗ = removeTopDecorations d in
    h (∈ᶜ-∪⁺ʳ (⟨ [ d∗ ] , v ⟩at x) Γ (case ad∈ of λ where (there ad∈′) → ad∈′)) ad∉ Γ→

traceInit :
    ` ad ∈ᶜ Γ₀
  → ` ad ∉ᶜ Γ
  → Γ₀ at t —[ αs ]↠ₜ Γ at t′
    --————————————————————————————
  → init⦅ ad .G , ad .C ⦆ ∈ αs
traceInit ad∈ ad∉ (_ ∎ₜ) = ⊥-elim $ ad∉ ad∈
traceInit {ad}{Γ₀}{Γ}{t}{α ∷ αs}{t′} ad∈ ad∉
  (_—→ₜ⟨_⟩_⊢_ .(Γ₀ at t) {Γ₀′ at _}{M at _}{M′ at _}{Γ at t′}
                         Γ₀→M ((refl , Γ₀≈) , (refl , M≈)) M↠)
  = case ¿ ` ad ∈ᶜ M′ ¿ of λ where
      (no  ad∉M′) → here $ sym $ hᵗ (∈ᶜ-resp-≈ {Γ₀}{Γ₀′} Γ₀≈ ad∈) ad∉M′ Γ₀→M
      (yes ad∈M′) → there $ traceInit (∈ᶜ-resp-≈ {M′}{M} (↭-sym M≈) ad∈M′) ad∉ M↠

ℍ[C-Init]⦅_↝_⦆⦅_⦆ : Cfg → Cfg → Ad → Set
ℍ[C-Init]⦅ Γ ↝ Γ′ ⦆⦅ ad ⦆ =
  ∃ λ Γ₁ → ∃ λ x → let ⟨ G ⟩ C = ad; partG = participants G in
  let toSpend = persistentDeposits G
      vs      = mapˢ select₂ toSpend
  in
    (Γ ≡ ` ad ∣ Γ₁
       ∣ ||ˢ mapˢ (λ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ ad ]) toSpend
       ∣ ||ˢ mapˢ _auth[ ♯▷ ad ] partG)
  × (Γ′ ≡ ⟨ C , sumˢ vs ⟩at x ∣ Γ₁)

init⇒ :
    Γ —[ init⦅ g , c ⦆ ]→ Γ′
    --—————————————————————————
  → ℍ[C-Init]⦅ Γ ↝ Γ′ ⦆⦅ ⟨ g ⟩ c ⦆
init⇒ ([C-Init] _) = -, -, refl , refl

init⇒∗ :
    (tr : Γₜ —[ αs ]↠ₜ Γₜ′)
  → init⦅ g , c ⦆ ∈ αs
    --—————————————————————————————————
  → ∃[ tr ∋ ℍ[C-Init]⦅_↝_⦆⦅ ⟨ g ⟩ c ⦆ ]
init⇒∗ Γ↠ α∈
  with _ , _ , _ , _ , xy∈ , ((_ , x≈) , (_ , y≈)) , [Action] Γ→ refl ← zoom Γ↠ α∈
     = -, -, -, -, L.Mem.∈-map⁺ (map₁₂ cfg) xy∈ , (x≈ , y≈) , init⇒ Γ→

open import BitML.Properties.TraceAd Participant Honest
open import BitML.Properties.TraceAuthInit Participant Honest

∃ℍ[C-AuthInit]⦅_↝_⦆⦅_⦆ : Cfg → Cfg → Ad → Set
∃ℍ[C-AuthInit]⦅ Γ ↝ Γ′ ⦆⦅ ad ⦆ = ∃ λ A → ∃ λ x → ℍ[C-AuthInit]⦅ Γ ↝ Γ′ ⦆⦅ A , ad , x ⦆

private
  HELP :
    let toSpend = persistentDeposits (ad .G); partG = participants (ad .G) in

      Valid ad
    → A ∈ˢ partG
    → ||ˢ mapˢ (λ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ
                                 ∣ Aᵢ auth[ xᵢ ▷ˢ ad ]) toSpend ⊆ᶜ Γ
      --————————————————————————————————————————
    → ∃ λ xᵢ → A auth[ xᵢ ▷ˢ ad ] ∈ᶜ Γ
  HELP {ad@(⟨ G ⟩ C)}{A}{Γ} vad A∈ Γ⊆ =
    xᵢ , auth∈
    where
      toSpend = persistentDeposits G
      A∈′ : A ∈ˢ persistentParticipants G
      A∈′ = vad .participants-⊆ (∈-∪⁺ˡ _ (participants G) (participants C) A∈)

      ∃A∈ : ∃ λ (vᵢ : Value) → ∃ λ (xᵢ : Id) → (A , vᵢ , xᵢ) ∈ˢ toSpend
      ∃A∈ with _ , Avx∈ , refl ← ∈ˢ-map⁻ proj₁ {persistentDeposits G} A∈′
        = -, -, Avx∈

      vᵢ = ∃A∈ .proj₁
      xᵢ = ∃A∈ .proj₂ .proj₁
      Avx∈ = ∃A∈ .proj₂ .proj₂

      auth∈ : A auth[ xᵢ ▷ˢ ad ] ∈ᶜ Γ
      auth∈ = ∈ᶜ-||ˢ⇒⊆ᶜ {Γ = Γ} toSpend (λ where refl → refl) Avx∈ Γ⊆
            $ ∈ᶜ-∪⁺ʳ (⟨ A has vᵢ ⟩at xᵢ) (A auth[ xᵢ ▷ˢ ad ]) (here refl)

ℍ[C-Init]⇒∃ℍ[C-AuthInit] :
    Initial Γₜ
  → (tr : Γₜ —[ αs ]↠ₜ Γₜ′)
  → ∃[ tr ∋ ℍ[C-Init]⦅_↝_⦆⦅ ad ⦆ ]
    --————————————————————————————————
  → ∃[ tr ∋ ∃ℍ[C-AuthInit]⦅_↝_⦆⦅ ad ⦆ ]
  × Valid ad
  × ad ∈ˢ advertisements tr
ℍ[C-Init]⇒∃ℍ[C-AuthInit] {Γₜ}{αs}{Γₜ′}{ad}
  (init , t≡0) tr (x , x′ , y , y′ , xy∈ , (x≈ , y≈) , H@(Γ₁ , xx , Γ≡ , Γ≡′))
  with tᵢ , _ , xy∈ᵗ ← ×∈⇒×∈ᵗ tr xy∈
  = ℍ , vad , ad∈∗
  where
    partG = participants (ad .G)
    Γₜᵢ = x at tᵢ

    tr′ : Γₜ —[ take (toℕ $ L.Any.index xy∈ᵗ) αs ]↠ₜ Γₜᵢ
    tr′ = splitTraceˡ tr xy∈ᵗ

    -- traceAd --

    ad∈′ : ` ad ∈ᶜ x′
    ad∈′ rewrite Γ≡ = here refl

    ad∈ : ` ad ∈ᶜ x
    ad∈ = ∈ᶜ-resp-≈ {x′}{x} (↭-sym x≈) ad∈′

    H′ : ∃[ tr′ ∋ ℍ[C-Advertise]⦅_↝_⦆⦅ ad ⦆ ]
    H′ = traceAd∗ init ad∈ tr′

    vad : Valid ad
    vad = let _ , _ , _ , _ , _ , _ , _ , vad , _ , _ = H′ in vad

    ∃hon : Anyˢ (_∈ Hon) partG
    ∃hon = let _ , _ , _ , _ , _ , _ , _ , _ , ∃hon , _ = H′ in ∃hon

    p : Participant
    p = L.Any.lookup ∃hon

    p∈ : p ∈ˢ partG
    p∈ = lookup∈ ∃hon

    p∈hon : p ∈ Hon
    p∈hon = L.Any.lookup-result ∃hon

    -- traceAuthInit --

    ∃auth∈ : ∃ λ xᵢ → p auth[ xᵢ ▷ˢ ad ] ∈ᶜ x′
    ∃auth∈ = qed′
      where
        toSpend = persistentDeposits (ad .G)
        Δ₁ = ` ad ∣ Γ₁
        Δ₂ = ||ˢ mapˢ (λ{ (Aᵢ , vᵢ , xᵢ) → ⟨ Aᵢ has vᵢ ⟩at xᵢ ∣ Aᵢ auth[ xᵢ ▷ˢ ad ] }) toSpend
        Δ₃ = ||ˢ mapˢ _auth[ ♯▷ ad ] partG
        Δ₁₂₃ = Δ₁ ∣ Δ₂ ∣ Δ₃

        Δ⊆ : Δ₂ ⊆ᶜ Δ₁₂₃
        Δ⊆ = ⊆ᶜ-∪⁺ˡ {Δ₂} (Δ₁ ∣ Δ₂) Δ₃
           $ ⊆ᶜ-∪⁺ʳ {Δ₂} Δ₁ Δ₂
           $ ⊆ᶜ-refl {Δ₂}

        qed : ∃ λ xᵢ → p auth[ xᵢ ▷ˢ ad ] ∈ᶜ Δ₁₂₃
        qed = HELP {Γ = Δ₁₂₃} vad p∈ Δ⊆

        qed′ : ∃ λ xᵢ → p auth[ xᵢ ▷ˢ ad ] ∈ᶜ x′
        qed′ = proj₁ qed , subst (p auth[ proj₁ qed ▷ˢ ad ] ∈ᶜ_) (sym Γ≡) (proj₂ qed)
        -- [BUG] c.f. personal-practice/agda/bugs/SubstDependentProduct.agda

    xᵢ = proj₁ ∃auth∈

    auth∈′ : p auth[ xᵢ ▷ˢ ad ] ∈ᶜ x′
    auth∈′ = proj₂ ∃auth∈

    auth∈ : p auth[ xᵢ ▷ˢ ad ] ∈ᶜ x
    auth∈ = ∈ᶜ-resp-≈ {x′}{x} (↭-sym x≈) auth∈′

    H″ : ∃[ tr′ ∋ ℍ[C-AuthInit]⦅_↝_⦆⦅ p , ad , xᵢ ⦆ ]
    H″ = traceAuthInit∗ init auth∈ tr′

    ℍ : ∃[ tr ∋ ∃ℍ[C-AuthInit]⦅_↝_⦆⦅ ad ⦆ ]
    ℍ = ∃-splitTraceˡ′ tr xy∈ᵗ (-,_ ∘ -,_) H″

    ad∈∗ : ad ∈ˢ advertisements tr
    ad∈∗ =
      let
        x , x′ , _ , _ , xy∈ , (x≈ , _)
          , _ , _ , Γ₁ , _ , Γ≡ , _ , part⊆ , _ = ℍ
        x∈ , _ = ∈-allTransitions⁻ tr xy∈

        ad∈Γ₁ : ad ∈ˢ advertisements Γ₁
        ad∈Γ₁ = committed⇒authAd p∈hon {ad}{Γ₁}
              $ part⊆ p∈

        ad∈adΓ₁ : ad ∈ˢ advertisements (` ad ∣ Γ₁)
        ad∈adΓ₁ = ∈-collect-∪⁺ʳ (` ad) Γ₁ ad∈Γ₁

        ad∈x′ : ad ∈ˢ advertisements x′
        ad∈x′ = subst (λ ◆ → ad ∈ˢ advertisements ◆) (sym Γ≡) ad∈adΓ₁

        ad∈x : ad ∈ˢ advertisements x
        ad∈x = ∈ads-resp-≈ ad {x′}{x} (↭-sym x≈) ad∈x′

      in
        ads⊆ {Γ = x} tr x∈ ad∈x
