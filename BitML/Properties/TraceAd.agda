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
    {Γ = .(⟨ c , v ⟩at x ∣ || map _auth[ x ▷ (c ‼ i) ] (nub $ authDecorations (c ‼ i)) ∣ Γ)}
    {α}{Γ′}
    ad∉ ([C-Control] {c}{v}{x}{Γ}{L}{.α}{.Γ′}{i} ≈L _ _)
    = ad∉L
    where
      d_ = c ‼ i
      d∗ = removeTopDecorations d_

      S₀ = ⟨ c , v ⟩at x ∣ || map _auth[ x ▷ d_ ] (nub $ authDecorations d_)
      S  = S₀ ∣ Γ
      S′ = Γ′

      ad∉Γ′ : ` ad ∉ᶜ Γ
      ad∉Γ′ ad∈Γ = ad∉ $ ∈ᶜ-++⁺ʳ S₀ Γ ad∈Γ

      ad∉L : ` ad ∉ᶜ L
      ad∉L ad∈L with L.Mem.∈-++⁻ [ ⟨ [ d∗ ] , v ⟩at x ] (∈ᶜ-resp-≈ {L}{⟨ [ d∗ ] , v ⟩at x ∣ Γ} (↭-sym ≈L) ad∈L)
      ... | inj₁ (here ())
      ... | inj₂ ad∈Γ′ = ad∉Γ′ ad∈Γ′

  ¬AuthJoin :
      ` ad ∉ᶜ Γ
    → Γ —[ auth-join⦅ A , x ↔ y ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∉ᶜ Γ′
  ¬AuthJoin ad∉ step@([C-Control] _ L→Γ′ _) = ¬AuthJoin (¬Control ad∉ step) L→Γ′
  ¬AuthJoin ad∉ ([DEP-AuthJoin] {A}{v}{x}{v′}{y}{Γ}) ad∈
    with L.Mem.∈-++⁻ (cfgToList $ ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at y ∣ A auth[ x ↔ y ▷⟨ A , v + v′ ⟩ ]) ad∈
  ... | inj₁ ad∈ˡ = case ad∈ˡ of λ where
    (here ())
    (there (here ()))
    (there (there (here ())))
  ... | inj₂ ad∈Γ = ad∉ $ L.Mem.∈-++⁺ʳ (cfgToList $ ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at y) ad∈Γ

  ¬Join :
      ` ad ∉ᶜ Γ
    → Γ —[ join⦅ x ↔ y ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∉ᶜ Γ′
  ¬Join ad∉ step@([C-Control] _ L→Γ′ _) = ¬Join (¬Control ad∉ step) L→Γ′
  ¬Join ad∉ ([DEP-Join] {A}{v}{x}{v′}{y}{Γ}{z}) ad∈
    with L.Mem.∈-++⁻ [ ⟨ A has v + v′ ⟩at z ] ad∈
  ... | inj₁ (here ())
  ... | inj₂ ad∈Γ = ad∉ $ L.Mem.∈-++⁺ʳ (cfgToList $ ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at y ∣ A auth[ x ↔ y ▷⟨ A , v + v′ ⟩ ]) ad∈Γ

  ¬AuthDivide :
      ` ad ∉ᶜ Γ
    → Γ —[ auth-divide⦅ A , x ▷ v , v′ ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∉ᶜ Γ′
  ¬AuthDivide ad∉ step@([C-Control] _ L→Γ′ _) = ¬AuthDivide (¬Control ad∉ step) L→Γ′
  ¬AuthDivide ad∉ ([DEP-AuthDivide] {A}{v}{v′}{x}{Γ}) ad∈
    with L.Mem.∈-++⁻ (cfgToList $ ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ]) ad∈
  ... | inj₁ ad∈ˡ = case ad∈ˡ of λ where
    (here ())
    (there (here ()))
  ... | inj₂ ad∈Γ = ad∉ $ L.Mem.∈-++⁺ʳ (cfgToList $ ⟨ A has (v + v′) ⟩at x) ad∈Γ

  ¬Divide :
      ` ad ∉ᶜ Γ
    → Γ —[ divide⦅ x ▷ v , v′ ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∉ᶜ Γ′
  ¬Divide ad∉ step@([C-Control] _ L→Γ′ _) = ¬Divide (¬Control ad∉ step) L→Γ′
  ¬Divide ad∉ ([DEP-Divide] {A}{v}{v′}{x}{Γ}{y}{y′}) ad∈
    with L.Mem.∈-++⁻ (cfgToList $ ⟨ A has v ⟩at y ∣ ⟨ A has v′ ⟩at y′) ad∈
  ... | inj₁ ad∈ˡ = case ad∈ˡ of λ where
    (here ())
    (there (here ()))
  ... | inj₂ ad∈Γ = ad∉ $ L.Mem.∈-++⁺ʳ (cfgToList $ ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ]) ad∈Γ

  ¬AuthDonate :
      ` ad ∉ᶜ Γ
    → Γ —[ auth-donate⦅ A , x ▷ᵈ B ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∉ᶜ Γ′
  ¬AuthDonate ad∉ step@([C-Control] _ L→Γ′ _) = ¬AuthDonate (¬Control ad∉ step) L→Γ′
  ¬AuthDonate ad∉ ([DEP-AuthDonate] {A}{v}{x}{Γ}{B}) =
    L.Mem.∈-++⁻ (cfgToList $ ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B ]) >≡>
    Sum.[ (λ{ (here ()); (there (here ())) })
        , ad∉ ∘ L.Mem.∈-++⁺ʳ [ ⟨ A has v ⟩at x ]
        ]

  ¬Donate :
      ` ad ∉ᶜ Γ
    → Γ —[ donate⦅ x ▷ᵈ B ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∉ᶜ Γ′
  ¬Donate ad∉ step@([C-Control] _ L→Γ′ _) = ¬Donate (¬Control ad∉ step) L→Γ′
  ¬Donate ad∉ ([DEP-Donate] {A}{v}{x}{B}{Γ}{y}) =
    L.Mem.∈-++⁻ [ ⟨ B has v ⟩at y ] >≡>
    Sum.[ (λ{ (here ()) })
        , ad∉ ∘ L.Mem.∈-++⁺ʳ (cfgToList $ ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B ])
        ]

  ¬AuthDestroy : ∀ {xs} {j′ : Index xs}
    → ` ad ∉ᶜ Γ
    → Γ —[ auth-destroy⦅ A , xs , j′ ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∉ᶜ Γ′
  ¬AuthDestroy ad∉ step@([C-Control] _ L→Γ′ _) = ¬AuthDestroy (¬Control ad∉ step) L→Γ′
  ¬AuthDestroy ad∉ ([DEP-AuthDestroy] {Γ}{y}{ds}{j}) =
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
      ` ad ∉ᶜ Γ
    → Γ —[ destroy⦅ xs ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∉ᶜ Γ′
  ¬Destroy ad∉ step@([C-Control] _ L→Γ′ _) = ¬Destroy (¬Control ad∉ step) L→Γ′
  ¬Destroy ad∉ ([DEP-Destroy] {y}{Γ}{ds}) =
    let xs = map select₃ ds
        Δ  = || map (λ{ (i , Ai , vi , xi) → ⟨ Ai has vi ⟩at xi ∣ Ai auth[ xs , ‼-map {xs = ds} i ▷ᵈˢ y ] })
                    (enumerate ds)
    in ad∉ ∘ ∈ᶜ-++⁺ʳ Δ Γ

  ¬Advertise :
      ` ad ∉ᶜ Γ
    → ad ≢ ad′
    → Γ —[ advertise⦅ ad′ ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∉ᶜ Γ′
  ¬Advertise ad∉ ¬eq step@([C-Control] _ L→Γ′ _) = ¬Advertise (¬Control ad∉ step) ¬eq L→Γ′
  ¬Advertise {ad′ = ad′} ad∉ ¬eq ([C-Advertise] {ad = .ad′}{Γ} vad hon⁺ d⊆) =
    ∈ᶜ-++⁻ (` ad′) Γ >≡>
    Sum.[ (λ{ (here refl) → ⊥-elim $ ¬eq refl })
        , ad∉
        ]

  ¬AuthCommit : ∀ {secrets : List (Secret × Maybe ℕ)}
    → ` ad ∉ᶜ Γ
    → Γ —[ auth-commit⦅ A , ad′ , secrets ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∉ᶜ Γ′
  ¬AuthCommit ad∉ step@([C-Control] _ L→Γ′ _) = ¬AuthCommit (¬Control ad∉ step) L→Γ′
  ¬AuthCommit ad∉ ([C-AuthCommit] {ad}{A}{Γ}{secrets} _ _ _) =
    let (as , ms) = unzip secrets
        Δ         = || map (uncurry ⟨ A ∶_♯_⟩) secrets
    in
    ∈ᶜ-++⁻ (` ad ∣ Γ ∣ Δ) (A auth[ ♯▷ ad ]) >≡>
    Sum.[ ∈ᶜ-++⁻ (` ad ∣ Γ) Δ >≡>
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
  ¬AuthInit ad∉ step@([C-Control] _ L→Γ′ _) = ¬AuthInit (¬Control ad∉ step) L→Γ′
  ¬AuthInit ad∉ ([C-AuthInit] {ad}{Γ}{A}{x = x} _ _) =
    ∈ᶜ-++⁻ (` ad ∣ Γ) (A auth[ x ▷ˢ ad ]) >≡>
    Sum.[ ad∉
        , (λ{ (here ()) })
        ]

  ¬Init : let ⟨ G ⟩ C = ad′ in
      ` ad ∉ᶜ Γ
    → Γ —[ init⦅ G , C ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∉ᶜ Γ′
  ¬Init ad∉ step@([C-Control] _ L→Γ′ _) = ¬Init (¬Control ad∉ step) L→Γ′
  ¬Init ad∉ ([C-Init] {ad}{Γ}{x}) =
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
      ` ad ∉ᶜ Γ
    → Γ —[ split⦅ y ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∉ᶜ Γ′
  ¬Split ad∉ step@([C-Control] _ L→Γ′ _) = ¬Split (¬Control ad∉ step) L→Γ′
  ¬Split ad∉ ([C-Split] {y}{Γ}{vcis}) =
    let (vs , cs , _) = unzip₃ vcis in
    ∈ᶜ-++⁻ (|| map (uncurry₃ $ flip ⟨_,_⟩at_) vcis) Γ >≡>
    Sum.[ ∉ᶜ-|| {f = uncurry₃ $ flip ⟨_,_⟩at_} (λ{ (here ()) }) vcis
        , ad∉ ∘ L.Mem.∈-++⁺ʳ [ ⟨ [ split (zip vs cs) ] , sum vs ⟩at y ]
        ]

  ¬AuthRev :
      ` ad ∉ᶜ Γ
    → Γ —[ auth-rev⦅ A , a ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∉ᶜ Γ′
  ¬AuthRev ad∉ step@([C-Control] _ L→Γ′ _) = ¬AuthRev (¬Control ad∉ step) L→Γ′
  ¬AuthRev ad∉ ([C-AuthRev] {A}{a}{n}{Γ}) =
    L.Mem.∈-++⁻ [ A ∶ a ♯ n ] >≡>
    Sum.[ (λ{ (here ()) })
        , ad∉ ∘ L.Mem.∈-++⁺ʳ [ ⟨ A ∶ a ♯ just n ⟩ ]
        ]

  ¬PutRev :
      ` ad ∉ᶜ Γ
    → Γ —[ put⦅ xs , as , y ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∉ᶜ Γ′
  ¬PutRev ad∉ step@([C-Control] _ L→Γ′ _) = ¬PutRev (¬Control ad∉ step) L→Γ′
  ¬PutRev ad∉ ([C-PutRev] {Γ′}{p}{c}{v}{y}{z}{ds}{ss} _) =
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
      ` ad ∉ᶜ Γ
    → Γ —[ withdraw⦅ A , v , y ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∉ᶜ Γ′
  ¬Withdraw ad∉ step@([C-Control] _ L→Γ′ _) = ¬Withdraw (¬Control ad∉ step) L→Γ′
  ¬Withdraw ad∉ ([C-Withdraw] {A}{v}{y}{Γ}{x}) =
    L.Mem.∈-++⁻ [ ⟨ A has v ⟩at x ] >≡>
    Sum.[ (λ{ (here ()) })
        , ad∉ ∘ L.Mem.∈-++⁺ʳ [ ⟨ [ withdraw A ] , v ⟩at y ]
        ]

  ¬AuthControl :
      ` ad ∉ᶜ Γ
    → Γ —[ auth-control⦅ A , x ▷ d ⦆ ]→ Γ′
      --————————————————————————————————————
    → ` ad ∉ᶜ Γ′
  ¬AuthControl ad∉ step@([C-Control] _ L→Γ′ _) = ¬AuthControl (¬Control ad∉ step) L→Γ′
  ¬AuthControl ad∉ ([C-AuthControl] {c}{A}{v}{x}{Γ}{i} _) =
    let d = c ‼ i in
    L.Mem.∈-++⁻ (cfgToList $ ⟨ c , v ⟩at x ∣ A auth[ x ▷ d ]) >≡>
    Sum.[ (λ{ (here ()); (there (here ())) })
        , ad∉ ∘ L.Mem.∈-++⁺ʳ [ ⟨ c , v ⟩at x ]
        ]

  ¬Delay : Γ —[ delay⦅ δ ⦆ ]↛ Γ′
  ¬Delay ([C-Control] _ _ cv≡) = contradict cv≡

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
  ... | yes refl = case step of λ{ ([C-Advertise] {ad = .ad} _ _ _) → refl }

  hᵗ :
      ` ad ∉ᶜ Γ
    → ` ad ∈ᶜ Γ′
    → Γ at t —[ α ]→ₜ Γ′ at t′
      --————————————————————————————
    → (α ≡ advertise⦅ ad ⦆)
  hᵗ ad∉ ad∈ ([Action] Γ→ _) = h ad∉ ad∈ Γ→
  hᵗ ad∉ ad∈ ([Delay] _) = ⊥-elim $ ad∉ ad∈
  hᵗ ad∉ ad∈ ([Timeout] {c}{t}{v}{x}{Γ}{α}{Γ′}{i} _ _ Γ→ _) =
    h (λ where (there ad∈′) → ad∉ (∈ᶜ-++⁺ʳ (⟨ c , v ⟩at x) Γ ad∈′)) ad∈ Γ→

traceAd :
    ` ad ∉ᶜ Γ₀
  → ` ad ∈ᶜ Γ
  → Γ₀ —[ αs ]↠ Γ
    --————————————————————————————
  → (advertise⦅ ad ⦆ ∈ αs)
traceAd ad∉ ad∈ (_ ∎) = ⊥-elim $ ad∉ ad∈

traceAd {ad}{Γ₀}{Γ}{α ∷ αs} ad∉ ad∈ (_—→⟨_⟩_⊢_ .Γ₀ {Γ₀′}{M}{M′}{Γ} Γ₀→M (Γ₀≈ , M≈) M↠)
  = case ¿ ` ad ∈ᶜ M′ ¿ of λ where
      (yes ad∈M′) → here $ sym $ h (∉ᶜ-resp-≈ {Γ₀}{Γ₀′} Γ₀≈ ad∉) ad∈M′ Γ₀→M
      (no  ad∉M′) → there $ traceAd (∉ᶜ-resp-≈ {M′}{M} (↭-sym M≈) ad∉M′) ad∈ M↠

traceAdₜ :
    ` ad ∉ᶜ Γ₀
  → ` ad ∈ᶜ Γ
  → Γ₀ at t —[ αs ]↠ₜ Γ at t′
    --————————————————————————————
  → (advertise⦅ ad ⦆ ∈ αs)
traceAdₜ ad∉ ad∈ (_ ∎ₜ) = ⊥-elim $ ad∉ ad∈
traceAdₜ {ad}{Γ₀}{Γ}{t}{α ∷ αs}{t′} ad∉ ad∈
  (_—→ₜ⟨_⟩_⊢_ .(Γ₀ at t) {Γ₀′ at _}{M at _}{M′ at _}{Γ at t′} Γ₀→M ((refl , Γ₀≈) , (refl , M≈)) M↠)
  = case ¿ ` ad ∈ᶜ M′ ¿ of λ where
      (yes ad∈M′) → here $ sym $ hᵗ (∉ᶜ-resp-≈ {Γ₀}{Γ₀′} Γ₀≈ ad∉) ad∈M′ Γ₀→M
      (no  ad∉M′) → there $ traceAdₜ (ad∉M′ ∘ ∈ᶜ-resp-≈ {M}{M′} M≈) ad∈ M↠

ℍ[C-Advertise]⦅_↝_⦆ : Cfg → Cfg → Ad → Set
ℍ[C-Advertise]⦅ Γ ↝ Γ′ ⦆ ad = let ⟨ G ⟩ _ = ad; partG = nub-participants G in
    (Γ′ ≡ ` ad ∣ Γ)
    --
  × ValidAdvertisement ad    -- the advertisement is valid
  × Any (_∈ Hon) partG       -- at least one honest participant
  × deposits ad ⊆ deposits Γ -- all persistent deposits in place

advertise⇒ :
    Γ —[ advertise⦅ ad ⦆ ]→ Γ′
    --—————————————————————————
  → ℍ[C-Advertise]⦅ Γ ↝ Γ′ ⦆ ad
advertise⇒ ([C-Advertise] vad hon⁺ d⊆) = refl , vad , hon⁺ , d⊆

advertise⇒∗ :
    (tr : Γₜ —[ αs ]↠ₜ Γₜ′)
  → advertise⦅ ad ⦆ ∈ αs
    --————————————————————————————————————
  → ∃ λ x → ∃ λ x′ → ∃ λ y → ∃ λ y′ →
        (x ∈ allStates tr)
      × (y ∈ allStates tr)
      × (x ≈ x′ × y ≈ y′)
      × ℍ[C-Advertise]⦅ x′ ↝ y′ ⦆ ad
advertise⇒∗ {ad = ad} Γ↠ α∈
  with _ , _ , _ , _ , x∈ , y∈ , ((_ , x≈) , (_ , y≈)) , [Action] Γ→ refl ← zoom Γ↠ α∈
    = -, -, -, -, L.Mem.∈-map⁺ cfg x∈ , L.Mem.∈-map⁺ cfg y∈ , (x≈ , y≈) , advertise⇒ Γ→