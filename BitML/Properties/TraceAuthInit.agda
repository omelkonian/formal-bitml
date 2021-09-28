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

      ad∉Γ′ : A auth[ y ▷ˢ ad ] ∉ᶜ Γ
      ad∉Γ′ ad∈Γ = ad∉ $ ∈ᶜ-++⁺ʳ S₀ Γ ad∈Γ

      ad∉L : A auth[ y ▷ˢ ad ] ∉ᶜ L
      ad∉L ad∈L with L.Mem.∈-++⁻ [ ⟨ [ d∗ ] , v ⟩at x ] (∈ᶜ-resp-≈ {L}{⟨ [ d∗ ] , v ⟩at x ∣ Γ} (↭-sym ≈L) ad∈L)
      ... | inj₁ (here ())
      ... | inj₂ ad∈Γ′ = ad∉Γ′ ad∈Γ′

  ¬AuthJoin :
      A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → Γ —[ auth-join⦅ B , x′ ↔ y ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ′
  ¬AuthJoin ad∉ step@([C-Control] _ L→Γ′ _) = ¬AuthJoin (¬Control ad∉ step) L→Γ′
  ¬AuthJoin ad∉ ([DEP-AuthJoin] {A}{v}{x}{v′}{y}{Γ}) ad∈
    with L.Mem.∈-++⁻ (cfgToList $ ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at y ∣ A auth[ x ↔ y ▷⟨ A , v + v′ ⟩ ]) ad∈
  ... | inj₁ ad∈ˡ = case ad∈ˡ of λ where
    (here ())
    (there (here ()))
    (there (there (here ())))
  ... | inj₂ ad∈Γ = ad∉ $ L.Mem.∈-++⁺ʳ (cfgToList $ ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at y) ad∈Γ

  ¬Join :
      A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → Γ —[ join⦅ x′ ↔ y ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ′
  ¬Join ad∉ step@([C-Control] _ L→Γ′ _) = ¬Join (¬Control ad∉ step) L→Γ′
  ¬Join ad∉ ([DEP-Join] {A}{v}{x}{v′}{y}{Γ}{z}) ad∈
    with L.Mem.∈-++⁻ [ ⟨ A has v + v′ ⟩at z ] ad∈
  ... | inj₁ (here ())
  ... | inj₂ ad∈Γ = ad∉ $ L.Mem.∈-++⁺ʳ (cfgToList $ ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at y ∣ A auth[ x ↔ y ▷⟨ A , v + v′ ⟩ ]) ad∈Γ

  ¬AuthDivide :
      A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → Γ —[ auth-divide⦅ B , x′ ▷ v , v′ ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ′
  ¬AuthDivide ad∉ step@([C-Control] _ L→Γ′ _) = ¬AuthDivide (¬Control ad∉ step) L→Γ′
  ¬AuthDivide ad∉ ([DEP-AuthDivide] {A}{v}{v′}{x}{Γ}) ad∈
    with L.Mem.∈-++⁻ (cfgToList $ ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ]) ad∈
  ... | inj₁ ad∈ˡ = case ad∈ˡ of λ where
    (here ())
    (there (here ()))
  ... | inj₂ ad∈Γ = ad∉ $ L.Mem.∈-++⁺ʳ (cfgToList $ ⟨ A has (v + v′) ⟩at x) ad∈Γ

  ¬Divide :
      A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → Γ —[ divide⦅ x′ ▷ v , v′ ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ′
  ¬Divide ad∉ step@([C-Control] _ L→Γ′ _) = ¬Divide (¬Control ad∉ step) L→Γ′
  ¬Divide ad∉ ([DEP-Divide] {A}{v}{v′}{x}{Γ}{y}{y′}) ad∈
    with L.Mem.∈-++⁻ (cfgToList $ ⟨ A has v ⟩at y ∣ ⟨ A has v′ ⟩at y′) ad∈
  ... | inj₁ ad∈ˡ = case ad∈ˡ of λ where
    (here ())
    (there (here ()))
  ... | inj₂ ad∈Γ = ad∉ $ L.Mem.∈-++⁺ʳ (cfgToList $ ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ]) ad∈Γ

  ¬AuthDonate :
      A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → Γ —[ auth-donate⦅ A′ , x′ ▷ᵈ B ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ′
  ¬AuthDonate ad∉ step@([C-Control] _ L→Γ′ _) = ¬AuthDonate (¬Control ad∉ step) L→Γ′
  ¬AuthDonate ad∉ ([DEP-AuthDonate] {A}{v}{x}{Γ}{B}) =
    L.Mem.∈-++⁻ (cfgToList $ ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B ]) >≡>
    Sum.[ (λ{ (here ()); (there (here ())) })
        , ad∉ ∘ L.Mem.∈-++⁺ʳ [ ⟨ A has v ⟩at x ]
        ]

  ¬Donate :
      A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → Γ —[ donate⦅ x′ ▷ᵈ B ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ′
  ¬Donate ad∉ step@([C-Control] _ L→Γ′ _) = ¬Donate (¬Control ad∉ step) L→Γ′
  ¬Donate ad∉ ([DEP-Donate] {A}{v}{x}{B}{Γ}{y}) =
    L.Mem.∈-++⁻ [ ⟨ B has v ⟩at y ] >≡>
    Sum.[ (λ{ (here ()) })
        , ad∉ ∘ L.Mem.∈-++⁺ʳ (cfgToList $ ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B ])
        ]

  ¬AuthDestroy : ∀ {xs} {j′ : Index xs}
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → Γ —[ auth-destroy⦅ B , xs , j′ ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ′
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
      A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → Γ —[ destroy⦅ xs ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ′
  ¬Destroy ad∉ step@([C-Control] _ L→Γ′ _) = ¬Destroy (¬Control ad∉ step) L→Γ′
  ¬Destroy ad∉ ([DEP-Destroy] {y}{Γ}{ds}) =
    let xs = map select₃ ds
        Δ  = || map (λ{ (i , Ai , vi , xi) → ⟨ Ai has vi ⟩at xi ∣ Ai auth[ xs , ‼-map {xs = ds} i ▷ᵈˢ y ] })
                    (enumerate ds)
    in ad∉ ∘ ∈ᶜ-++⁺ʳ Δ Γ

  ¬Advertise :
      A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → Γ —[ advertise⦅ ad′ ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ′
  ¬Advertise ad∉ step@([C-Control] _ L→Γ′ _) = ¬Advertise (¬Control ad∉ step) L→Γ′
  ¬Advertise {ad′ = ad′} ad∉ ([C-Advertise] {ad = .ad′}{Γ} vad hon⁺ d⊆) =
    ∈ᶜ-++⁻ (` ad′) Γ >≡>
    Sum.[ contradict
        , ad∉
        ]

  ¬AuthInit :
      A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → ¬ ((A′ ≡ A) × (ad′ ≡ ad) × (x′ ≡ x))
    → Γ —[ auth-init⦅ A′ , ad′ , x′ ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ′
  ¬AuthInit ad∉ ¬eq step@([C-Control] _ L→Γ′ _) = ¬AuthInit (¬Control ad∉ step) ¬eq L→Γ′
  ¬AuthInit ad∉ ¬eq ([C-AuthInit] {ad}{Γ}{A}{v}{x} _ _) =
    ∈ᶜ-++⁻ (` ad ∣ Γ) (A auth[ x ▷ˢ ad ]) >≡>
    Sum.[ ad∉
        , (λ{ (here refl) → ⊥-elim $ ¬eq (refl , refl , refl) })
        ]

  ¬AuthCommit : ∀ {secrets : List (Secret × Maybe ℕ)}
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → Γ —[ auth-commit⦅ B , ad′ , secrets ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ′
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

  ¬Init : let ⟨ G ⟩ C = ad′ in
      A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → Γ —[ init⦅ G , C ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ′
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
      A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → Γ —[ split⦅ y ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ′
  ¬Split ad∉ step@([C-Control] _ L→Γ′ _) = ¬Split (¬Control ad∉ step) L→Γ′
  ¬Split ad∉ ([C-Split] {y}{Γ}{vcis}) =
    let (vs , cs , _) = unzip₃ vcis in
    ∈ᶜ-++⁻ (|| map (uncurry₃ $ flip ⟨_,_⟩at_) vcis) Γ >≡>
    Sum.[ ∉ᶜ-|| {f = uncurry₃ $ flip ⟨_,_⟩at_} (λ{ (here ()) }) vcis
        , ad∉ ∘ L.Mem.∈-++⁺ʳ [ ⟨ [ split (zip vs cs) ] , sum vs ⟩at y ]
        ]

  ¬AuthRev :
      A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → Γ —[ auth-rev⦅ B , a ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ′
  ¬AuthRev ad∉ step@([C-Control] _ L→Γ′ _) = ¬AuthRev (¬Control ad∉ step) L→Γ′
  ¬AuthRev ad∉ ([C-AuthRev] {A}{a}{n}{Γ}) =
    L.Mem.∈-++⁻ [ A ∶ a ♯ n ] >≡>
    Sum.[ (λ{ (here ()) })
        , ad∉ ∘ L.Mem.∈-++⁺ʳ [ ⟨ A ∶ a ♯ just n ⟩ ]
        ]

  ¬PutRev :
      A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → Γ —[ put⦅ xs , as , y ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ′
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
      A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → Γ —[ withdraw⦅ B , v , y ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ′
  ¬Withdraw ad∉ step@([C-Control] _ L→Γ′ _) = ¬Withdraw (¬Control ad∉ step) L→Γ′
  ¬Withdraw ad∉ ([C-Withdraw] {A}{v}{y}{Γ}{x}) =
    L.Mem.∈-++⁻ [ ⟨ A has v ⟩at x ] >≡>
    Sum.[ (λ{ (here ()) })
        , ad∉ ∘ L.Mem.∈-++⁺ʳ [ ⟨ [ withdraw A ] , v ⟩at y ]
        ]

  ¬AuthControl :
      A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → Γ —[ auth-control⦅ B , x′ ▷ d ⦆ ]→ Γ′
      --————————————————————————————————————
    → A auth[ x ▷ˢ ad ] ∉ᶜ Γ′
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
  ... | no ¬eq
      = ⊥-elim $ ¬AuthInit ad∉ ¬eq step ad∈
  ... | yes (refl , refl , refl)
      = case step of λ{ ([C-AuthInit] {ad = .ad} {A = .A} {x = .x} _ _) → refl }

  hᵗ :
      A auth[ x ▷ˢ ad ] ∉ᶜ Γ
    → A auth[ x ▷ˢ ad ] ∈ᶜ Γ′
    → Γ at t —[ α ]→ₜ Γ′ at t′
      --——————————————————————————————————————
    → α ≡ auth-init⦅ A , ad , x ⦆
  hᵗ auth∉ auth∈ ([Action] Γ→ _) = h auth∉ auth∈ Γ→
  hᵗ auth∉ auth∈ ([Delay] _) = ⊥-elim $ auth∉ auth∈
  hᵗ auth∉ auth∈ ([Timeout] {c}{t}{v}{x}{Γ}{α}{Γ′}{i} _ _ Γ→ _) =
    h (λ where (there auth∈′) → auth∉ (∈ᶜ-++⁺ʳ (⟨ c , v ⟩at x) Γ auth∈′)) auth∈ Γ→

traceAuthInit :
    A auth[ x ▷ˢ ad ] ∉ᶜ Γ₀
  → A auth[ x ▷ˢ ad ] ∈ᶜ Γ
  → Γ₀ —[ αs ]↠ Γ
    --————————————————————————————
  → auth-init⦅ A , ad , x ⦆ ∈ αs
traceAuthInit auth∉ auth∈ (_ ∎) = ⊥-elim $ auth∉ auth∈

traceAuthInit {A}{x}{ad}{Γ₀}{Γ}{α ∷ αs} auth∉ auth∈ (_—→⟨_⟩_⊢_ .Γ₀ {Γ₀′}{M}{M′}{Γ} Γ₀→M (Γ₀≈ , M≈) M↠)
  = case ¿ A auth[ x ▷ˢ ad ] ∈ᶜ M′ ¿ of λ where
      (yes auth∈M′) → (λ{ refl → here refl }) $ h (∉ᶜ-resp-≈ {Γ₀}{Γ₀′} Γ₀≈ auth∉) auth∈M′ Γ₀→M
      (no  auth∉M′) → there $ traceAuthInit (auth∉M′ ∘ ∈ᶜ-resp-≈ {M}{M′} M≈) auth∈ M↠

traceAuthInitₜ :
    A auth[ x ▷ˢ ad ] ∉ᶜ Γ₀
  → A auth[ x ▷ˢ ad ] ∈ᶜ Γ
  → Γ₀ at t —[ αs ]↠ₜ Γ at t′
    --————————————————————————————
  → auth-init⦅ A , ad , x ⦆ ∈ αs
traceAuthInitₜ auth∉ auth∈ (_ ∎ₜ) = ⊥-elim $ auth∉ auth∈
traceAuthInitₜ {A}{x}{ad}{Γ₀}{Γ}{t}{α ∷ αs}{t′} auth∉ auth∈
  (_—→ₜ⟨_⟩_⊢_ .(Γ₀ at t) {Γ₀′ at _}{M at _}{M′ at _}{Γ at t′} Γ₀→M ((refl , Γ₀≈) , (refl , M≈)) M↠)
  = case ¿ A auth[ x ▷ˢ ad ] ∈ᶜ M′ ¿ of λ where
      (yes auth∈M′) → (λ{ refl → here refl }) $ hᵗ (∉ᶜ-resp-≈ {Γ₀}{Γ₀′} Γ₀≈ auth∉) auth∈M′ Γ₀→M
      (no  auth∉M′) → there $ traceAuthInitₜ (auth∉M′ ∘ ∈ᶜ-resp-≈ {M}{M′} M≈) auth∈ M↠

ℍ[C-AuthInit]⦅_↝_⦆ : Cfg → Cfg → Participant → Ad → Id → Set
ℍ[C-AuthInit]⦅ Γ ↝ Γ′ ⦆ A ad x = ∃ λ Γ₁ → Σ Value λ v → let ⟨ G ⟩ _ = ad; partG = nub-participants G in
    (Γ ≡ ` ad ∣ Γ₁)
  × (Γ′ ≡ ` ad ∣ Γ₁ ∣ A auth[ x ▷ˢ ad ])
    --
  × partG ⊆ committedParticipants ad Γ -- all participants have committed their secrets
  × (A , v , x) ∈ persistentDeposits G -- G = A :! v @ x | ...

auth-init⇒ :
    Γ —[ auth-init⦅ A , ad , x ⦆ ]→ Γ′
    --—————————————————————————————————
  → ℍ[C-AuthInit]⦅ Γ ↝ Γ′ ⦆ A ad x
auth-init⇒ ([C-AuthInit] {Γ = Γ} {v = v} p⊆ A∈) = Γ , v , refl , refl , p⊆ , A∈

auth-init⇒∗ :
    (tr : Γₜ —[ αs ]↠ₜ Γₜ′)
  → auth-init⦅ A , ad , z ⦆ ∈ αs
    --—————————————————————————————
  → ∃ λ x → ∃ λ x′ → ∃ λ y → ∃ λ y′ →
        (x ∈ allStates tr)
      × (y ∈ allStates tr)
      × (x ≈ x′ × y ≈ y′)
      × ℍ[C-AuthInit]⦅ x′ ↝ y′ ⦆ A ad z
auth-init⇒∗ {ad = ad} Γ↠ α∈
  with _ , _ , _ , _ , x∈ , y∈ , ((_ , x≈) , (_ , y≈)) , [Action] Γ→ refl ← zoom Γ↠ α∈
     = -, -, -, -, L.Mem.∈-map⁺ cfg x∈ , L.Mem.∈-map⁺ cfg y∈ , (x≈ , y≈) , auth-init⇒ Γ→
