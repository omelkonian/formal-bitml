open import Prelude.Init; open SetAsType
open import Prelude.Lists
open import Prelude.DecEq
open import Prelude.Lists.Dec
open import Prelude.Nary
open import Prelude.InferenceRules
open import Prelude.Setoid

open import BitML.BasicTypes

module BitML.Properties.Invariants (⋯ : ⋯) where

open import BitML.Contracts ⋯
open import BitML.Semantics ⋯

open import Prelude.General

private variable X : Type ℓ

private
  𝒫 : Pred₀ Cfg
  𝒫 = Unique ∘ names

  𝒫≈ : Γ ≈ Γ′ → 𝒫 Γ → 𝒫 Γ′
  𝒫≈ {Γ}{Γ′} = Unique-resp-↭ ∘ ≈⇒names↭ {Γ}{Γ′}

  Control :
    ∙ 𝒫 Γ
    → ∀ (step : Γ —[ α ]→ Γ′)
      {ctrl : isControl step} →
      ─────────────────────────────────
      𝒫 Γ′
  Control
    {Γ = .( ⟨ c , v ⟩at x
          ∣ || map _auth[ x ▷ (c ‼ i) ] (nub $ authDecorations (c ‼ i))
          ∣ Γ
          )}
    {α}{Γ′}
    IH ([C-Control] {c}{Γ}{L}{v}{x}{.α}{.Γ′}{i} _ ≈L _ _)
    = {!IH!}

--   AuthJoin :
--     ∙ 𝒫 Γ
--     ∙ Γ —[ auth-join⦅ A , x ↔ y ⦆ ]→ Γ′
--       ─────────────────────────────────
--       𝒫 Γ′
--   AuthJoin IH [DEP-AuthJoin] = IH

--   Join :
--     ∙ 𝒫 Γ
--     ∙ Γ —[ join⦅ x ↔ y ⦆ ]→ Γ′
--       ─────────────────────────────────
--       𝒫 Γ′
--   Join IH ([DEP-Join] {z}{x}{y}{Γ}{A}{v}{v′} fresh-z) =
--     {!!} ∷ {! IH!}

--   AuthDivide :
--     ∙ 𝒫 Γ
--     ∙ Γ —[ auth-divide⦅ A , x ▷ v , v′ ⦆ ]→ Γ′
--       ─────────────────────────────────
--       𝒫 Γ′
--   AuthDivide IH ([DEP-AuthDivide] {A}{v}{v′}{x}{Γ}) =
--     IH

--   Divide :
--     ∙ 𝒫 Γ
--     ∙ Γ —[ divide⦅ x ▷ v , v′ ⦆ ]→ Γ′
--       ─────────────────────────────────
--       𝒫 Γ′
--   Divide IH ([DEP-Divide] {x}{Γ}{y}{y′}{A}{v}{v′} _) =
--     {!IH!}


--   AuthDonate :
--     ∙ 𝒫 Γ
--     ∙ Γ —[ auth-donate⦅ A , x ▷ᵈ B ⦆ ]→ Γ′
--       ─────────────────────────────────
--       𝒫 Γ′
--   AuthDonate IH ([DEP-AuthDonate] {A}{v}{x}{Γ}{B}) =
--     IH

--   Donate :
--     ∙ 𝒫 Γ
--     ∙ Γ —[ donate⦅ x ▷ᵈ B ⦆ ]→ Γ′
--       ─────────────────────────────────
--       𝒫 Γ′
--   Donate IH ([DEP-Donate] {y}{x}{Γ}{A}{v}{B} _) =
--     {!IH!}

--   AuthDestroy : ∀ {xs} {j′ : Index xs} →
--     ∙ 𝒫 Γ
--     ∙ Γ —[ auth-destroy⦅ A , xs , j′ ⦆ ]→ Γ′
--       ─────────────────────────────────
--       𝒫 Γ′
--   AuthDestroy IH ([DEP-AuthDestroy] {y}{Γ}{ds}{j} _) =
--     let xs = map select₃ ds
--         Aj = proj₁ (ds ‼ j)
--         j′ = ‼-map {xs = ds} j
--         Δ  = || map (uncurry₃ ⟨_has_⟩at_) ds
--     in
--     {!IH!}

--   Destroy :
--     ∙ 𝒫 Γ
--     ∙ Γ —[ destroy⦅ xs ⦆ ]→ Γ′
--       ─────────────────────────────────
--       𝒫 Γ′
--   Destroy IH ([DEP-Destroy] {y}{Γ}{ds}) =
--     let xs = map select₃ ds
--         Δ  = || map (λ{ (i , Ai , vi , xi) → ⟨ Ai has vi ⟩at xi ∣ Ai auth[ xs , ‼-map {xs = ds} i ▷ᵈˢ y ] })
--                     (enumerate ds)
--     in {!IH!}

--   Advertise :
--     ∙ 𝒫 Γ
--     ∙ Γ —[ advertise⦅ ad′ ⦆ ]→ Γ′
--       ─────────────────────────────────
--       𝒫 Γ′
--   Advertise IH ([C-Advertise] {ad = ad}{Γ} vad hon⁺ d⊆) =
--     IH

--   AuthCommit : ∀ {secrets : List (Secret × Maybe ℕ)} →
--     ∙ 𝒫 Γ
--     ∙ Γ —[ auth-commit⦅ A , ad′ , secrets ⦆ ]→ Γ′
--       ─────────────────────────────────
--       𝒫 Γ′
--   AuthCommit IH ([C-AuthCommit] {ad}{A}{Γ}{secrets} _ _ _) =
--     let (as , ms) = unzip secrets
--         Δ         = || map (uncurry ⟨ A ∶_♯_⟩) secrets
--     in
--     {!IH!}

--   AuthInit :
--     ∙ 𝒫 Γ
--     ∙ Γ —[ auth-init⦅ A , ad′ , x ⦆ ]→ Γ′
--       ─────────────────────────────────
--       𝒫 Γ′
--   AuthInit IH ([C-AuthInit] {ad}{Γ}{A}{x = x} _ _) =
--     {!IH!}

--   Init : let ⟨ G ⟩ C = ad′ in
--     ∙ 𝒫 Γ
--     ∙ Γ —[ init⦅ G , C ⦆ ]→ Γ′
--       ─────────────────────────────────
--       𝒫 Γ′
--   Init IH ([C-Init] {ad}{x}{Γ} _) =
--     let toSpend = persistentDeposits $ G ad
--         vs      = map (proj₁ ∘ proj₂) toSpend

--         Δ₁ = || map (λ{ (Ai , vi , xi) → ⟨ Ai has vi ⟩at xi ∣ Ai auth[ xi ▷ˢ ad ] }) toSpend
--         Δ₂ = || map _auth[ ♯▷ ad ] (nub-participants $ ad .G)
--     in
--     {!IH!}

--   Split :
--     ∙ 𝒫 Γ
--     ∙ Γ —[ split⦅ y ⦆ ]→ Γ′
--       ─────────────────────────────────
--       𝒫 Γ′
--   Split IH step@([C-Control] _ _ _ _) = Control IH step
--   Split IH ([C-Split] {y}{Γ}{vcis} _) =
--     let (vs , cs , _) = unzip₃ vcis in
--     {!IH!}

--   AuthRev :
--     ∙ 𝒫 Γ
--     ∙ Γ —[ auth-rev⦅ A , a ⦆ ]→ Γ′
--       ─────────────────────────────────
--       𝒫 Γ′
--   AuthRev IH ([C-AuthRev] {A}{a}{n}{Γ}) =
--     IH

--   PutRev :
--     ∙ 𝒫 Γ
--     ∙ Γ —[ put⦅ xs , as , y ⦆ ]→ Γ′
--       ─────────────────────────────────
--       𝒫 Γ′
--   PutRev IH step@([C-Control] _ _ _ _) = Control IH step
--   PutRev IH ([C-PutRev] {Γ′}{z}{y}{p}{c}{v} {ds}{ss} _ _) =
--     let (_ , vs , xs) = unzip₃ ds
--         (_ , as , _)  = unzip₃ ss
--         Γ = || map (uncurry₃ ⟨_has_⟩at_) ds
--         Δ = || map (uncurry₃ _∶_♯_) ss
--         ΔΓ′ = Δ ∣ Γ′
--     in
--     {!!}

--   Withdraw :
--     ∙ 𝒫 Γ
--     ∙ Γ —[ withdraw⦅ A , v , y ⦆ ]→ Γ′
--       ─────────────────────────────────
--       𝒫 Γ′
--   Withdraw IH step@([C-Control] _ _ L→Γ′ _) = Control IH step
--   Withdraw (_ ∷ IH) ([C-Withdraw] {x}{y}{Γ}{A}{v} fresh-x) =
--     L.All.¬Any⇒All¬ (names Γ) (λ x∈ → fresh-x (there (∈-mapMaybe⁺ isInj₂ x∈ refl))) ∷ IH

--   AuthControl :
--     ∙ 𝒫 Γ
--     ∙ Γ —[ auth-control⦅ A , x ▷ d ⦆ ]→ Γ′
--       ─────────────────────────────────
--       𝒫 Γ′
--   AuthControl IH ([C-AuthControl] {c}{A}{v}{x}{Γ}{i} _) =
--     IH

-- Unique-invariant :
--   ∙ 𝒫 Γ
--   ∙ Γ —→ Γ′
--     ───────
--     𝒫 Γ′
-- Unique-invariant IH (α , Γ→) with α
-- ... | auth-join⦅ _ , _ ↔ _ ⦆       = AuthJoin IH Γ→
-- ... | join⦅ _ ↔ _ ⦆                = Join IH Γ→
-- ... | auth-divide⦅ _ , _ ▷ _ , _ ⦆ = AuthDivide IH Γ→
-- ... | divide⦅ _ ▷ _ , _ ⦆          = Divide IH Γ→
-- ... | auth-donate⦅ _ , _ ▷ᵈ _ ⦆    = AuthDonate IH Γ→
-- ... | donate⦅ _ ▷ᵈ _ ⦆             = Donate IH Γ→
-- ... | auth-destroy⦅ _ , _ , _ ⦆    = AuthDestroy IH Γ→
-- ... | destroy⦅ _ ⦆                 = Destroy IH Γ→
-- ... | advertise⦅ _ ⦆               = Advertise IH Γ→
-- ... | auth-commit⦅ _ , _ , _ ⦆     = AuthCommit IH Γ→
-- ... | auth-init⦅ _ , _ , _ ⦆       = AuthInit IH Γ→
-- ... | init⦅ _ , _ ⦆                = Init IH Γ→
-- ... | split⦅ _ ⦆                   = Split IH Γ→
-- ... | auth-rev⦅ _ , _ ⦆            = AuthRev IH Γ→
-- ... | put⦅ _ , _ , _ ⦆             = PutRev IH Γ→
-- ... | withdraw⦅ _ , _ , _ ⦆        = Withdraw IH Γ→
-- ... | auth-control⦅ _ , _ ▷ _ ⦆    = AuthControl IH Γ→
-- ... | delay⦅ _ ⦆                   = case Γ→ of λ where ([C-Control] _ _ _ ())
