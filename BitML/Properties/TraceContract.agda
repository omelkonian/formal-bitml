[C-Withdraw] {x}{y}{Γ}{A}{v} _{-# OPTIONS --allow-unsolved-metas #-}
open import Prelude.Init
open import Prelude.DecEq
open import Prelude.Decidable
open import Prelude.Membership
open import Prelude.Bifunctor
open import Prelude.Nary
open import Prelude.Lists
open import Prelude.DecLists
open import Prelude.Validity
open import Prelude.Closures
open import Prelude.Traces

module BitML.Properties.TraceContract
  (Participant : Set) ⦃ _ : DecEq Participant ⦄ (Honest : List⁺ Participant)
  where

open import BitML.BasicTypes
open import BitML.Contracts Participant Honest
open import BitML.Semantics Participant Honest

_∙—[_]↠_ : LRel₀ (Cfg , List Label)
Γ₀ ∙—[ αs ]↠ Γ = Initial Γ × (Γ₀ —[ αs ]↠ Γ)

_∙—[_]↠ₜ_ : LRel₀ (Cfgᵗ , List Label)
Γ₀ ∙—[ αs ]↠ₜ Γ = Initial Γ₀ × (Γ₀ —[ αs ]↠ₜ Γ)

-- record Sub (A : Set) : Set where
--   field
--     subs⁺ : A → Contracts
-- open Sub ⦃...⦄

-- instance
--   Sub-C : Sub Contract
--   Sub-C .subs⁺ = subterms⁺ ∘ Induction.C

--   Sub-CS : Sub Contracts
--   Sub-CS .subs⁺ = subterms⁺ ∘ Induction.CS

--   Sub-VCS : Sub VContracts
--   Sub-VCS .subs⁺ = subterms⁺ ∘ Induction.VCS

-- record Ordℂ (A : Set) : Set where
--   field
--     _≺ᶜ_ : A? → A? → Set

private
  h₁ :
      Γ —[ α ]→ Γ′
    → ⟨ c , v ⟩at x ∈ᶜ Γ′
      --————————————————————————————
    → (∃ λ c′ → ∃ λ v′ → ∃ λ x′ → (⟨ c′ , v′ ⟩at x′ ∈ᶜ Γ) × (c ⊆ subtermsᶜ⁺ c′))
    ⊎ (∃ λ ad → (` ad ∈ᶜ Γ) × (c ⊆ subtermsᶜ′ (C ad)))
  h₁ {c = c}{vᶜ}{xᶜ} ([DEP-AuthJoin] {A}{v}{x}{v′}{y}{Γ} ) c∈ =
    case ∈ᶜ-++⁻ (⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at y ∣ A auth[ x ↔ y ▷⟨ A , v + v′ ⟩ ]) Γ c∈ of λ where
      (inj₁ c∈ˡ) → contradict c∈ˡ
      (inj₂ c∈ʳ) → inj₁ $ c , vᶜ , xᶜ , ∈ᶜ-++⁺ʳ (⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at y) Γ c∈ʳ , {!!}
  --  ,  subtermsᶜ⁺-refl {ds = c}
  h₁ [DEP-Join] c∈ = {!!}
  h₁ [DEP-AuthDivide] c∈ = {!!}
  h₁ [DEP-Divide] c∈ = {!!}
  h₁ [DEP-AuthDonate] c∈ = {!!}
  h₁ [DEP-Donate] c∈ = {!!}
  h₁ [DEP-AuthDestroy] c∈ = {!!}
  h₁ [DEP-Destroy] c∈ = {!!}
  h₁ ([C-Advertise] x x₁ x₂) c∈ = {!!}
  h₁ ([C-AuthCommit] x x₁ x₂) c∈ = {!!}
  h₁ ([C-AuthInit] x x₁) c∈ = {!!}
  h₁ [C-Init] c∈ = {!!}
  h₁ [C-Split] c∈ = {!!}
  h₁ [C-AuthRev] c∈ = {!!}
  h₁ ([C-PutRev] x) c∈ = {!!}
  h₁ [C-Withdraw] c∈ = {!!}
  h₁ ([C-AuthControl] x) c∈ = {!!}
  h₁ ([C-Control] x st x₁) c∈ = {!!}

traceContract :
    Γ₀ ∙—[ αs ]↠ Γ
  → ⟨ c , v ⟩at x ∈ᶜ Γ
    --————————————————————————————
  -- → ⟨ c , v ⟩at x ∈ᶜ Γ\
  → ∃ λ ad → ∃ λ Γ′ → ∃ λ αsˡ → ∃ λ αsʳ →
       (Γ₀ ∙—[ αsˡ ]↠ Γ′)
     × (` ad ∈ᶜ Γ′)
     × (Γ′ —[ αsʳ ]↠ Γ)
     × (c ⊆ subtermsᶜ′ (C ad))
traceContract = {!!}
-- h (fst , (_ ∎)) c∈ = {!!}
-- h (fst , (_ —→⟨ [DEP-AuthJoin] ⟩ x₁ ⊢ snd)) c∈ = {!!}
-- h (fst , (_ —→⟨ [DEP-Join] ⟩ x₁ ⊢ snd)) c∈ = {!!}
-- h (fst , (_ —→⟨ [DEP-AuthDivide] ⟩ x₁ ⊢ snd)) c∈ = {!!}
-- h (fst , (_ —→⟨ [DEP-Divide] ⟩ x₁ ⊢ snd)) c∈ = {!!}
-- h (fst , (_ —→⟨ [DEP-AuthDonate] ⟩ x₁ ⊢ snd)) c∈ = {!!}
-- h (fst , (_ —→⟨ [DEP-Donate] ⟩ x₁ ⊢ snd)) c∈ = {!!}
-- h (fst , (_ —→⟨ [DEP-AuthDestroy] ⟩ x₁ ⊢ snd)) c∈ = {!!}
-- h (fst , (_ —→⟨ [DEP-Destroy] ⟩ x₁ ⊢ snd)) c∈ = {!!}
-- h (fst , (_ —→⟨ [C-Advertise] x x₂ x₃ ⟩ x₁ ⊢ snd)) c∈ = {!!}
-- h (fst , (_ —→⟨ [C-AuthCommit] x x₂ x₃ ⟩ x₁ ⊢ snd)) c∈ = {!!}
-- h (fst , (_ —→⟨ [C-AuthInit] x x₂ ⟩ x₁ ⊢ snd)) c∈ = {!!}
-- h (fst , (_ —→⟨ [C-Init] ⟩ x₁ ⊢ snd)) c∈ = {!!}
-- h (fst , (_ —→⟨ [C-Split] ⟩ x₁ ⊢ snd)) c∈ = {!!}
-- h (fst , (_ —→⟨ [C-AuthRev] ⟩ x₁ ⊢ snd)) c∈ = {!!}
-- h (fst , (_ —→⟨ [C-PutRev] x ⟩ x₁ ⊢ snd)) c∈ = {!!}
-- h (fst , (_ —→⟨ [C-Withdraw] ⟩ x₁ ⊢ snd)) c∈ = {!!}
-- h (fst , (_ —→⟨ [C-AuthControl] x ⟩ x₁ ⊢ snd)) c∈ = {!!}
-- h (fst , (_ —→⟨ [C-Control] x x₂ x₃ ⟩ x₁ ⊢ snd)) c∈ = {!!}

-- -- ¬Control :
-- --     ` ad ∉ᶜ Γ
-- --   → (step : Γ —[ α ]→ Γ′)
-- --   → {ctrl : isControl step}
-- --     --————————————————————————————————————
-- --   → ` ad ∉ᶜ innerL step {ctrl}
-- -- ¬Control {ad}
-- --   {Γ = .(⟨ c , v ⟩at x ∣ || map _auth[ x ▷ (c ‼ i) ] (nub $ authDecorations (c ‼ i)) ∣ Γ)}
-- --   {α}{Γ′}
-- --   ad∉ ([C-Control] {c}{v}{x}{Γ}{L}{.α}{.Γ′}{i} ≈L _ _)
-- --   = ad∉L
-- --   where
-- --     d_ = c ‼ i
-- --     d∗ = removeTopDecorations d_

-- --     S₀ = ⟨ c , v ⟩at x ∣ || map _auth[ x ▷ d_ ] (nub $ authDecorations d_)
-- --     S  = S₀ ∣ Γ
-- --     S′ = Γ′

-- --     ad∉Γ′ : ` ad ∉ᶜ Γ
-- --     ad∉Γ′ ad∈Γ = ad∉ $ ∈ᶜ-++⁺ʳ S₀ Γ ad∈Γ

-- --     ad∉L : ` ad ∉ᶜ L
-- --     ad∉L ad∈L with L.Mem.∈-++⁻ [ ⟨ [ d∗ ] , v ⟩at x ] (∈ᶜ-resp-≈ {L}{⟨ [ d∗ ] , v ⟩at x ∣ Γ} (↭-sym ≈L) ad∈L)
-- --     ... | inj₁ (here ())
-- --     ... | inj₂ ad∈Γ′ = ad∉Γ′ ad∈Γ′

-- -- ¬AuthJoin :
-- --     ` ad ∉ᶜ Γ
-- --   → Γ —[ auth-join⦅ A , x ↔ y ⦆ ]→ Γ′
-- --     --————————————————————————————————————
-- --   → ` ad ∉ᶜ Γ′
-- -- ¬AuthJoin ad∉ step@([C-Control] _ L→Γ′ _) = ¬AuthJoin (¬Control ad∉ step) L→Γ′
-- -- ¬AuthJoin ad∉ ([DEP-AuthJoin] {A}{v}{x}{v′}{y}{Γ}) ad∈
-- --   with L.Mem.∈-++⁻ (cfgToList $ ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at y ∣ A auth[ x ↔ y ▷⟨ A , v + v′ ⟩ ]) ad∈
-- -- ... | inj₁ ad∈ˡ = case ad∈ˡ of λ where
-- --   (here ())
-- --   (there (here ()))
-- --   (there (there (here ())))
-- -- ... | inj₂ ad∈Γ = ad∉ $ L.Mem.∈-++⁺ʳ (cfgToList $ ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at y) ad∈Γ

-- -- ¬Join :
-- --     ` ad ∉ᶜ Γ
-- --   → Γ —[ join⦅ x ↔ y ⦆ ]→ Γ′
-- --     --————————————————————————————————————
-- --   → ` ad ∉ᶜ Γ′
-- -- ¬Join ad∉ step@([C-Control] _ L→Γ′ _) = ¬Join (¬Control ad∉ step) L→Γ′
-- -- ¬Join ad∉ ([DEP-Join] {A}{v}{x}{v′}{y}{Γ}{z}) ad∈
-- --   with L.Mem.∈-++⁻ [ ⟨ A has v + v′ ⟩at z ] ad∈
-- -- ... | inj₁ (here ())
-- -- ... | inj₂ ad∈Γ = ad∉ $ L.Mem.∈-++⁺ʳ (cfgToList $ ⟨ A has v ⟩at x ∣ ⟨ A has v′ ⟩at y ∣ A auth[ x ↔ y ▷⟨ A , v + v′ ⟩ ]) ad∈Γ

-- -- ¬AuthDivide :
-- --     ` ad ∉ᶜ Γ
-- --   → Γ —[ auth-divide⦅ A , x ▷ v , v′ ⦆ ]→ Γ′
-- --     --————————————————————————————————————
-- --   → ` ad ∉ᶜ Γ′
-- -- ¬AuthDivide ad∉ step@([C-Control] _ L→Γ′ _) = ¬AuthDivide (¬Control ad∉ step) L→Γ′
-- -- ¬AuthDivide ad∉ ([DEP-AuthDivide] {A}{v}{v′}{x}{Γ}) ad∈
-- --   with L.Mem.∈-++⁻ (cfgToList $ ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ]) ad∈
-- -- ... | inj₁ ad∈ˡ = case ad∈ˡ of λ where
-- --   (here ())
-- --   (there (here ()))
-- -- ... | inj₂ ad∈Γ = ad∉ $ L.Mem.∈-++⁺ʳ (cfgToList $ ⟨ A has (v + v′) ⟩at x) ad∈Γ

-- -- ¬Divide :
-- --     ` ad ∉ᶜ Γ
-- --   → Γ —[ divide⦅ x ▷ v , v′ ⦆ ]→ Γ′
-- --     --————————————————————————————————————
-- --   → ` ad ∉ᶜ Γ′
-- -- ¬Divide ad∉ step@([C-Control] _ L→Γ′ _) = ¬Divide (¬Control ad∉ step) L→Γ′
-- -- ¬Divide ad∉ ([DEP-Divide] {x}{Γ}{y}{y′}{A}{v}{v′} _) ad∈
-- --   with L.Mem.∈-++⁻ (cfgToList $ ⟨ A has v ⟩at y ∣ ⟨ A has v′ ⟩at y′) ad∈
-- -- ... | inj₁ ad∈ˡ = case ad∈ˡ of λ where
-- --   (here ())
-- --   (there (here ()))
-- -- ... | inj₂ ad∈Γ = ad∉ $ L.Mem.∈-++⁺ʳ (cfgToList $ ⟨ A has (v + v′) ⟩at x ∣ A auth[ x ▷⟨ A , v , v′ ⟩ ]) ad∈Γ

-- -- ¬AuthDonate :
-- --     ` ad ∉ᶜ Γ
-- --   → Γ —[ auth-donate⦅ A , x ▷ᵈ B ⦆ ]→ Γ′
-- --     --————————————————————————————————————
-- --   → ` ad ∉ᶜ Γ′
-- -- ¬AuthDonate ad∉ step@([C-Control] _ L→Γ′ _) = ¬AuthDonate (¬Control ad∉ step) L→Γ′
-- -- ¬AuthDonate ad∉ ([DEP-AuthDonate] {A}{v}{x}{Γ}{B}) =
-- --   L.Mem.∈-++⁻ (cfgToList $ ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B ]) >≡>
-- --   Sum.[ (λ{ (here ()); (there (here ())) })
-- --       , ad∉ ∘ L.Mem.∈-++⁺ʳ [ ⟨ A has v ⟩at x ]
-- --       ]

-- -- ¬Donate :
-- --     ` ad ∉ᶜ Γ
-- --   → Γ —[ donate⦅ x ▷ᵈ B ⦆ ]→ Γ′
-- --     --————————————————————————————————————
-- --   → ` ad ∉ᶜ Γ′
-- -- ¬Donate ad∉ step@([C-Control] _ L→Γ′ _) = ¬Donate (¬Control ad∉ step) L→Γ′
-- -- ¬Donate ad∉ ([DEP-Donate] {A}{v}{x}{B}{Γ}{y}) =
-- --   L.Mem.∈-++⁻ [ ⟨ B has v ⟩at y ] >≡>
-- --   Sum.[ (λ{ (here ()) })
-- --       , ad∉ ∘ L.Mem.∈-++⁺ʳ (cfgToList $ ⟨ A has v ⟩at x ∣ A auth[ x ▷ᵈ B ])
-- --       ]

-- -- ¬AuthDestroy : ∀ {xs} {j′ : Index xs}
-- --   → ` ad ∉ᶜ Γ
-- --   → Γ —[ auth-destroy⦅ A , xs , j′ ⦆ ]→ Γ′
-- --     --————————————————————————————————————
-- --   → ` ad ∉ᶜ Γ′
-- -- ¬AuthDestroy ad∉ step@([C-Control] _ L→Γ′ _) = ¬AuthDestroy (¬Control ad∉ step) L→Γ′
-- -- ¬AuthDestroy ad∉ ([DEP-AuthDestroy] {Γ}{y}{ds}{j}) =
-- --   let xs = map select₃ ds
-- --       Aj = proj₁ (ds ‼ j)
-- --       j′ = ‼-map {xs = ds} j
-- --       Δ  = || map (uncurry₃ ⟨_has_⟩at_) ds
-- --   in
-- --   ∈ᶜ-++⁻ (Δ ∣ Aj auth[ xs , j′ ▷ᵈˢ y ]) Γ >≡>
-- --   Sum.[ (∈ᶜ-++⁻ Δ (Aj auth[ xs , j′ ▷ᵈˢ y ]) >≡>
-- --          Sum.[ ad∉ ∘ ∈ᶜ-++⁺ˡ Δ Γ
-- --              , (λ{ (here ()) })
-- --              ])
-- --       , ad∉ ∘ ∈ᶜ-++⁺ʳ Δ Γ
-- --       ]

-- -- ¬Destroy :
-- --     ` ad ∉ᶜ Γ
-- --   → Γ —[ destroy⦅ xs ⦆ ]→ Γ′
-- --     --————————————————————————————————————
-- --   → ` ad ∉ᶜ Γ′
-- -- ¬Destroy ad∉ step@([C-Control] _ L→Γ′ _) = ¬Destroy (¬Control ad∉ step) L→Γ′
-- -- ¬Destroy ad∉ ([DEP-Destroy] {y}{Γ}{ds}) =
-- --   let xs = map select₃ ds
-- --       Δ  = || map (λ{ (i , Ai , vi , xi) → ⟨ Ai has vi ⟩at xi ∣ Ai auth[ xs , ‼-map {xs = ds} i ▷ᵈˢ y ] })
-- --                   (enumerate ds)
-- --   in ad∉ ∘ ∈ᶜ-++⁺ʳ Δ Γ

-- -- ¬Advertise :
-- --     ` ad ∉ᶜ Γ
-- --   → ad ≢ ad′
-- --   → Γ —[ advertise⦅ ad′ ⦆ ]→ Γ′
-- --     --————————————————————————————————————
-- --   → ` ad ∉ᶜ Γ′
-- -- ¬Advertise ad∉ ad≢ step@([C-Control] _ L→Γ′ _) = ¬Advertise (¬Control ad∉ step) ad≢ L→Γ′
-- -- ¬Advertise {ad′ = ad′} ad∉ ad≢ ([C-Advertise] {ad = .ad′}{Γ} vad hon⁺ d⊆) =
-- --   ∈ᶜ-++⁻ (` ad′) Γ >≡>
-- --   Sum.[ (λ{ (here refl) → ⊥-elim $ ad≢ refl })
-- --       , ad∉
-- --       ]

-- -- ¬AuthCommit : ∀ {secrets : List (Secret × Maybe ℕ)}
-- --   → ` ad ∉ᶜ Γ
-- --   → Γ —[ auth-commit⦅ A , ad′ , secrets ⦆ ]→ Γ′
-- --     --————————————————————————————————————
-- --   → ` ad ∉ᶜ Γ′
-- -- ¬AuthCommit ad∉ step@([C-Control] _ L→Γ′ _) = ¬AuthCommit (¬Control ad∉ step) L→Γ′
-- -- ¬AuthCommit ad∉ ([C-AuthCommit] {ad}{A}{Γ}{secrets} _ _ _) =
-- --   let (as , ms) = unzip secrets
-- --       Δ         = || map (uncurry ⟨ A ∶_♯_⟩) secrets
-- --   in
-- --   ∈ᶜ-++⁻ (` ad ∣ Γ ∣ Δ) (A auth[ ♯▷ ad ]) >≡>
-- --   Sum.[ ∈ᶜ-++⁻ (` ad ∣ Γ) Δ >≡>
-- --         Sum.[ ad∉
-- --             , ∉ᶜ-|| {f = uncurry ⟨ A ∶_♯_⟩} (λ{ (here ()); (there ())}) secrets
-- --             ]
-- --       , (λ{ (here ()) })
-- --       ]

-- -- ¬AuthInit :
-- --     ` ad ∉ᶜ Γ
-- --   → Γ —[ auth-init⦅ A , ad′ , x ⦆ ]→ Γ′
-- --     --————————————————————————————————————
-- --   → ` ad ∉ᶜ Γ′
-- -- ¬AuthInit ad∉ step@([C-Control] _ L→Γ′ _) = ¬AuthInit (¬Control ad∉ step) L→Γ′
-- -- ¬AuthInit ad∉ ([C-AuthInit] {ad}{Γ}{A}{x = x} _ _) =
-- --   ∈ᶜ-++⁻ (` ad ∣ Γ) (A auth[ x ▷ˢ ad ]) >≡>
-- --   Sum.[ ad∉
-- --       , (λ{ (here ()) })
-- --       ]

-- -- ¬Init : let ⟨ G ⟩ C = ad′ in
-- --     ` ad ∉ᶜ Γ
-- --   → Γ —[ init⦅ G , C ⦆ ]→ Γ′
-- --     --————————————————————————————————————
-- --   → ` ad ∉ᶜ Γ′
-- -- ¬Init ad∉ step@([C-Control] _ L→Γ′ _) = ¬Init (¬Control ad∉ step) L→Γ′
-- -- ¬Init ad∉ ([C-Init] {ad}{Γ}{x}) =
-- --   let toSpend = persistentDeposits $ G ad
-- --       vs      = map (proj₁ ∘ proj₂) toSpend

-- --       Δ₁ = || map (λ{ (Ai , vi , xi) → ⟨ Ai has vi ⟩at xi ∣ Ai auth[ xi ▷ˢ ad ] }) toSpend
-- --       Δ₂ = || map _auth[ ♯▷ ad ] (nub-participants $ ad .G)
-- --   in
-- --   L.Mem.∈-++⁻ [ ⟨ C ad , sum vs ⟩at x ] >≡>
-- --   Sum.[ (λ{ (here ()) })
-- --       , ad∉ ∘ ∈ᶜ-++⁺ˡ (` ad ∣ Γ ∣ Δ₁) Δ₂
-- --             ∘ ∈ᶜ-++⁺ˡ (` ad ∣ Γ) Δ₁
-- --             ∘ ∈ᶜ-++⁺ʳ (` ad) Γ
-- --       ]

-- -- ¬Split :
-- --     ` ad ∉ᶜ Γ
-- --   → Γ —[ split⦅ y ⦆ ]→ Γ′
-- --     --————————————————————————————————————
-- --   → ` ad ∉ᶜ Γ′
-- -- ¬Split ad∉ step@([C-Control] _ L→Γ′ _) = ¬Split (¬Control ad∉ step) L→Γ′
-- -- ¬Split ad∉ ([C-Split] {y}{Γ}{vcis}) =
-- --   let (vs , cs , _) = unzip₃ vcis in
-- --   ∈ᶜ-++⁻ (|| map (uncurry₃ $ flip ⟨_,_⟩at_) vcis) Γ >≡>
-- --   Sum.[ ∉ᶜ-|| {f = uncurry₃ $ flip ⟨_,_⟩at_} (λ{ (here ()) }) vcis
-- --       , ad∉ ∘ L.Mem.∈-++⁺ʳ [ ⟨ [ split (zip vs cs) ] , sum vs ⟩at y ]
-- --       ]

-- -- ¬AuthRev :
-- --     ` ad ∉ᶜ Γ
-- --   → Γ —[ auth-rev⦅ A , a ⦆ ]→ Γ′
-- --     --————————————————————————————————————
-- --   → ` ad ∉ᶜ Γ′
-- -- ¬AuthRev ad∉ step@([C-Control] _ L→Γ′ _) = ¬AuthRev (¬Control ad∉ step) L→Γ′
-- -- ¬AuthRev ad∉ ([C-AuthRev] {A}{a}{n}{Γ}) =
-- --   L.Mem.∈-++⁻ [ A ∶ a ♯ n ] >≡>
-- --   Sum.[ (λ{ (here ()) })
-- --       , ad∉ ∘ L.Mem.∈-++⁺ʳ [ ⟨ A ∶ a ♯ just n ⟩ ]
-- --       ]

-- -- ¬PutRev :
-- --     ` ad ∉ᶜ Γ
-- --   → Γ —[ put⦅ xs , as , y ⦆ ]→ Γ′
-- --     --————————————————————————————————————
-- --   → ` ad ∉ᶜ Γ′
-- -- ¬PutRev ad∉ step@([C-Control] _ L→Γ′ _) = ¬PutRev (¬Control ad∉ step) L→Γ′
-- -- ¬PutRev ad∉ ([C-PutRev] {Γ′}{p}{c}{v}{y}{z}{ds}{ss} _) =
-- --   let (_ , vs , xs) = unzip₃ ds
-- --       (_ , as , _)  = unzip₃ ss
-- --       Γ = || map (uncurry₃ ⟨_has_⟩at_) ds
-- --       Δ = || map (uncurry₃ _∶_♯_) ss
-- --       ΔΓ′ = Δ ∣ Γ′
-- --   in
-- --   L.Mem.∈-++⁻ [ ⟨ c , v + sum vs ⟩at z ] >≡>
-- --   Sum.[ (λ{ (here ()) })
-- --       , ad∉ ∘ L.Mem.∈-++⁺ʳ [ ⟨ [ put xs &reveal as if p ⇒ c ] , v ⟩at y ] ∘ ∈ᶜ-++⁺ʳ Γ ΔΓ′
-- --       ]

-- -- ¬Withdraw :
-- --     ` ad ∉ᶜ Γ
-- --   → Γ —[ withdraw⦅ A , v , y ⦆ ]→ Γ′
-- --     --————————————————————————————————————
-- --   → ` ad ∉ᶜ Γ′
-- -- ¬Withdraw ad∉ step@([C-Control] _ L→Γ′ _) = ¬Withdraw (¬Control ad∉ step) L→Γ′
-- -- ¬Withdraw ad∉ ([C-Withdraw] {A}{v}{y}{Γ}{x}) =
-- --   L.Mem.∈-++⁻ [ ⟨ A has v ⟩at x ] >≡>
-- --   Sum.[ (λ{ (here ()) })
-- --       , ad∉ ∘ L.Mem.∈-++⁺ʳ [ ⟨ [ withdraw A ] , v ⟩at y ]
-- --       ]

-- -- ¬AuthControl :
-- --     ` ad ∉ᶜ Γ
-- --   → Γ —[ auth-control⦅ A , x ▷ d ⦆ ]→ Γ′
-- --     --————————————————————————————————————
-- --   → ` ad ∉ᶜ Γ′
-- -- ¬AuthControl ad∉ step@([C-Control] _ L→Γ′ _) = ¬AuthControl (¬Control ad∉ step) L→Γ′
-- -- ¬AuthControl ad∉ ([C-AuthControl] {c}{A}{v}{x}{Γ}{i} _) =
-- --   let d = c ‼ i in
-- --   L.Mem.∈-++⁻ (cfgToList $ ⟨ c , v ⟩at x ∣ A auth[ x ▷ d ]) >≡>
-- --   Sum.[ (λ{ (here ()); (there (here ())) })
-- --       , ad∉ ∘ L.Mem.∈-++⁺ʳ [ ⟨ c , v ⟩at x ]
-- --       ]

-- -- ¬Delay : Γ —[ delay⦅ δ ⦆ ]↛ Γ′
-- -- ¬Delay ([C-Control] _ _ cv≡) = contradict cv≡

-- -- h₂ :
-- --     ` ad ∉ᶜ Γ
-- --   → ` ad ∈ᶜ Γ′
-- --   → Γ —[ α ]→ Γ′
-- --     --————————————————————————————
-- --   → (α ≡ advertise⦅ ad ⦆)
-- --   × Valid ad
-- -- h₂ {ad}{Γ}{Γ′}{α} ad∉ ad∈ step
-- --   with α
-- -- ... | auth-join⦅ _ , _ ↔ _ ⦆       = ⊥-elim $ ¬AuthJoin ad∉ step ad∈
-- -- ... | join⦅ _ ↔ _ ⦆                = ⊥-elim $ ¬Join ad∉ step ad∈
-- -- ... | auth-divide⦅ _ , _ ▷ _ , _ ⦆ = ⊥-elim $ ¬AuthDivide ad∉ step ad∈
-- -- ... | divide⦅ _ ▷ _ , _ ⦆          = ⊥-elim $ ¬Divide ad∉ step ad∈
-- -- ... | auth-donate⦅ _ , _ ▷ᵈ _ ⦆    = ⊥-elim $ ¬AuthDonate ad∉ step ad∈
-- -- ... | donate⦅ _ ▷ᵈ _ ⦆             = ⊥-elim $ ¬Donate ad∉ step ad∈
-- -- ... | auth-destroy⦅ _ , _ , _ ⦆    = ⊥-elim $ ¬AuthDestroy ad∉ step ad∈
-- -- ... | destroy⦅ _ ⦆                 = ⊥-elim $ ¬Destroy ad∉ step ad∈
-- -- ... | auth-commit⦅ _ , _ , _ ⦆     = ⊥-elim $ ¬AuthCommit ad∉ step ad∈
-- -- ... | auth-init⦅ _ , _ , _ ⦆       = ⊥-elim $ ¬AuthInit ad∉ step ad∈
-- -- ... | init⦅ _ , _ ⦆                = ⊥-elim $ ¬Init ad∉ step ad∈
-- -- ... | split⦅ _ ⦆                   = ⊥-elim $ ¬Split ad∉ step ad∈
-- -- ... | auth-rev⦅ _ , _ ⦆            = ⊥-elim $ ¬AuthRev ad∉ step ad∈
-- -- ... | put⦅ _ , _ , _ ⦆             = ⊥-elim $ ¬PutRev ad∉ step ad∈
-- -- ... | withdraw⦅ _ , _ , _ ⦆        = ⊥-elim $ ¬Withdraw ad∉ step ad∈
-- -- ... | auth-control⦅ _ , _ ▷ _ ⦆    = ⊥-elim $ ¬AuthControl ad∉ step ad∈
-- -- ... | delay⦅ _ ⦆                   = ⊥-elim $ ¬Delay step
-- -- ... | advertise⦅ ad′ ⦆
-- --   with ad ≟ ad′
-- -- ... | no  ad≢  = ⊥-elim $ ¬Advertise ad∉ ad≢ step ad∈
-- -- ... | yes refl = case step of λ{ ([C-Advertise] {ad = .ad} vad _ _) → refl , vad }

-- -- h :
-- --     Initial Γ₀
-- --   → Γ₀ —[ αs ]↠ Γ
-- --     --————————————————————————————
-- --   → (advertise⦅ ad ⦆ ∈ αs)
-- --   × Valid ad
-- -- h ad∉ ad∈ (_ ∎) = ⊥-elim $ ad∉ ad∈

-- -- h {ad}{Γ₀}{Γ}{α ∷ αs} ad∉ ad∈ (_—→⟨_⟩_⊢_ .Γ₀ {Γ₀′}{M}{M′}{Γ} Γ₀→M (Γ₀≈Γ₀′ , M≈M′) M↠)
-- --   = case ¿ ` ad ∈ᶜ M′ ¿ of λ where
-- --       (yes ad∈M′) → map₁ (λ{ refl → here refl }) $ h₂ ad∉′ ad∈M′ Γ₀→M
-- --       (no  ad∉M′) → map₁ there $ h (ad∉M′ ∘ ∈ᶜ-resp-≈ {M}{M′} M≈M′) ad∈ M↠
-- --   where
-- --     ad∉′ : ` ad ∉ᶜ Γ₀′
-- --     ad∉′ = ad∉ ∘ ∈ᶜ-resp-≈ {Γ₀′}{Γ₀} (↭-sym Γ₀≈Γ₀′)
