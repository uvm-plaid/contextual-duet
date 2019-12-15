{-# OPTIONS --allow-unsolved-metas #-}
module proof where

open import rules public
open import lemmas public
open import logical-relations public

-- Theorem 1.1.1 (Fundamental Property / (Metric Preservation in Fuzz)).

change-Σ-𝒱 : ∀ {t t′ : τ ᴢ} {v₁ v₂ : 𝓋} {s : Sens} (⊢v₁ : ⊢ v₁ ⦂ t′) (⊢v₂ : ⊢ v₂ ⦂ t′) (ε : t′ ≡ t) → ⟨ v₁ , v₂ ⟩∈𝒱′⟦ t ː subst[( λ X → ⊢ v₁ ⦂ X )] ε ⊢v₁ , subst[( λ X → ⊢ v₂ ⦂ X )] ε ⊢v₂ ː s ⟧ → ⟨ v₁ , v₂ ⟩∈𝒱′⟦ t′ ː ⊢v₁ , ⊢v₂ ː s ⟧
change-Σ-𝒱 ⊢v₁ ⊢v₂ ↯ r[v₁,v₂] = r[v₁,v₂]

fp : ∀ {N} {Γ : Γ[ N ]} {ℾ e τ Σ γ₁ γ₂ Σ′ Σ₀} → ℾ ⊢ γ₁ → ℾ ⊢ γ₂ → Γ , Σ₀ ⊢ e ⦂ τ , Σ → ⟨ γ₁ , γ₂ ⟩∈𝒢⟦ Σ′ ː ℾ ⟧ → ⟨ γ₁ ⊢ e , γ₂ ⊢ e ⟩∈ℰ⟦ Σ ⨰ Σ′ ː (Σ′ ⟨⟨ τ ⟩⟩) ⟧

-- RLIT
fp {Σ′ = Σ′} ⊢γ₁ ⊢γ₂ ⊢`ℝ e₂ (𝓇 r₁) (𝓇 r₁) ⊢𝓇 ⊢𝓇 ⟨ ⊢`ℝ , ⊢`ℝ ⟩ rewrite lzero[⨰]< Σ′ > = [≡] (L0-8 r₁)

-- BOOLEANS
fp ⊢γ₁ ⊢γ₂ ⊢`𝔹 r[γ₁,γ₂] .(𝒷 ᴏ) .(𝒷 ᴏ) (⊢𝒷 {ᴏ}) ⊢𝒷 ⟨ ⊢`𝔹 {b = .ᴏ} , ⊢`𝔹 {b = .ᴏ} ⟩ = •
fp ⊢γ₁ ⊢γ₂ ⊢`𝔹 r[γ₁,γ₂] .(𝒷 ɪ) .(𝒷 ɪ) (⊢𝒷 {ɪ}) ⊢𝒷 ⟨ ⊢`𝔹 {b = .ɪ} , ⊢`𝔹 {b = .ɪ} ⟩ = •

-- ADDITION
fp {Σ′ = Σ′} ⊢γ₁ ⊢γ₂ (⊢_`+_ {Σ₁ = Σ₁} {Σ₂ = Σ₂} δ₁ δ₂) r[γ₁,γ₂] (𝓇 .(r₁₁ + r₁₂)) (𝓇 .(r₂₁ + r₂₂)) ⊢𝓇 ⊢𝓇 ⟨ ⊢_`+_ {r₁ = r₁₁} {r₂ = r₁₂} jr₁₁ jr₂₁ , ⊢_`+_  {r₁ = r₂₁} {r₂ = r₂₂} jr₁₂ jr₂₂ ⟩
  with fp ⊢γ₁ ⊢γ₂ δ₁ r[γ₁,γ₂] (𝓇 r₁₁) (𝓇 r₂₁) ⊢𝓇 ⊢𝓇 ⟨ jr₁₁ , jr₁₂ ⟩
     | fp ⊢γ₁ ⊢γ₂ δ₂ r[γ₁,γ₂] (𝓇 r₁₂) (𝓇 r₂₂) ⊢𝓇 ⊢𝓇 ⟨ jr₂₁ , jr₂₂ ⟩
… | IH₁ | IH₂ = ▵ {Σ₁ = Σ₁} {Σ₂ = Σ₂} {Σ₃ = Σ′} IH₁ IH₂

-- MULTIPLICATION
fp {Σ′ = Σ′} ⊢γ₁ ⊢γ₂ (⊢_`×_ {Σ₁ = Σ₁} {Σ₂ = Σ₂} e₁ e₂) r[γ₁,γ₂] .(𝓇 (r₁₁ ×ᴺ r₁₂)) .(𝓇 (r₂₁ ×ᴺ r₂₂)) ⊢𝓇 ⊢𝓇 ⟨ ⊢_`×_ {r₁ = r₁₁} {r₁₂} jr₁₁ jr₂₁ , ⊢_`×_ {r₁ = r₂₁} {r₂₂} jr₁₂ jr₂₂ ⟩
  with fp ⊢γ₁ ⊢γ₂ e₁ r[γ₁,γ₂] (𝓇 r₁₁) (𝓇 r₂₁) ⊢𝓇 ⊢𝓇 ⟨ jr₁₁ , jr₁₂ ⟩
     | fp ⊢γ₁ ⊢γ₂ e₂ r[γ₁,γ₂] (𝓇 r₁₂) (𝓇 r₂₂) ⊢𝓇 ⊢𝓇 ⟨ jr₂₁ , jr₂₂ ⟩
     | truncDichotomy (Σ₁ + Σ₂) Σ′
-- typo in latex? (l2.2)
… | IH₁ | IH₂ | ʟ ε rewrite ε = [≡] (▵× ε IH₁ IH₂)
… | IH₁ | IH₂ | ʀ ε rewrite ε = [<] `∞

-- LEQ
fp {Σ′ = Σ′} ⊢γ₁ ⊢γ₂ (⊢_`≤_ {Σ₁ = Σ₁} {Σ₂ = Σ₂} e₁ e₂) r[γ₁,γ₂] .(𝒷 (r₁ ≤? r₂)) .(𝒷 (r₃ ≤? r₄)) ε₁ ε₂ ⟨ ⊢_`≤_ {r₁ = r₁} {r₂ = r₂} δ₁  δ₂ , ⊢_`≤_ {r₁ = r₃} {r₂ = r₄} δ₃ δ₄ ⟩
  with fp ⊢γ₁ ⊢γ₂ e₁ r[γ₁,γ₂] (𝓇 r₁) (𝓇 r₃) ⊢𝓇 ⊢𝓇 ⟨ δ₁ , δ₃ ⟩
    | fp ⊢γ₁ ⊢γ₂ e₂ r[γ₁,γ₂] (𝓇 r₂) (𝓇 r₄) ⊢𝓇 ⊢𝓇 ⟨ δ₂ , δ₄ ⟩
    | r₁ ≤? r₂
    | r₃ ≤? r₄
... | IH₁ | IH₂ | ᴏ | ᴏ = •
... | IH₁ | IH₂ | ᴏ | ɪ = truncDichotomy ((Σ₁ + Σ₂)) Σ′
... | IH₁ | IH₂ | ɪ | ᴏ = truncDichotomy ((Σ₁ + Σ₂)) Σ′
... | IH₁ | IH₂ | ɪ | ɪ = •

-- VARIABLE REFERENCING
fp ⊢γ₁ ⊢γ₂ (⊢`var_ {i = i} x) r[γ₁,γ₂] .(_ #[ i ]) .(_ #[ i ]) e₁ e₂ ⟨ ⊢`var ↯ , ⊢`var ↯ ⟩ = gammaVarValRel r[γ₁,γ₂] e₁ e₂

-- UNIT
fp ⊢γ₁ ⊢γ₂ ⊢`tt r[γ₁,γ₂] .tt .tt ⊢tt ⊢tt ⟨ ⊢`tt , ⊢`tt ⟩ = ⟨ ↯ , ↯ ⟩

-- INL
fp {Σ′ = Σ′} ⊢γ₁ ⊢γ₂ (⊢`inl {Σ₁ = Σ₁} e₁) r[γ₁,γ₂] .(inl 𝓋₁) .(inl 𝓋₂) (⊢inl jv₁) (⊢inl jv₂) ⟨ ⊢`inl {𝓋 = 𝓋₁} r₁ , ⊢`inl {𝓋 = 𝓋₂} r₂ ⟩
  with fp ⊢γ₁ ⊢γ₂ e₁ r[γ₁,γ₂] 𝓋₁ 𝓋₂ jv₁ jv₂ ⟨ r₁ , r₂ ⟩
... | IH rewrite lzero[⨰]< Σ′ >
    | lunit[+][qty]< (⟨ 0 ⟩ +[qty] (Σ′ ⨰ Σ₁)) >
    | lunit[+][qty]< (Σ′ ⨰ Σ₁) >
    | L1 Σ′ Σ₁ = IH

-- INR
fp {Σ′ = Σ′} ⊢γ₁ ⊢γ₂ (⊢`inr {Σ₂ = Σ₂} e₁) r[γ₁,γ₂] .(inr 𝓋₁) .(inr 𝓋₂) (⊢inr jv₁) (⊢inr jv₂) ⟨ ⊢`inr {𝓋 = 𝓋₁} r₁ , ⊢`inr {𝓋 = 𝓋₂} r₂ ⟩
  with fp ⊢γ₁ ⊢γ₂ e₁ r[γ₁,γ₂] 𝓋₁ 𝓋₂ jv₁ jv₂ ⟨ r₁ , r₂ ⟩
... | IH rewrite lzero[⨰]< Σ′ >
  | lunit[+][qty]< (⟨ 0 ⟩ +[qty] (Σ′ ⨰ Σ₂)) >
  | lunit[+][qty]< (Σ′ ⨰ Σ₂) >
  | L1 Σ′ Σ₂ = IH

-- CASE
fp {Σ′ = Σ′} ⊢γ₁ ⊢γ₂ (⊢`case {Γ = Γ} {Σ₁ = Σ₁} {Σ₁₁ = Σ₁₁} {Σ₁₂ = Σ₁₂} {Σ₂ = Σ₂} {Σ₃ = Σ₃} {s₂ = s₂} {s₃ = s₃} e₁ e₂ e₃ tyjoin) r[γ₁,γ₂] v₁ v₂ ε₁ ε₂ ⟨ ⊢`case/l {𝓋₁ = 𝓋₁₁} r₁ r₂ , ⊢`case/l {𝓋₁ = 𝓋₁₂} r₃ r₄ ⟩
  with typeSafety {Σ′ = Σ′} e₁ r₁
     | typeSafety {Σ′ = Σ′} e₁ r₃
     | fp ⊢γ₁ ⊢γ₂ e₁ r[γ₁,γ₂] (inl 𝓋₁₁) (inl 𝓋₁₂) (typeSafety {Σ′ = Σ′} e₁ r₁) (typeSafety {Σ′ = Σ′} e₁ r₃) ⟨ r₁ , r₃ ⟩
… | ⊢inl ⊢v₁ | ⊢inl ⊢v₂ | IH₁
  with fp (⊢s ⊢v₁ ⊢γ₁) (⊢s ⊢v₂ ⊢γ₂) e₂ ⟨∃ ⊢v₁ , ⟨∃ ⊢v₂ , ⟨ IH₁ , r[γ₁,γ₂] ⟩ ⟩ ⟩ v₁ v₂ (typeSafety e₂ r₂) (typeSafety e₂ r₄) ⟨ r₂ , r₄ ⟩
… | IH₂ = subsumption tyjoin IH₂

fp {Σ′ = Σ′} ⊢γ₁ ⊢γ₂ (⊢`case {Σ₁ = Σ₁} {Σ₁₁ = Σ₁₁} {Σ₁₂ = Σ₁₂} {Σ₂ = Σ₂} {Σ₃ = Σ₃} {s₂ = s₂} {s₃ = s₃} e₁ e₂ e₃ tyjoin) r[γ₁,γ₂] v₁ v₂ ε₁ ε₂ ⟨ ⊢`case/l {𝓋₁ = 𝓋₁₁} r₁ r₂ , ⊢`case/r {𝓋₁ = 𝓋₁₂} r₃ r₄ ⟩
  with fp ⊢γ₁ ⊢γ₂ e₁ r[γ₁,γ₂] ((inl 𝓋₁₁)) ((inr 𝓋₁₂)) (typeSafety e₁ r₁) (typeSafety e₁ r₃) ⟨ r₁ , r₃ ⟩
... | IH with typeSafety {Σ′ = Σ′} e₁ r₁ | typeSafety {Σ′ = Σ′} e₁ r₃
… | ⊢inl X | ⊢inr Y rewrite L4 s₂ s₃ Σ₁ Σ₁₁ Σ₁₂ Σ₂ Σ₃ Σ′ IH = L5 ε₁ ε₂

-- TODO: these cases are analogous to those above
{-
fp ⊢γ₁ ⊢γ₂ (⊢`case e₁ e₂ e₃ tyjoin) r[γ₁,γ₂] v₁ v₂ ε₁ ε₂ ⟨ ⊢`case/r {𝓋₁ = 𝓋₁₁} r₁ r₂ , ⊢`case/l {𝓋₁ = 𝓋₁₂} r₃ r₄ ⟩
  with fp ⊢γ₁ ⊢γ₂ e₁ r[γ₁,γ₂] (inr 𝓋₁₁) (inl 𝓋₁₂) (typeSafety e₁ r₁) (typeSafety e₁ r₃) ⟨ r₁ , r₃ ⟩
... | IH  = {!   !}
fp ⊢γ₁ ⊢γ₂ (⊢`case e₁ e₂ e₃ tyjoin) r[γ₁,γ₂] v₁ v₂ ε₁ ε₂ ⟨ ⊢`case/r {𝓋₁ = 𝓋₁₁} r₁ r₂ , ⊢`case/r {𝓋₁ = 𝓋₁₂} r₃ r₄ ⟩
  with fp ⊢γ₁ ⊢γ₂ e₁ r[γ₁,γ₂] (inr 𝓋₁₁) (inr 𝓋₁₂) (typeSafety e₁ r₁) (typeSafety e₁ r₃) ⟨ r₁ , r₃ ⟩
... | IH  = {!IH   !}

-- TODO: derived terms
-- IF
fp ⊢γ₁ ⊢γ₂ (⊢`if e₁ e₂ e₃) r[γ₁,γ₂] v₁ v₂ ε₁ ε₂ ⟨ ⊢`if-true r₁ r₂ , ⊢`if-true r₃ r₄ ⟩
  with fp ⊢γ₁ ⊢γ₂ e₂ r[γ₁,γ₂] v₁ v₂ ε₁ ε₂ ⟨ r₂ , r₄ ⟩
... | IH = {!   !}
fp ⊢γ₁ ⊢γ₂ (⊢`if e₁ e₂ e₃) r[γ₁,γ₂] v₁ v₂ ε₁ ε₂ ⟨ ⊢`if-true r₁ r₂ , ⊢`if-false r₃ r₄ ⟩ = {!   !}
fp ⊢γ₁ ⊢γ₂ (⊢`if e₁ e₂ e₃) r[γ₁,γ₂] v₁ v₂ ε₁ ε₂ ⟨ ⊢`if-false r₁ r₂ , ⊢`if-true r₃ r₄ ⟩ = {!   !}
fp ⊢γ₁ ⊢γ₂ (⊢`if e₁ e₂ e₃) r[γ₁,γ₂] v₁ v₂ ε₁ ε₂ ⟨ ⊢`if-false r₁ r₂ , ⊢`if-false r₃ r₄ ⟩ = {!   !}

-- LET
fp ⊢γ₁ ⊢γ₂ (⊢`let e₁ e₂) r[γ₁,γ₂] v₁ v₂ ε₁ ε₂ ⟨ ⊢`let {𝓋₁ = 𝓋₁₁} r₁ r₂ , ⊢`let {𝓋₁ = 𝓋₁₂} r₃ r₄ ⟩
  with fp ⊢γ₁ ⊢γ₂ e₁ r[γ₁,γ₂] 𝓋₁₁ 𝓋₁₂ (typeSafety e₁ r₁) (typeSafety e₁ r₃) ⟨ r₁ , r₃ ⟩
... | IH₁ with fp ⊢γ₁ ⊢γ₂ e₂ ⟨∃ (typeSafety e₁ r₁) , ⟨∃ (typeSafety e₁ r₃) , ⟨ IH₁ , r[γ₁,γ₂] ⟩ ⟩ ⟩ v₁ v₂ (typeSafety e₂ r₂) (typeSafety e₂ r₄) ⟨ r₂ , r₄ ⟩
... | IH₂ = {! IH₂  !}

-}

-- LAMBDA
fp {Σ = Σ} {Σ′ = Σ′} ⊢γ₁ ⊢γ₂
  (⊢`sλ {Σ₁ = Σe₁} {τ₁ = τ₁} {τ₂} ⊢e) r[γ₁,γ₂]
  .(sƛ⦂ e₁ ∥ γ₁) .(sƛ⦂ e₂ ∥ γ₂)
  (⊢sλ {Γ = ℾ₁} {τ₁ = τ₁₁} {τ₂ = τ₂₁} {s = sx†₁} {s′ = s†₁} {Σ = Σ₁} ⊢γ₁′ ⊢e₁ ε₁₁ ε₁₂ ε₁₃)
  (⊢sλ {Γ = ℾ₂} {τ₁ = τ₁₂} {τ₂ = τ₂₂} {s = sx†₂} {s′ = s†₂} {Σ = Σ₂} ⊢γ₂′ ⊢e₂ ε₂₁ ε₂₂ ε₂₃)
  ⟨ ⊢`λ {γ = γ₁} {e = e₁} , ⊢`λ {γ = γ₂} {e = e₂} ⟩
  with L6 Σ′ τ₂ τ₂₁ τ₂₂ ε₁₂ ε₂₂
    | L3′′ ⊢γ₁ ⊢γ₂ ⊢γ₁′ ⊢γ₂′
    | L7 Σ′ τ₁₂ τ₁₁ τ₁ ε₂₁ ε₁₁
... | ↯ | ↯ | ↯ with L8 ⊢e₁ ⊢e₂
... | Σ₁≡Σ₂ = ⟨∃ ↯ , ⟨ ⟨ ⟨ ⟨ ↯ , Σ₁≡Σ₂ ⟩ , ↯ ⟩ , ↯ ⟩  , P ⟩ ⟩
  where
    P : ∀ {v₁ v₂ : 𝓋} {ε₁ : ⊢ v₁ ⦂ (_ ⟨⟨ _ ⟩⟩)} {ε₂ : ⊢ v₂ ⦂ (_ ⟨⟨ _ ⟩⟩)} {s′ Σ′′}
      → ⟨ γ₁ , γ₂ ⟩∈𝒢⟦ Σ′′ ː mapⱽ (instantiateΣ/τ Σ′′) ℾ₂ ⟧
      → ⟨ v₁ , v₂ ⟩∈𝒱′⟦ _ ⟨⟨ _ ⟩⟩ ː ε₁ , ε₂ ː s′ ⟧
      → ⟨ v₁ ∷ γ₁ ⊢ e₁ , v₂ ∷ γ₂ ⊢ e₁ ⟩∈ℰ⟦ (Σ ⨰ Σ′) + (Σ₂ ⨰ Σ′′) + (sx†₂ × s′) ː substSx/τ s′ (⇧ᵗ ((⇧ˢ _ ⟨⟨ _ ⟩⟩))) ⟧
    P {v₁} {v₂} {ε₁} {ε₂} {s′} {Σ′′} r[γ₁,γ₂]′ r[v₁,v₂]′ v₃ v₄ ⊢v₃ ⊢v₄ ⟨ e₁⇓v₃ , e₂⇓v₄ ⟩
      with (L2 s′ Σ′ τ₂)
    … | E with fp (⊢s ε₁ ⊢γ₁) (⊢s ε₂ ⊢γ₂) ⊢e ⟨∃ ε₁ , ⟨∃ ε₂ , ⟨ r[v₁,v₂]′ , r[γ₁,γ₂] ⟩ ⟩ ⟩ v₃ v₄ (subst[( λ X → ⊢ v₃ ⦂ X )] E ⊢v₃) (subst[( λ X → ⊢ v₄ ⦂ X )] E ⊢v₄) ⟨ e₁⇓v₃ , e₂⇓v₄ ⟩
    … | IH with change-Σ-𝒱 ⊢v₃ ⊢v₄ E IH
      | delayedΣEq (⊢`sλ {Σ₁ = Σe₁} {τ₁ = τ₁} {τ₂} ⊢e) ((⊢`λ {γ = γ₂} {e = e₂})) ⊢e₂
      | gammaDelayedΣEq r[γ₁,γ₂] r[γ₁,γ₂]′
    … | IH′ | ↯ | ↯ rewrite L0-1 Σ′
      | L0-2 s′
      | L0-3 (Σ₂ ⨰ Σ′′)
      | L0-7 (sx†₁ ×[qty] s′) ( Σ₂ ⨰ Σ′′) = IH′


-- LAMBDA APPLICATION
fp {Σ = Σ} {Σ′ = Σ′} ⊢γ₁ ⊢γ₂ (⊢`app {Σ₁ = Σ₁} {Σ₂ = Σ₂} {τ₁ = τ₁} {τ₂} e₁ e₂) r[γ₁,γ₂] v₁ v₂ ε₁ ε₂ ⟨ ⊢`app {γ = γ₁} {e′ = e′₁} {𝓋₁ = 𝓋₁}  r₁ r₂ r₃ , ⊢`app {γ = γ₂} {e′ = e′₂} {𝓋₁ = 𝓋₂} r₄ r₅ r₆ ⟩
  with fp ⊢γ₁ ⊢γ₂ e₁ r[γ₁,γ₂] (sƛ⦂ e′₁ ∥ γ₁) (sƛ⦂ e′₂ ∥ γ₂) (typeSafety e₁ r₁) (typeSafety e₁ r₄) ⟨ r₁ , r₄ ⟩
     | fp ⊢γ₁ ⊢γ₂ e₂ r[γ₁,γ₂] 𝓋₁ 𝓋₂ (typeSafety e₂ r₂) (typeSafety e₂ r₅) ⟨ r₂ , r₅ ⟩
... | IH₁ | IH₂ with typeSafety {Σ′ = Σ′} e₁ r₁ | typeSafety {Σ′ = Σ′} e₁ r₄ | IH₁
… | ⊢sλ {Γ = Γ₁} {τ₁ = τ₁₁} {τ₂ = τ₂₁} {s = sx†₁} {s′ = s†₁} {Σ = Σ′₁} ⊢γ₁′ ⊢e₁ ε₁₁ ε₁₂ ε₁₃
  | ⊢sλ {Γ = Γ₂} {τ₁ = τ₁₂} {τ₂ = τ₂₂} {s = sx†₂} {s′ = s†₂} {Σ = Σ′₂} ⊢γ₂′ ⊢e₂ ε₂₁ ε₂₂ ε₂₃
  | ⟨∃ ↯ , ⟨ ⟨ ⟨ ⟨ ↯ , ↯ ⟩ , ↯ ⟩ , ↯ ⟩ , IH′ ⟩ ⟩
  with L6 Σ′ τ₂ τ₂₁ τ₂₂ ε₁₂ ε₂₂
... | ↯ with L3 r₁ r₄ ⊢γ₁′ ⊢γ₂′
    | L7 Σ′ τ₁₂ τ₁₁ τ₁ ε₂₁ ε₁₁
... | ⟨ ↯ , ↯ ⟩ | ↯ with L9 Σ₂ Σ′ τ₂
    | ε₁₃
    | delayedΣEq e₁ r₁ ⊢e₁
... | ZZ | Z | G with IH′ {v₁ = 𝓋₁} {v₂ = 𝓋₂} {ε₁ = (typeSafety e₂ r₂)} {ε₂ = (typeSafety e₂ r₅)} {s′ = Σ₂ ⨰ Σ′} {Σ′ = Σ′} (L3′ ⊢γ₁′ ⊢γ₂′ r[γ₁,γ₂]) IH₂ v₁ v₂ (subst[( λ X → ⊢ v₁ ⦂ X )] ZZ ε₁) (subst[( λ X → ⊢ v₂ ⦂ X )] ZZ ε₂) ⟨ r₃ , r₆ ⟩
... | IH′′ rewrite L0-1 Σ′ | L1 Σ′₁ Σ′
    | L0-3 (Σ′ ⨰ Σ′₁)
    | ZZ | ◇ (L0-9 Σ₁ (mapⱽ (_×[qty]_ sx†₁) Σ₂) Σ′)
    | L0-4′ (Σ₁ ⨰ Σ′) | L0-6 sx†₁ Σ₂ Σ′ | L1 Σ₁ Σ′ | L0-4′ (Σ′ ⨰ Σ′₁) | G = IH′′

-- PAIR
fp {Σ′ = Σ′} ⊢γ₁ ⊢γ₂ (⊢`_pair_ {Σ₁ = Σ₁} {Σ₂ = Σ₂} e₁ e₂) r[γ₁,γ₂] .(𝓋₁₁ pair 𝓋₁₂) .(𝓋₂₁ pair 𝓋₂₂) (⊢pair t₁ t₂) (⊢pair t₃ t₄) ⟨ ⊢`_pair_ {𝓋₁ = 𝓋₁₁} {𝓋₂ = 𝓋₁₂} r₁ r₂ , ⊢`_pair_ {𝓋₁ = 𝓋₂₁} {𝓋₂ = 𝓋₂₂} r₃ r₄ ⟩
  with fp ⊢γ₁ ⊢γ₂ e₁ r[γ₁,γ₂] 𝓋₁₁ 𝓋₂₁ t₁ t₃ ⟨ r₁ , r₃ ⟩
    | fp ⊢γ₁ ⊢γ₂ e₂ r[γ₁,γ₂] 𝓋₁₂ 𝓋₂₂ t₂ t₄ ⟨ r₂ , r₄ ⟩
... | IH₁ | IH₂ rewrite lzero[⨰]< Σ′ >
    | lunit[+][qty]< (⟨ 0 ⟩ +[qty] (Σ′ ⨰ Σ₁)) >
    | lunit[+][qty]< (⟨ 0 ⟩ +[qty] (Σ′ ⨰ Σ₂)) >
    | lunit[+][qty]< (Σ′ ⨰ Σ₁) >
    | lunit[+][qty]< (Σ′ ⨰ Σ₂) >
    | L1 Σ′ Σ₁
    | L1 Σ′ Σ₂ = ⟨ IH₁ , IH₂ ⟩

-- FST
fp {Σ′ = Σ′} ⊢γ₁ ⊢γ₂ (⊢`fst {Σ = Σ} {Σ₁ = Σ₁} e₁) r[γ₁,γ₂] v₁ v₂ t₁ t₂ ⟨ ⊢`fst r₁ , ⊢`fst r₂ ⟩
  with fp ⊢γ₁ ⊢γ₂ e₁ r[γ₁,γ₂] (v₁ pair _) (v₂ pair _) (⊢pair t₁ _) (⊢pair t₂ _) ⟨ r₁ , r₂ ⟩
... | ⟨ π₃ , π₄ ⟩ rewrite L1 Σ′ Σ₁
    | lunit[+][qty]< (Σ₁ ⨰ Σ′) >
    | ◇ (L0-9 Σ Σ₁ Σ′) = π₃

-- SND
fp {Σ′ = Σ′} ⊢γ₁ ⊢γ₂ (⊢`snd {Σ = Σ} {Σ₂ = Σ₂} e₁) r[γ₁,γ₂] v₁ v₂ t₁ t₂ ⟨ ⊢`snd r₁ , ⊢`snd r₂ ⟩
  with fp ⊢γ₁ ⊢γ₂ e₁ r[γ₁,γ₂] (_ pair v₁) (_ pair v₂) (⊢pair _ t₁) (⊢pair _ t₂) ⟨ r₁ , r₂ ⟩
... | ⟨ π₃ , π₄ ⟩  rewrite L1 Σ′ Σ₂
    | lunit[+][qty]< (Σ₂ ⨰ Σ′) >
    | ◇ (L0-9 Σ Σ₂ Σ′) = π₄

{-
-}

fp _ = {!!}
