{-# OPTIONS --allow-unsolved-metas #-}
module proof where

open import rules public
open import post public
open import logical-relations public

-- Theorem 1.1 (Fundamental Property / (Metric Preservation in Fuzz)).

change-Σ-𝒱 : ∀ {t t′ : τ ᴢ} {v₁ v₂ : 𝓋} {s : Sens} (⊢v₁ : ⊢ v₁ ⦂ t′) (⊢v₂ : ⊢ v₂ ⦂ t′) (ε : t′ ≡ t) → ⟨ v₁ , v₂ ⟩∈𝒱′⟦ t ː subst[( λ X → ⊢ v₁ ⦂ X )] ε ⊢v₁ , subst[( λ X → ⊢ v₂ ⦂ X )] ε ⊢v₂ ː s ⟧ → ⟨ v₁ , v₂ ⟩∈𝒱′⟦ t′ ː ⊢v₁ , ⊢v₂ ː s ⟧
change-Σ-𝒱 ⊢v₁ ⊢v₂ ↯ r[v₁,v₂] = r[v₁,v₂]

fp : ∀ {N} {Γ : Γ[ N ]} {ℾ e τ Σ γ₁ γ₂ Σ′} → ℾ ⊢ γ₁ → ℾ ⊢ γ₂ → Γ ⊢ e ⦂ τ , Σ → ⟨ γ₁ , γ₂ ⟩∈𝒢⟦ Σ′ ː ℾ ⟧ → ⟨ γ₁ ⊢ e , γ₂ ⊢ e ⟩∈ℰ⟦ Σ ⨰ Σ′ ː (Σ′ ⟨⟨ τ ⟩⟩) ⟧
fp {Σ′ = Σ′} ⊢γ₁ ⊢γ₂ ⊢`ℝ e₂ (𝓇 r₁) (𝓇 r₁) ⊢𝓇 ⊢𝓇 ⟨ ⊢`ℝ , ⊢`ℝ ⟩ rewrite lzero[⨰]< Σ′ > = [≡] (L2 r₁)
{-
fp ⊢`𝔹 r[γ₁,γ₂] .(𝒷 ᴏ) .(𝒷 ᴏ) (⊢𝒷 {ᴏ}) ⊢𝒷 ⟨ ⊢`𝔹 {b = .ᴏ} , ⊢`𝔹 {b = .ᴏ} ⟩ = •
fp ⊢`𝔹 r[γ₁,γ₂] .(𝒷 ɪ) .(𝒷 ɪ) (⊢𝒷 {ɪ}) ⊢𝒷 ⟨ ⊢`𝔹 {b = .ɪ} , ⊢`𝔹 {b = .ɪ} ⟩ = •
fp {Σ′ = Σ′} (⊢_`+_ {Σ₁ = Σ₁} {Σ₂ = Σ₂} δ₁ δ₂) r[γ₁,γ₂] (𝓇 .(r₁₁ + r₁₂)) (𝓇 .(r₂₁ + r₂₂)) ⊢𝓇 ⊢𝓇 ⟨ ⊢_`+_ {r₁ = r₁₁} {r₂ = r₁₂} jr₁₁ jr₂₁ , ⊢_`+_  {r₁ = r₂₁} {r₂ = r₂₂} jr₁₂ jr₂₂ ⟩
  with fp δ₁ r[γ₁,γ₂] (𝓇 r₁₁) (𝓇 r₂₁) ⊢𝓇 ⊢𝓇 ⟨ jr₁₁ , jr₁₂ ⟩
     | fp δ₂ r[γ₁,γ₂] (𝓇 r₁₂) (𝓇 r₂₂) ⊢𝓇 ⊢𝓇 ⟨ jr₂₁ , jr₂₂ ⟩
… | IH₁ | IH₂ = L3 {Σ₁ = Σ₁} {Σ₂ = Σ₂} {Σ₃ = Σ′} IH₁ IH₂
fp {Σ′ = Σ′} (⊢_`×_ {Σ₁ = Σ₁} {Σ₂ = Σ₂} e₁ e₂) r[γ₁,γ₂] .(𝓇 (r₁₁ ×ᴺ r₁₂)) .(𝓇 (r₂₁ ×ᴺ r₂₂)) ⊢𝓇 ⊢𝓇 ⟨ ⊢_`×_ {r₁ = r₁₁} {r₁₂} jr₁₁ jr₂₁ , ⊢_`×_ {r₁ = r₂₁} {r₂₂} jr₁₂ jr₂₂ ⟩
  with fp e₁ r[γ₁,γ₂] (𝓇 r₁₁) (𝓇 r₂₁) ⊢𝓇 ⊢𝓇 ⟨ jr₁₁ , jr₁₂ ⟩
     | fp e₂ r[γ₁,γ₂] (𝓇 r₁₂) (𝓇 r₂₂) ⊢𝓇 ⊢𝓇 ⟨ jr₂₁ , jr₂₂ ⟩
     | L6 (Σ₁ + Σ₂) Σ′
-- typo in latex? (l2.2)
… | IH₁ | IH₂ | ʟ ε rewrite ε = [≡] (L13 ε IH₁ IH₂)
… | IH₁ | IH₂ | ʀ ε rewrite ε = [<] `∞
fp {Σ′ = Σ′} (⊢_`≤_ {Σ₁ = Σ₁} {Σ₂ = Σ₂} e₁ e₂) r[γ₁,γ₂] .(𝒷 (r₁ ≤? r₂)) .(𝒷 (r₃ ≤? r₄)) ε₁ ε₂ ⟨ ⊢_`≤_ {r₁ = r₁} {r₂ = r₂} δ₁  δ₂ , ⊢_`≤_ {r₁ = r₃} {r₂ = r₄} δ₃ δ₄ ⟩
  with fp e₁ r[γ₁,γ₂] (𝓇 r₁) (𝓇 r₃) ⊢𝓇 ⊢𝓇 ⟨ δ₁ , δ₃ ⟩
    | fp e₂ r[γ₁,γ₂] (𝓇 r₂) (𝓇 r₄) ⊢𝓇 ⊢𝓇 ⟨ δ₂ , δ₄ ⟩
    | r₁ ≤? r₂
    | r₃ ≤? r₄
... | IH₁ | IH₂ | ᴏ | ᴏ = •
... | IH₁ | IH₂ | ᴏ | ɪ = L6 ((Σ₁ + Σ₂)) Σ′
... | IH₁ | IH₂ | ɪ | ᴏ = L6 ((Σ₁ + Σ₂)) Σ′
... | IH₁ | IH₂ | ɪ | ɪ = •
fp (⊢`var_ {i = i} x) r[γ₁,γ₂] .(_ #[ i ]) .(_ #[ i ]) e₁ e₂ ⟨ ⊢`var ↯ , ⊢`var ↯ ⟩ = L7 r[γ₁,γ₂] e₁ e₂
fp ⊢`tt r[γ₁,γ₂] .tt .tt ⊢tt ⊢tt ⟨ ⊢`tt , ⊢`tt ⟩ = ⟨ ↯ , ↯ ⟩
fp {Σ′ = Σ′} (⊢`inl {Σ₁ = Σ₁} e₁) r[γ₁,γ₂] .(inl 𝓋₁) .(inl 𝓋₂) (⊢inl jv₁) (⊢inl jv₂) ⟨ ⊢`inl {𝓋 = 𝓋₁} r₁ , ⊢`inl {𝓋 = 𝓋₂} r₂ ⟩
  with fp e₁ r[γ₁,γ₂] 𝓋₁ 𝓋₂ jv₁ jv₂ ⟨ r₁ , r₂ ⟩
... | IH rewrite lzero[⨰]< Σ′ >
    | lunit[+][qty]< (⟨ 0 ⟩ +[qty] (Σ′ ⨰ Σ₁)) >
    | lunit[+][qty]< (Σ′ ⨰ Σ₁) >
    | L5 Σ′ Σ₁ = IH
fp {Σ′ = Σ′} (⊢`inr {Σ₂ = Σ₂} e₁) r[γ₁,γ₂] .(inr 𝓋₁) .(inr 𝓋₂) (⊢inr jv₁) (⊢inr jv₂) ⟨ ⊢`inr {𝓋 = 𝓋₁} r₁ , ⊢`inr {𝓋 = 𝓋₂} r₂ ⟩
  with fp e₁ r[γ₁,γ₂] 𝓋₁ 𝓋₂ jv₁ jv₂ ⟨ r₁ , r₂ ⟩
... | IH rewrite lzero[⨰]< Σ′ >
  | lunit[+][qty]< (⟨ 0 ⟩ +[qty] (Σ′ ⨰ Σ₂)) >
  | lunit[+][qty]< (Σ′ ⨰ Σ₂) >
  | L5 Σ′ Σ₂ = IH

-}

fp {Σ′ = Σ′} ⊢γ₁ ⊢γ₂ (⊢`case {Γ = Γ} {Σ₁ = Σ₁} {Σ₁₁ = Σ₁₁} {Σ₁₂ = Σ₁₂} {Σ₂ = Σ₂} {Σ₃ = Σ₃} {s₂ = s₂} {s₃ = s₃} e₁ e₂ e₃ tyjoin) r[γ₁,γ₂] v₁ v₂ ε₁ ε₂ ⟨ ⊢`case/l {𝓋₁ = 𝓋₁₁} r₁ r₂ , ⊢`case/l {𝓋₁ = 𝓋₁₂} r₃ r₄ ⟩
  with fp ⊢γ₁ ⊢γ₂ e₁ r[γ₁,γ₂] (inl 𝓋₁₁) (inl 𝓋₁₂) (typeSafety {Σ′ = Σ′} e₁ r₁) (typeSafety {Σ′ = Σ′} e₁ r₃) ⟨ r₁ , r₃ ⟩
... | IH₁ with fp (⊢s (L10 (typeSafety {Γ = Γ} {Σ = Σ₁} {Σ′ = Σ′} e₁ r₁)) ⊢γ₁) (⊢s (L10 ((typeSafety {Σ =  Σ₁} {Σ′ = Σ′} e₁ r₃))) ⊢γ₂) e₂ ⟨∃ L10 ((typeSafety {Σ =  Σ₁} {Σ′ = Σ′} e₁ r₁)) , ⟨∃ L10 ((typeSafety {Σ =  Σ₁} {Σ′ = Σ′} e₁ r₃)) , ⟨ L12 IH₁ , r[γ₁,γ₂] ⟩ ⟩ ⟩ v₁ v₂
… | IH₂P with IH₂P (typeSafety e₂ r₂) (typeSafety e₂ r₄) ⟨ r₂ , r₄ ⟩
… | IH₂ = {! IH₂ !}

{-
fp {Σ′ = Σ′} ⊢γ₁ ⊢γ₂ (⊢`case {Σ₁ = Σ₁} {Σ₁₁ = Σ₁₁} {Σ₁₂ = Σ₁₂} {Σ₂ = Σ₂} {Σ₃ = Σ₃} {s₂ = s₂} {s₃ = s₃} e₁ e₂ e₃ tyjoin) r[γ₁,γ₂] v₁ v₂ ε₁ ε₂ ⟨ ⊢`case/l {𝓋₁ = 𝓋₁₁} r₁ r₂ , ⊢`case/r {𝓋₁ = 𝓋₁₂} r₃ r₄ ⟩
  with fp ⊢γ₁ ⊢γ₂ e₁ r[γ₁,γ₂] ((inl 𝓋₁₁)) ((inr 𝓋₁₂)) (typeSafety e₁ r₁) (typeSafety e₁ r₃) ⟨ r₁ , r₃ ⟩
... | IH with typeSafety {Σ′ = Σ′} e₁ r₁ | typeSafety {Σ′ = Σ′} e₁ r₃
… | ⊢inl X | ⊢inr Y rewrite L16 s₂ s₃ Σ₁ Σ₁₁ Σ₁₂ Σ₂ Σ₃ Σ′ IH = L17 ε₁ ε₂

fp (⊢`case e₁ e₂ e₃ tyjoin) r[γ₁,γ₂] v₁ v₂ ε₁ ε₂ ⟨ ⊢`case/r {𝓋₁ = 𝓋₁₁} r₁ r₂ , ⊢`case/l {𝓋₁ = 𝓋₁₂} r₃ r₄ ⟩
  with fp e₁ r[γ₁,γ₂] (inr 𝓋₁₁) (inl 𝓋₁₂) (typeSafety e₁ r₁) (typeSafety e₁ r₃) ⟨ r₁ , r₃ ⟩
... | IH  = {!   !}
fp (⊢`case e₁ e₂ e₃ tyjoin) r[γ₁,γ₂] v₁ v₂ ε₁ ε₂ ⟨ ⊢`case/r {𝓋₁ = 𝓋₁₁} r₁ r₂ , ⊢`case/r {𝓋₁ = 𝓋₁₂} r₃ r₄ ⟩
  with fp e₁ r[γ₁,γ₂] (inr 𝓋₁₁) (inr 𝓋₁₂) (typeSafety e₁ r₁) (typeSafety e₁ r₃) ⟨ r₁ , r₃ ⟩
... | IH  = {!IH   !}
fp (⊢`if e₁ e₂ e₃) r[γ₁,γ₂] v₁ v₂ ε₁ ε₂ ⟨ ⊢`if-true r₁ r₂ , ⊢`if-true r₃ r₄ ⟩
  with fp e₂ r[γ₁,γ₂] v₁ v₂ ε₁ ε₂ ⟨ r₂ , r₄ ⟩
... | IH = {!   !}
fp (⊢`if e₁ e₂ e₃) r[γ₁,γ₂] v₁ v₂ ε₁ ε₂ ⟨ ⊢`if-true r₁ r₂ , ⊢`if-false r₃ r₄ ⟩ = {!   !}
fp (⊢`if e₁ e₂ e₃) r[γ₁,γ₂] v₁ v₂ ε₁ ε₂ ⟨ ⊢`if-false r₁ r₂ , ⊢`if-true r₃ r₄ ⟩ = {!   !}
fp (⊢`if e₁ e₂ e₃) r[γ₁,γ₂] v₁ v₂ ε₁ ε₂ ⟨ ⊢`if-false r₁ r₂ , ⊢`if-false r₃ r₄ ⟩ = {!   !}
fp (⊢`let e₁ e₂) r[γ₁,γ₂] v₁ v₂ ε₁ ε₂ ⟨ ⊢`let {𝓋₁ = 𝓋₁₁} r₁ r₂ , ⊢`let {𝓋₁ = 𝓋₁₂} r₃ r₄ ⟩
  with fp e₁ r[γ₁,γ₂] 𝓋₁₁ 𝓋₁₂ (typeSafety e₁ r₁) (typeSafety e₁ r₃) ⟨ r₁ , r₃ ⟩
... | IH₁ with fp e₂ ⟨∃ (typeSafety e₁ r₁) , ⟨∃ (typeSafety e₁ r₃) , ⟨ IH₁ , r[γ₁,γ₂] ⟩ ⟩ ⟩ v₁ v₂ (typeSafety e₂ r₂) (typeSafety e₂ r₄) ⟨ r₂ , r₄ ⟩
... | IH₂ = {! IH₂  !}
-}
-- ⊢ ƛ⦂ e₁ ∥ γ₂ ⦂
--       (ƛ⦂ Σ′ ⟨⟨ .τ₁ ⟩⟩ ⇒[ (⟨ 0 ⟩ ∷ Σ′ ⨰ .Σ₁) +[qty] ⟨ 0 ⟩ ∔ [ ⟨ 0 ⟩ ] ]
--        ⇧ᵗ< ᴢ > (⇧ˢ Σ′ ⟨⟨ τ₂ ⟩⟩))

{-
fp {Σ′ = Σ′} ⊢γ₁ ⊢γ₂ (⊢`λ {τ₂ = τ₂} ⊢e) r[γ₁,γ₂] .(ƛ⦂ e₁ ∥ γ₁) .(ƛ⦂ e₂ ∥ γ₂) (⊢λ {ℾ = ℾ₁} ⊢γ₁′ ⊢e₁ ε₁₁ ε₁₂ ε₁₃) (⊢λ {ℾ = ℾ₂} ⊢γ₂′ ⊢e₂ ε₂₁ ε₂₂ ε₂₃) ⟨ ⊢`λ {γ = γ₁} {e = e₁} , ⊢`λ {γ = γ₂} {e = e₂} ⟩ = --rewrite L14 ⊢γ₁′ ⊢γ₁ | L14 ⊢γ₂′ ⊢γ₂  =
  ⟨∃ ↯ , ⟨ L15 ⊢γ₁ ⊢γ₂ ⊢γ₁′ ⊢γ₂′ r[γ₁,γ₂] , P ⟩ ⟩
  where
    P : ∀ {v₁ v₂ : 𝓋} {ε₁ : ⊢ v₁ ⦂ (_ ⟨⟨ _ ⟩⟩)} {ε₂ : ⊢ v₂ ⦂ (_ ⟨⟨ _ ⟩⟩)} {s s′ s′′ Σ Σ′}
      → ⟨ γ₁ , γ₂ ⟩∈𝒢⟦ Σ′ ː mapⱽ (instantiateΣ/τ Σ′) ℾ₂ ⟧
      → ⟨ v₁ , v₂ ⟩∈𝒱′⟦ _ ⟨⟨ _ ⟩⟩ ː ε₁ , ε₂ ː s′′ ⟧
      → ⟨ v₁ ∷ γ₁ ⊢ e₁ , v₂ ∷ γ₂ ⊢ e₁ ⟩∈ℰ⟦ (s + (Σ ⨰ Σ′)) + (s′ × s′′) ː substSx/τ s′′ (⇧ᵗ ((⇧ˢ _ ⟨⟨ _ ⟩⟩))) ⟧
    P {v₁} {v₂} {ε₁} {ε₂} {s} {s′} {s′′} {Σ} {Σ′ᵢ} r[γ₁,γ₂]′ r[v₁,v₂]′ v₃ v₄ ⊢v₃ ⊢v₄ ⟨ e₁⇓v₃ , e₂⇓v₄ ⟩
      with (L9 s′′ Σ′ τ₂)
    … | E with fp (⊢s ε₁ ⊢γ₁) (⊢s ε₂ ⊢γ₂) ⊢e ⟨∃ ε₁ , ⟨∃ ε₂ , ⟨ r[v₁,v₂]′ , r[γ₁,γ₂] ⟩ ⟩ ⟩ v₃ v₄ (subst[( λ X → ⊢ v₃ ⦂ X )] E ⊢v₃) (subst[( λ X → ⊢ v₄ ⦂ X )] E ⊢v₄) ⟨ e₁⇓v₃ , e₂⇓v₄ ⟩
    … | IH with change-Σ-𝒱 ⊢v₃ ⊢v₄ E IH
    … | IH′ = {!IH′ !}

fp {Σ′ = Σ′} ⊢γ₁ ⊢γ₂ (⊢`app e₁ e₂) r[γ₁,γ₂] v₁ v₂ ε₁ ε₂ ⟨ ⊢`app {γ′ = γ′₁} {e′ = e′₁} {𝓋₁ = 𝓋₁}  r₁ r₂ r₃ , ⊢`app {γ′ = γ′₂} {e′ = e′₂} {𝓋₁ = 𝓋₂} r₄ r₅ r₆ ⟩
  with fp ⊢γ₁ ⊢γ₂ e₁ r[γ₁,γ₂] (ƛ⦂ e′₁ ∥ γ′₁) (ƛ⦂ e′₂ ∥ γ′₂) (typeSafety e₁ r₁) (typeSafety e₁ r₄) ⟨ r₁ , r₄ ⟩
     | fp ⊢γ₁ ⊢γ₂ e₂ r[γ₁,γ₂] 𝓋₁ 𝓋₂ (typeSafety e₂ r₂) (typeSafety e₂ r₅) ⟨ r₂ , r₅ ⟩
... | IH₁ | IH₂ with typeSafety {Σ′ = Σ′} e₁ r₁ | typeSafety {Σ′ = Σ′} e₁ r₄ | IH₁
… | ⊢λ ⊢γ₁′ ⊢e₁ ε₁₁ ε₁₂ ε₁₃ | ⊢λ ⊢γ₂′ ⊢e₂ ε₂₁ ε₂₂ ε₂₃ | ⟨∃ ↯ , IH′ ⟩ = {!  !}

-}

{-
fp {Σ′ = Σ′} (⊢`_pair_ {Σ₁ = Σ₁} {Σ₂ = Σ₂} e₁ e₂) r[γ₁,γ₂] .(𝓋₁₁ pair 𝓋₁₂) .(𝓋₂₁ pair 𝓋₂₂) (⊢pair t₁ t₂) (⊢pair t₃ t₄) ⟨ ⊢`_pair_ {𝓋₁ = 𝓋₁₁} {𝓋₂ = 𝓋₁₂} r₁ r₂ , ⊢`_pair_ {𝓋₁ = 𝓋₂₁} {𝓋₂ = 𝓋₂₂} r₃ r₄ ⟩
  with fp e₁ r[γ₁,γ₂] 𝓋₁₁ 𝓋₂₁ t₁ t₃ ⟨ r₁ , r₃ ⟩
    | fp e₂ r[γ₁,γ₂] 𝓋₁₂ 𝓋₂₂ t₂ t₄ ⟨ r₂ , r₄ ⟩
... | IH₁ | IH₂ rewrite lzero[⨰]< Σ′ >
    | lunit[+][qty]< (⟨ 0 ⟩ +[qty] (Σ′ ⨰ Σ₁)) >
    | lunit[+][qty]< (⟨ 0 ⟩ +[qty] (Σ′ ⨰ Σ₂)) >
    | lunit[+][qty]< (Σ′ ⨰ Σ₁) >
    | lunit[+][qty]< (Σ′ ⨰ Σ₂) >
    | L5 Σ′ Σ₁
    | L5 Σ′ Σ₂ = ⟨ IH₁ , IH₂ ⟩
fp {Σ′ = Σ′} (⊢`fst {Σ = Σ} {Σ₁ = Σ₁} e₁) r[γ₁,γ₂] v₁ v₂ t₁ t₂ ⟨ ⊢`fst r₁ , ⊢`fst r₂ ⟩
  with fp e₁ r[γ₁,γ₂] (v₁ pair _) (v₂ pair _) (⊢pair t₁ _) (⊢pair t₂ _) ⟨ r₁ , r₂ ⟩
... | ⟨ π₃ , π₄ ⟩ rewrite L5 Σ′ Σ₁
    | lunit[+][qty]< (Σ₁ ⨰ Σ′) >
    | ◇ (L4 Σ Σ₁ Σ′) = π₃
fp {Σ′ = Σ′} (⊢`snd {Σ = Σ} {Σ₂ = Σ₂} e₁) r[γ₁,γ₂] v₁ v₂ t₁ t₂ ⟨ ⊢`snd r₁ , ⊢`snd r₂ ⟩
  with fp e₁ r[γ₁,γ₂] (_ pair v₁) (_ pair v₂) (⊢pair _ t₁) (⊢pair _ t₂) ⟨ r₁ , r₂ ⟩
... | ⟨ π₃ , π₄ ⟩  rewrite L5 Σ′ Σ₂
    | lunit[+][qty]< (Σ₂ ⨰ Σ′) >
    | ◇ (L4 Σ Σ₂ Σ′) = π₄
-}

fp _ = {!!}
