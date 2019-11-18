{-# OPTIONS --allow-unsolved-metas #-}
module post where

open import rules public
open import logical-relations public

postulate
  L0-1 : ∀ {N} (Σ : Σ[ N ]) → zero ⨰ Σ ≡< qty ℕ > ⟨ 0 ⟩
  L0-2 : ∀ (s : Sens) → ⟨ 0 ⟩ ×[qty] s ≡< qty ℕ > ⟨ 0 ⟩
  L0-3 : ∀ (s : Sens) → ⟨ 0 ⟩ +[qty] s ≡< qty ℕ > s
  L0-4 : ∀ (s : Sens) → (s +[qty] ⟨ 0 ⟩) ≡< qty ℕ > s
  L0-4′ : ∀ (s : Sens) → s ≡< qty ℕ > s +[qty] ⟨ 0 ⟩
  L0-5 : ∀ {N} (Σ₁ : Σ[ N ]) (Σ₂ : Σ[ ꜱ N ]) → ((⟨ 0 ⟩ ∷ Σ₁ ⨰ Σ₂) +[qty] ⟨ 0 ⟩) ≡ (⟨ 0 ⟩ ∷ Σ₁ ⨰ Σ₂)
  L0-6 : ∀ {N} (s : Sens) (Σ Σ′ : Σ[ N ]) → mapⱽ (_×[qty]_ s) Σ ⨰ Σ′ ≡ s ×[qty] (Σ ⨰ Σ′)
  L1 : ∀ (N : ℕ) → ∣ N - N ∣ ≡ 0
  L2 : ∀ (N : ℕ) → ⟨ ∣ N - N ∣ ⟩ ≡< qty ℕ > ⟨ 0 ⟩
  L3 : ∀ {a b c d N : ℕ} {Σ₁ Σ₂ Σ₃ : Σ[ N ]} → ⟨ ∣ a - b ∣ ⟩ ≤ (Σ₁ ⨰ Σ₃) → ⟨ ∣ c - d ∣ ⟩ ≤ (Σ₂ ⨰ Σ₃) → ⟨ ∣ (a + c) - (b + d) ∣ ⟩ ≤ ((Σ₁ + Σ₂) ⨰ Σ₃)
  L4 : ∀ {N} (Σ₁ Σ₂ Σ₃ : Σ[ N ]) → (Σ₁ ⨰ Σ₃) + (Σ₂ ⨰ Σ₃) ≡ ((Σ₁ + Σ₂) ⨰ Σ₃)
  -- L4-1 : ∀ {N} (Σ₁ Σ₂ Σ₃ : Σ[ N ]) → (Σ₁ ⨰ Σ₃) + (Σ₂ ⨰ Σ₃) ≡ ((Σ₁ + Σ₂) ⨰ Σ₃)
  L5 : ∀ {N} (Σ₁ Σ₂ : Σ[ N ]) → (Σ₁ ⨰ Σ₂) ≡ (Σ₂ ⨰ Σ₁)
  L5′ : ∀ (Σ₁ Σ₂ : Sens) → (Σ₁ +[qty] Σ₂) ≡ (Σ₂ +[qty] Σ₁)
  L6 : ∀ {N} (Σ₁ Σ₂ : Σ[ N ]) → [vec]⌉ Σ₁ ⌈⸢ `∞ ⸣ ⨰ Σ₂ ≡ ⟨ 0 ⟩ ∨  [vec]⌉ Σ₁ ⌈⸢ `∞ ⸣ ⨰ Σ₂ ≡ `∞
  L7 : ∀ {N} {γ₁ γ₂ : γ[ N ]} {Σ : Σ[ N ]} {ℾ : ℾ[ N ]} {x : idx N }
    → ⟨ γ₁ , γ₂ ⟩∈𝒢⟦ Σ ː ℾ ⟧
    → (ε₁ : ⊢ γ₁ #[ x ] ⦂ ℾ #[ x ])
    → (ε₂ : ⊢ γ₂ #[ x ] ⦂ ℾ #[ x ])
    → ⟨ γ₁ #[ x ] , γ₂ #[ x ] ⟩∈𝒱′⟦ ℾ #[ x ] ː ε₁ , ε₂ ː Σ #[ x ] ⟧
  -- typeSafety : ∀ {N} {e : Term N} {Γ : Γ[ N ]} {Σ Σ′ : Σ[ N ]} {v} {γ : γ[ N ]} {τ : τ N} → Γ ⊢ e ⦂ τ , Σ → γ ⊢ e ⇓ v → ⊢ v ⦂ Σ′ ⟨⟨ τ ⟩⟩
  L8 : ∀ {N} {s} {Σ : Σ[ N ]} {τ v} → (⊢ v ⦂ (substSx/τ s (⇧ᵗ (⇧ˢ Σ ⟨⟨ τ ⟩⟩)))) → (⊢ v ⦂ ((s ∷ Σ) ⟨⟨ τ ⟩⟩))
  -- L9-1 : ∀ {N} (Σ : Σ[ N ]) (τ : τ (ꜱ N)) → (substSx/τ s (⇧ᵗ (⇧ˢ Σ ⟨⟨ τ ⟩⟩))) ≡ (s ∷ Σ) ⟨⟨ τ ⟩⟩
  L9 : ∀ {N} (s : Sens) (Σ : Σ[ N ]) (τ : τ (ꜱ N)) → (substSx/τ s (⇧ᵗ (⇧ˢ Σ ⟨⟨ τ ⟩⟩))) ≡ (s ∷ Σ) ⟨⟨ τ ⟩⟩
  L13 : ∀ {N} {r₁₁ r₁₂ r₂₁ r₂₂ : ℕ} {Σ₁ Σ₂ Σ′ : Σ[ N ]} → [vec]⌉ (Σ₁ + Σ₂) ⌈⸢ `∞ ⸣ ⨰ Σ′ ≡ ⟨ 0 ⟩
    → ⟨ ∣ r₁₁ - r₂₁ ∣ ⟩ ≤ (Σ₁ ⨰ Σ′)
    → ⟨ ∣ r₁₂ - r₂₂ ∣ ⟩ ≤ (Σ₂ ⨰ Σ′)
    → ⟨ ∣ r₁₁ ×ᴺ r₁₂ - r₂₁ ×ᴺ r₂₂ ∣ ⟩ ≡< qty ℕ > ⟨ 0 ⟩
  L14 : ∀ {N} {γ : γ[ N ]} {Σ′} {ℾ₁ : Γ[ N ]} {ℾ₂ : ℾ[ N ]} → mapⱽ (instantiateΣ/τ Σ′) ℾ₁ ⊢ γ → ℾ₂ ⊢ γ → mapⱽ (instantiateΣ/τ Σ′) ℾ₁ ≡ ℾ₂
  L14-1 : ∀ {N} {γ : γ[ N ]} {Σ′} {ℾ₁ ℾ₂ : Γ[ N ]} → mapⱽ (instantiateΣ/τ Σ′) ℾ₁ ⊢ γ → mapⱽ (instantiateΣ/τ Σ′) ℾ₂ ⊢ γ → ℾ₁ ≡ ℾ₂
  L14-2 : ∀ {N} {γ : γ[ N ]} {ℾ₁ ℾ₂ : ℾ[ N ]} → ℾ₁ ⊢ γ → ℾ₂ ⊢ γ → ℾ₁ ≡ ℾ₂
  L15 : ∀ {N} {γ₁ γ₂ : γ[ N ]} {ℾ : ℾ[ N ]} {Γ₁ Γ₂} {Σ₁ : Σ[ N ]} → ℾ ⊢ γ₁ → ℾ ⊢ γ₂
    → mapⱽ (instantiateΣ/τ Σ₁) Γ₁ ⊢ γ₁
    → mapⱽ (instantiateΣ/τ Σ₁) Γ₂ ⊢ γ₂
    → Γ₁ ≡ Γ₂
  L16 : ∀ {N} (s₂ s₃ : Sens) (Σ₁ Σ₁₁ Σ₁₂ Σ₂ Σ₃ Σ′ : Σ[ N ])
    → Σ₁ ⨰ Σ′ ≡ `∞
    → ([vec]⌉ Σ₁ ⌈⸢ `∞ ⸣ + ((s₂ ⨵ Σ₁₁) + Σ₂) ⊔ ((s₃ ⨵ Σ₁₂) + Σ₃)) ⨰ Σ′ ≡ `∞
  L17 : ∀ {N} {v₁ v₂ τ} {Σ : Σ[ N ]} → (ε₁ : ⊢ v₁ ⦂ Σ ⟨⟨ τ ⟩⟩)
    → (ε₂ : ⊢ v₂ ⦂ Σ ⟨⟨ τ ⟩⟩)
    → ⟨ v₁ , v₂ ⟩∈𝒱′⟦ Σ ⟨⟨ τ ⟩⟩ ː ε₁ , ε₂ ː `∞ ⟧
  L18 : ∀ {N} (Σ′ : Σ[ N ]) (τ₂ τ₃ τ₁ : τ (ꜱ N))
    → ⇧ᵗ< ᴢ > (⇧ˢ Σ′ ⟨⟨ τ₂ ⟩⟩) ≡ instantiateΣ/τ 𝟎 τ₃
    → ⇧ᵗ< ᴢ > (⇧ˢ Σ′ ⟨⟨ τ₂ ⟩⟩) ≡ instantiateΣ/τ 𝟎 τ₁
    → τ₁ ≡ τ₃
  L19 : ∀ {N} (Σ′ : Σ[ N ]) (τ₃ τ₂ τ₁ : τ N)
    → (Σ′ ⟨⟨ τ₁ ⟩⟩) ≡ instantiateΣ/τ (𝐜< N > ⟨ 0 ⟩) τ₃
    → (Σ′ ⟨⟨ τ₁ ⟩⟩) ≡ instantiateΣ/τ (𝐜< N > ⟨ 0 ⟩) τ₂
    → τ₃ ≡ τ₂
  L20 : ∀ {N} {τ₁ ℾ Σ₁ Σ₂ τ₂ s} {e : Term (ꜱ N)} → ⇧ᵗ< ᴢ > τ₁ ∷ mapⱽ ⇧ᵗ< ᴢ > ℾ ⊢ e ⦂ τ₂ , s ∷ Σ₁
    → ⇧ᵗ< ᴢ > τ₁ ∷ mapⱽ ⇧ᵗ< ᴢ > ℾ ⊢ e ⦂ τ₂ , s ∷ Σ₂
    → Σ₁ ≡ Σ₂
  L21 : ∀ {N} {γ₁ γ′₁ : γ[ N ]} {e e′} → γ₁ ⊢ e ⇓ (ƛ⦂ e′ ∥ γ′₁) → γ₁ ≡ γ′₁
  L21-1 : ∀ {N} {γ′₁ : γ[ N ]} {e₁ e′₁ γ′₂} {e′₂} →  γ′₁ ⊢ e₁ ⇓ (ƛ⦂ e′₁ ∥ γ′₁) → γ′₂ ⊢ e₁ ⇓ (ƛ⦂ e′₂ ∥ γ′₂) → e′₁ ≡ e′₂
  L22 : ∀ {N} → (Σ₂ Σ′ : Σ[ N ]) → (τ : τ (ꜱ N)) →  (Σ′ ⟨⟨ substΣ/τ ᴢ Σ₂ τ ⟩⟩) ≡ substSx/τ< ᴢ > (Σ₂ ⨰ Σ′) (⇧ᵗ< ᴢ > ((⟨ 0 ⟩ ∷ Σ′) ⟨⟨ τ ⟩⟩))
  subsumption : ∀ {N} {τ τ₁ τ₂ v₁ v₂  Σ′ } {s₂ s₃ ε₁ ε₂ ε₃ ε₄} {Σ₁ Σ₁₁ Σ₁₂ Σ₂ Σ₃ : Σ[ N ]}  → (τ₁ τ[⊔] τ₂) ≡ ⟨ τ ⟩
    → ⟨ v₁ , v₂ ⟩∈𝒱′⟦ (Σ′ ⟨⟨ τ₁ ⟩⟩) ː ε₃ , ε₄ ː (s₂ ×[qty] ((Σ₁ ⨰ Σ′) +[qty] (⟨ 0 ⟩ +[qty] (Σ′ ⨰ Σ₁₁)))) +[qty] (Σ₂ ⨰ Σ′)⟧
    → ⟨ v₁ , v₂ ⟩∈𝒱′⟦ (Σ′ ⟨⟨ τ ⟩⟩) ː ε₁ , ε₂ ː (([vec]⌉ Σ₁ ⌈⸢ `∞ ⸣ + ((s₂ ⨵ Σ₁₁) + Σ₂) ⊔ ((s₃ ⨵ Σ₁₂) + Σ₃)) ⨰ Σ′)⟧


typeSafety : ∀ {N} {e : Term N} {Γ : Γ[ N ]} {Σ Σ′ : Σ[ N ]} {v} {γ : γ[ N ]} {τ : τ N} → Γ ⊢ e ⦂ τ , Σ → γ ⊢ e ⇓ v → ⊢ v ⦂ Σ′ ⟨⟨ τ ⟩⟩
typeSafety ⊢`ℝ ⊢`ℝ = ⊢𝓇
typeSafety ⊢`𝔹 ⊢`𝔹 = ⊢𝒷
typeSafety (⊢ ⊢e `+ ⊢e₁) (⊢ e⇓v `+ e⇓v₁) = ⊢𝓇
typeSafety (⊢ ⊢e `× ⊢e₁) (⊢ e⇓v `× e⇓v₁) = ⊢𝓇
typeSafety (⊢ ⊢e `≤ ⊢e₁) (⊢ e⇓v `≤ e⇓v₁) = ⊢𝒷
typeSafety (⊢`var x) (⊢`var x⇓v) = {!   !}
typeSafety ⊢`tt ⊢`tt = ⊢tt
typeSafety (⊢`inl ⊢e) (⊢`inl e⇓v) = ⊢inl (typeSafety ⊢e e⇓v)
typeSafety (⊢`inr ⊢e) (⊢`inr e⇓v) = ⊢inr (typeSafety ⊢e e⇓v)
typeSafety (⊢`case ⊢e₁ ⊢e₂ ⊢e₃ x) (⊢`case/l e⇓v₁ e⇓v₂) = {!   !}
typeSafety (⊢`case ⊢e₁ ⊢e₂ ⊢e₃ x) (⊢`case/r e⇓v₁ e⇓v₂) = {!    !}
typeSafety (⊢`if ⊢e₁ ⊢e₂ ⊢e₃) (⊢`if-true e⇓v₁ e⇓v₂) = typeSafety ⊢e₂ e⇓v₂
typeSafety (⊢`if ⊢e₁ ⊢e₂ ⊢e₃) (⊢`if-false e⇓v₁ e⇓v₃) = typeSafety ⊢e₃ e⇓v₃
typeSafety (⊢`let ⊢e₁ ⊢e₂) (⊢`let e⇓v₁ e⇓v₂) with typeSafety ⊢e₁ e⇓v₁ | typeSafety ⊢e₂ e⇓v₂
typeSafety (⊢`let ⊢e₁ ⊢e₂) (⊢`let e⇓v₁ e⇓v₂) | IH₁ | IH₂ = {!   !}
-----
-- typeSafety (⊢`λ ⊢e) ⊢`λ = {!    !}
typeSafety (⊢`λ ⊢e) ⊢`λ = {! ⊢`λ   !}

typeSafety (⊢`app ⊢e₁ ⊢e₂) (⊢`app e⇓v₁ e⇓v₂ e⇓v₃) = {!   !}
typeSafety (⊢` ⊢e₁ pair ⊢e₂) (⊢` e⇓v₁ pair e⇓v₂) = ⊢pair (typeSafety ⊢e₁ e⇓v₁) (typeSafety ⊢e₂ e⇓v₂)
typeSafety (⊢`fst ⊢e) (⊢`fst e⇓v) = {! typeSafety ⊢e e⇓v  !}
typeSafety (⊢`snd ⊢e) (⊢`snd e⇓v) = {! typeSafety ⊢e e⇓v   !}
