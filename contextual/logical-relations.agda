{-# OPTIONS --allow-unsolved-metas #-}
module logical-relations where

open import rules public

mutual
  -- this is for sensitivity, we will need another one for privacy
  ⟨_⊢_,_⊢_⟩∈ℰ⟦_ː_⟧ : ∀ {N} → γ[ N ] → Term N → γ[ N ] → Term N → Sens → τ ᴢ → Set
  ⟨ γ₁ ⊢ e₁ , γ₂ ⊢ e₂ ⟩∈ℰ⟦ s ː τ ⟧ = ∀ v₁ v₂ → (ε₁ : ⊢ v₁ ⦂ τ) → (ε₂ : ⊢ v₂ ⦂ τ) → (γ₁ ⊢ e₁ ⇓ v₁) ∧ (γ₂ ⊢ e₂ ⇓ v₂) → ⟨ v₁ , v₂ ⟩∈𝒱′⟦ τ ː ε₁ , ε₂ ː s ⟧

  -- ⟨_,_⟩∈𝒢⟦_ː_⟧ : ∀ {N} → γ[ N ] → γ[ N ] → Σ[ N ] → ℾ[ N ] → Set
  -- ⟨ γ₁ , γ₂ ⟩∈𝒢⟦ Σ ː ℾ ⟧ = ∀ x → (ε₁ : ⊢ γ₁ #[ x ] ⦂ ℾ #[ x ]) → (ε₂ : ⊢ γ₂ #[ x ] ⦂ ℾ #[ x ]) → ⟨ γ₁ #[ x ] , γ₂ #[ x ] ⟩∈𝒱′⟦ ℾ #[ x ] ː ε₁ , ε₂ ː Σ #[ x ] ⟧

  ⟨_,_⟩∈𝒢⟦_ː_⟧ : ∀ {N} → γ[ N ] → γ[ N ] → Σ[ N ] → ℾ[ N ] → Set
  ⟨ [] , [] ⟩∈𝒢⟦ [] ː [] ⟧ = 𝟙
  ⟨ v₁ ∷ γ₁ , v₂ ∷ γ₂ ⟩∈𝒢⟦ s ∷ Σ ː τ ∷ ℾ ⟧ = ∃ δ₁ ⦂ (⊢ v₁ ⦂ τ) ST ∃ δ₂ ⦂ (⊢ v₂ ⦂ τ) ST ⟨ v₁ , v₂ ⟩∈𝒱′⟦ τ ː δ₁ , δ₂ ː s ⟧ ∧ ⟨ γ₁ , γ₂ ⟩∈𝒢⟦ Σ ː ℾ ⟧

  -- data ⟨_,_⟩∈𝒢⟦_ː_⟧ : ∀ {N} → γ[ N ] → γ[ N ] → Σ[ N ] → ℾ[ N ] → Set where
  --   [] : ⟨ [] , [] ⟩∈𝒢⟦ [] ː [] ⟧
  --   _∷_ : ∀ {N} {v₁ v₂ : 𝓋} {t : τ ᴢ} {δ₁ : ⊢ v₁ ⦂ t} {δ₂ : ⊢ v₂ ⦂ t} {γ₁ γ₂ : γ[ N ]} {Γ : ℾ[ N ]} {s : Sens} {Σ : Σ[ N ]} →
  --       ⟨ v₁ , v₂ ⟩∈𝒱′⟦ t ː δ₁ , δ₂ ː s ⟧
  --     → ⟨ γ₁ , γ₂ ⟩∈𝒢⟦ Σ ː Γ ⟧
  --     → ⟨ v₁ ∷ γ₁ , v₂ ∷ γ₂ ⟩∈𝒢⟦ s ∷ Σ ː t ∷ Γ ⟧
      

  {-# TERMINATING #-}
  ⟨_,_⟩∈𝒱′⟦_ː_,_ː_⟧ : ∀ (v₁ v₂ : 𝓋) (t : τ ᴢ) → ⊢ v₁ ⦂ t → ⊢ v₂ ⦂ t → Sens →  Set
  ⟨ .(ƛ⦂ e₁ ∥ γ₁) , .(ƛ⦂ e₂ ∥ γ₂) ⟩∈𝒱′⟦ ƛ⦂ τ₁ ⇒[ s′′ ∔ s‴ ] τ₂
                                 ː ⊢λ {N = N₁} {ℾ = ℾ₁} {e = e₁} {γ = γ₁} H₁₁ H₁₂ H₁₃ H₁₄ H₁₅
                                 , ⊢λ {N = N₂} {ℾ = ℾ₂} {e = e₂} {γ = γ₂} H₂₁ H₂₂ H₂₃ H₂₄ H₂₅
                                 ː s ⟧ =
    ∃ ε ⦂ N₁ ≡ N₂ ST
    (subst[(λ N → ⟬ τ N ⟭[ N ] )] ε ℾ₁ ≡ ℾ₂
    → ∀ {v₁ v₂ ε₁ ε₂ s s′ s′′ Σ Σ′} → ⟨ subst[(λ N → γ[ N ] )] ε γ₁ , γ₂ ⟩∈𝒢⟦ Σ′ ː mapⱽ (instantiateΣ/τ Σ′) ℾ₂ ⟧
    → ⟨ v₁ , v₂ ⟩∈𝒱′⟦ τ₁ ː ε₁ , ε₂ ː s′′ ⟧
    → ⟨ (v₁ ∷ subst[(λ N → γ[ N ] )] ε γ₁) ⊢ subst[(λ N → Term (ꜱ N) )] ε e₁ , (v₂ ∷ γ₂) ⊢ e₂ ⟩∈ℰ⟦ (s + (Σ ⨰ Σ′) + (s′ × s′′)) ː (substSx/τ s′′ τ₂) ⟧)
  ⟨ v₁₁ pair v₁₂ , v₂₁ pair v₂₂ ⟩∈𝒱′⟦ τ₁ ∥ s₁ ∔ [] ⊗ s₂ ∔ [] ∥ τ₂ ː ⊢pair δ₁₁ δ₁₂ , ⊢pair δ₂₁ δ₂₂ ː s ⟧ =
    ⟨ v₁₁ , v₂₁ ⟩∈𝒱′⟦ τ₁ ː δ₁₁ , δ₂₁ ː s + s₁ ⟧
    ∧
    ⟨ v₁₂ , v₂₂ ⟩∈𝒱′⟦ τ₂ ː δ₁₂ , δ₂₂ ː s + s₂ ⟧
  ⟨ inl v₁ , inl v₂ ⟩∈𝒱′⟦ τ₁ ∥ s₁ ∔ [] ⊕ s₂ ∔ [] ∥ τ₂ ː ⊢inl δ₁ , ⊢inl δ₂ ː s ⟧ =
    ⟨ v₁ , v₂ ⟩∈𝒱′⟦ τ₁ ː δ₁ , δ₂ ː s + s₁ ⟧
  ⟨ inl v₁ , inr v₂ ⟩∈𝒱′⟦ τ₁ ∥ s₁ ∔ [] ⊕ s₂ ∔ [] ∥ τ₂ ː ⊢inl δ₁ , ⊢inr δ₂ ː s ⟧ = s ≡ `∞
  ⟨ inr v₁ , inl v₂ ⟩∈𝒱′⟦ τ₁ ∥ s₁ ∔ [] ⊕ s₂ ∔ [] ∥ τ₂ ː ⊢inr δ₁ , ⊢inl δ₂ ː s ⟧ = s ≡ `∞
  ⟨ inr v₁ , inr v₂ ⟩∈𝒱′⟦ τ₁ ∥ s₁ ∔ [] ⊕ s₂ ∔ [] ∥ τ₂ ː ⊢inr δ₁ , ⊢inr δ₂ ː s ⟧ =
    ⟨ v₁ , v₂ ⟩∈𝒱′⟦ τ₂ ː δ₁ , δ₂ ː s + s₂ ⟧
  ⟨ v₁ , v₂ ⟩∈𝒱′⟦ unit ː δ₁ , δ₂ ː s ⟧ = v₁ ≡ tt ∧ v₂ ≡ tt
  ⟨ (𝓇 r₁) , (𝓇 r₂) ⟩∈𝒱′⟦ ℝT ː ⊢𝓇 , ⊢𝓇 ː s ⟧ = ⟨ ∣ r₁ - r₂ ∣ ⟩ ≤ s
  ⟨ v₁ , v₂ ⟩∈𝒱′⟦ 𝔹T ː δ₁ , δ₂ ː s ⟧ = {!!}