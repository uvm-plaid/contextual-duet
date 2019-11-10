{-# OPTIONS --allow-unsolved-metas #-}
module post where

open import rules public
open import logical-relations public

postulate
  L1 : ∀ (N : ℕ) → ∣ N - N ∣ ≡ 0
  L2 : ∀ (N : ℕ) → ⟨ ∣ N - N ∣ ⟩ ≡< qty ℕ > ⟨ 0 ⟩
  L3 : ∀ {a b c d N : ℕ} {Σ₁ Σ₂ Σ₃ : Σ[ N ]} → ⟨ ∣ a - b ∣ ⟩ ≤ (Σ₁ ⨰ Σ₃) → ⟨ ∣ c - d ∣ ⟩ ≤ (Σ₂ ⨰ Σ₃) → ⟨ ∣ (a + c) - (b + d) ∣ ⟩ ≤ ((Σ₁ + Σ₂) ⨰ Σ₃)
  L4 : ∀ {N} (Σ₁ Σ₂ Σ₃ : Σ[ N ]) → (Σ₁ ⨰ Σ₃) + (Σ₂ ⨰ Σ₃) ≡ ((Σ₁ + Σ₂) ⨰ Σ₃)
  L5 : ∀ {N} (Σ₁ Σ₂ : Σ[ N ]) → (Σ₁ ⨰ Σ₂) ≡ (Σ₂ ⨰ Σ₁)
  L6 : ∀ {N} (Σ₁ Σ₂ : Σ[ N ]) → [vec]⌉ Σ₁ ⌈⸢ `∞ ⸣ ⨰ Σ₂ ≡ ⟨ 0 ⟩ ∨  [vec]⌉ Σ₁ ⌈⸢ `∞ ⸣ ⨰ Σ₂ ≡ `∞
  L7 : ∀ {N} {γ₁ γ₂ : γ[ N ]} {Σ : Σ[ N ]} {ℾ : ℾ[ N ]} {x : idx N }
    → ⟨ γ₁ , γ₂ ⟩∈𝒢⟦ Σ ː ℾ ⟧
    → (ε₁ : ⊢ γ₁ #[ x ] ⦂ ℾ #[ x ])
    → (ε₂ : ⊢ γ₂ #[ x ] ⦂ ℾ #[ x ])
    → ⟨ γ₁ #[ x ] , γ₂ #[ x ] ⟩∈𝒱′⟦ ℾ #[ x ] ː ε₁ , ε₂ ː Σ #[ x ] ⟧
  typeSafety : ∀ {N} {e : Term N} {Γ : Γ[ N ]} {Σ Σ′ : Σ[ N ]} {v} {γ : γ[ N ]} {τ : τ N} → Γ ⊢ e ⦂ τ , Σ → γ ⊢ e ⇓ v → ⊢ v ⦂ Σ′ ⟨⟨ τ ⟩⟩
  L8 : ∀ {N} {s} {Σ : Σ[ N ]} {τ v} → (⊢ v ⦂ (substSx/τ s (⇧ᵗ (⇧ˢ Σ ⟨⟨ τ ⟩⟩)))) → (⊢ v ⦂ ((s ∷ Σ) ⟨⟨ τ ⟩⟩))
  L9 : ∀ {N} (s : Sens) (Σ : Σ[ N ]) (τ : τ (ꜱ N)) → (substSx/τ s (⇧ᵗ (⇧ˢ Σ ⟨⟨ τ ⟩⟩))) ≡ (s ∷ Σ) ⟨⟨ τ ⟩⟩
  -- these two should be by def.
  L10 : ∀ {v τ₁ s₁ s₂ τ₂} → ⊢ (inl v) ⦂ τ₁ ∥ s₁ ∔ zero ⊕ s₂ ∔ zero ∥ τ₂ → ⊢ v ⦂ τ₁
  L11 : ∀ {v τ₁ s₁ s₂ τ₂} → ⊢ (inr v) ⦂ τ₁ ∥ s₁ ∔ zero ⊕ s₂ ∔ zero ∥ τ₂ → ⊢ v ⦂ τ₂
