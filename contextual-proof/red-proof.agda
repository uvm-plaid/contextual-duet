{-# OPTIONS --allow-unsolved-metas #-}
module red-proof where

open import rules public
-- open import lemmas public
open import logical-relations public

postulate
  typeSafety : ∀ {N} {e : Term N} {Γ : Γ[ N ]} {Σ Σ′ Σ₀ : Σ[ N ]} {v} {γ : γ[ N ]} {τ : τ N} → Γ , Σ₀ ⊢ e ⦂ τ , Σ → γ ⊢ e ⇓ v → ⊢ v ⦂ Σ′ ⟨⟨ τ ⟩⟩
  fp : ∀ {N} {Γ : Γ[ N ]} {ℾ e τ Σ γ₁ γ₂ Σ′ Σ₀} → ℾ ⊢ γ₁ → ℾ ⊢ γ₂ → Γ , Σ₀ ⊢ e ⦂ τ , Σ → ⟨ γ₁ , γ₂ ⟩∈𝒢⟦ Σ′ ː ℾ ⟧ → ⟨ γ₁ ⊢ e , γ₂ ⊢ e ⟩∈ℰ⟦ Σ ⨰ Σ′ ː (Σ′ ⟨⟨ τ ⟩⟩) ⟧

-- Theorem 1.1.2 (Fundamental Property / (Metric Preservation in Fuzz)).
fp₂ : ∀ {N} {Γ : Γ[ N ]} {ℾ e τ Σ Σ₀ γ₁ γ₂ Σ′} → ℾ ⊢ γ₁ → ℾ ⊢ γ₂
  → Γ , Σ₀ ⊢ₚ e ⦂ τ , Σ
  → ⟨ γ₁ , γ₂ ⟩∈𝒢⟦ Σ′ ː ℾ ⟧
  → ⟨ γ₁ ⊢ e , γ₂ ⊢ e ⟩∈ℰₚ⟦ L1N Σ ː (Σ′ ⟨⟨ τ ⟩⟩) ⟧
fp₂ ⊢γ₁ ⊢γ₂ (⊢`papp {Σ₁ = Σ₁} {Σ₂ = Σ₂} {p = p} e₁ e₂) r[γ₁,γ₂] v₁ v₂ r₁ r₂ ε₁ ε₂ ⟨ ⊢`papp {γ = γ₁} {e′ = e′₁} {𝓋₁ = 𝓋₁} ⊢e₁₁ ⊢e₁₂ ⊢e₁₂′ , ⊢`papp {γ = γ₂} {e′ = e′₂} {𝓋₁ = 𝓋₂} ⊢e₂₁ ⊢e₂₂ ⊢e₂₂′ ⟩ pr₁ pr₂
  with fp ⊢γ₁ ⊢γ₂ e₁ r[γ₁,γ₂] (pƛ⦂ e′₁ ∥ γ₁) (pƛ⦂ e′₂ ∥ γ₂) (typeSafety e₁ ⊢e₁₁) (typeSafety e₁ ⊢e₂₁) ⟨ ⊢e₁₁ , ⊢e₂₁ ⟩
     | fp ⊢γ₁ ⊢γ₂ e₂ r[γ₁,γ₂] 𝓋₁ 𝓋₂ (typeSafety e₂ ⊢e₁₂) (typeSafety e₂ ⊢e₂₂) ⟨ ⊢e₁₂ , ⊢e₂₂ ⟩
... | IH₁ | IH₂ = {!   !}
