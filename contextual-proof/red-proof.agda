{-# OPTIONS --allow-unsolved-metas #-}
module red-proof where

open import rules public
-- open import lemmas public
open import logical-relations public

-- Theorem 1.1.2 (Fundamental Property / (Metric Preservation in Fuzz)).
fp₂ : ∀ {N} {Γ : Γ[ N ]} {ℾ e τ Σ Σ₀ γ₁ γ₂ Σ′} → ℾ ⊢ γ₁ → ℾ ⊢ γ₂
  → Γ , Σ₀ ⊢ₚ e ⦂ τ , Σ
  → ⟨ γ₁ , γ₂ ⟩∈𝒢⟦ Σ′ ː ℾ ⟧
  → ⟨ γ₁ ⊢ e , γ₂ ⊢ e ⟩∈ℰₚ⟦ L1N Σ ː (Σ′ ⟨⟨ τ ⟩⟩) ⟧
fp₂ ⊢γ₁ ⊢γ₂ ⊢ₚe r[γ₁,γ₂] v₁ v₂ r₁ r₂ ε₁ ε₂ ⟨ δ₁ , δ₂ ⟩ pr₁ pr₂ = {!   !}
