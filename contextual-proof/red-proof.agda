{-# OPTIONS --allow-unsolved-metas #-}
module red-proof where

open import rules public
open import lemmas public
open import logical-relations public

postulate
  fp : ∀ {N} {Γ : Γ[ N ]} {ℾ e τ Σ γ₁ γ₂ Σ′ Σ₀} → ℾ ⊢ γ₁ → ℾ ⊢ γ₂ → Γ , Σ₀ ⊢ e ⦂ τ , Σ → ⟨ γ₁ , γ₂ ⟩∈𝒢⟦ Σ′ ː ℾ ⟧ → ⟨ γ₁ ⊢ e , γ₂ ⊢ e ⟩∈ℰ⟦ Σ ⨰ Σ′ ː (Σ′ ⟨⟨ τ ⟩⟩) ⟧

-- Theorem 1.1.2 (Fundamental Property / (Metric Preservation in Fuzz)).
fp₂ : ∀ {N} {Γ : Γ[ N ]} {ℾ e τ Σ Σ₀ γ₁ γ₂ Σ′} → ℾ ⊢ γ₁ → ℾ ⊢ γ₂
  → Γ , Σ₀ ⊢ₚ e ⦂ τ , Σ
  → ⟨ γ₁ , γ₂ ⟩∈𝒢⟦ Σ′ ː ℾ ⟧
  → ⟨ γ₁ ⊢ e , γ₂ ⊢ e ⟩∈ℰₚ⟦ L1N Σ ː (Σ′ ⟨⟨ τ ⟩⟩) ⟧
fp₂ {Σ₀ = Σ₀} {Σ′ = Σ′} ⊢γ₁ ⊢γ₂ (⊢`papp {Σ₁ = Σ₁} {Σ₂ = Σ₂} {τ₂ = τ₂} {p = p} e₁ e₂) r[γ₁,γ₂]
  v₁ v₂ r₁ r₂ ε₁ ε₂
  ⟨ ⊢`papp {γ = γ₁} {e′ = e′₁} {𝓋₁ = 𝓋₁} ⊢e₁₁ ⊢e₁₂ ⊢e₁₂′ , ⊢`papp {γ = γ₂} {e′ = e′₂} {𝓋₁ = 𝓋₂} ⊢e₂₁ ⊢e₂₂ ⊢e₂₂′ ⟩
  pr₁ pr₂
  with fp ⊢γ₁ ⊢γ₂ e₁ r[γ₁,γ₂] (pƛ⦂ e′₁ ∥ γ₁) (pƛ⦂ e′₂ ∥ γ₂) (typeSafety e₁ ⊢e₁₁) (typeSafety e₁ ⊢e₂₁) ⟨ ⊢e₁₁ , ⊢e₂₁ ⟩
     | fp ⊢γ₁ ⊢γ₂ e₂ r[γ₁,γ₂] 𝓋₁ 𝓋₂ (typeSafety e₂ ⊢e₁₂) (typeSafety e₂ ⊢e₂₂) ⟨ ⊢e₁₂ , ⊢e₂₂ ⟩
... | IH₁ | IH₂ with typeSafety {Σ′ = Σ′} e₁ ⊢e₁₁ | typeSafety {Σ′ = Σ′} e₁ ⊢e₂₁ | L9 Σ₂ Σ′ τ₂ | IH₁
… | ⊢pλ {Γ = Γ₁} {τ₁ = τ₁₁} {τ₂ = τ₂₁} {p = px†₁} {p′ = p†₁} {Σ = Σ′₁} ⊢γ₁′ ⊢e₁ ε₁₁ ε₁₂ ε₁₃
  | ⊢pλ {Γ = Γ₂} {τ₁ = τ₁₂} {τ₂ = τ₂₂} {p = px†₂} {p′ = p†₂} {Σ = Σ′₂} ⊢γ₂′ ⊢e₂ ε₂₁ ε₂₂ ε₂₃
  | ZZ
  | ⟨∃ ↯ , ⟨ ⟨ ⟨ ⟨ ↯ , ↯ ⟩ , ↯ ⟩ , ↯ ⟩ , IH′ ⟩ ⟩
  with IH′ {v₁ = 𝓋₁} {v₂ = 𝓋₂} {ε₁ = (typeSafety e₂ ⊢e₁₂)} {ε₂ = (typeSafety e₂ ⊢e₂₂)} {s′ = Σ₂ ⨰ Σ′}
            {Σ₀ = Σ₀} {!   !} IH₂ v₁ v₂ r₁ r₂ ((subst[( λ X → ⊢ v₁ ⦂ X )] ZZ ε₁))
            ((subst[( λ X → ⊢ v₂ ⦂ X )] ZZ ε₂)) ⟨ ( {!   !} ⊢e₁₂′) , {!   !}  ⊢e₂₂′ ⟩ pr₁ pr₂
... | IH′′ = {! IH′′  !}
