{-# OPTIONS --allow-unsolved-metas #-}
module red-proof where

open import rules public
open import lemmas public
open import logical-relations public

postulate
  fp : ∀ {N} {Γ : Γ[ N ]} {ℾ e τ Σ γ₁ γ₂ Σ′ Σ₀} → ℾ ⊢ γ₁ → ℾ ⊢ γ₂ → Γ , Σ₀ ⊢ e ⦂ τ , Σ → ⟨ γ₁ , γ₂ ⟩∈𝒢⟦ Σ′ ː ℾ ⟧ → ⟨ γ₁ ⊢ e , γ₂ ⊢ e ⟩∈ℰ⟦ Σ ⨰ Σ′ ː (Σ′ ⟨⟨ τ ⟩⟩) ⟧

  -- given two equal length vectors, and the operations:
    -- (1) truncate each, then take the dot product ([vec]⌉ Σ′ ⌈⸢ ⟨ 1 ⟩ ⸣ ⨰ [vec]⌉ Σ ⌈⸢ ⟨ p ⟩ ⸣ ) or,
    -- (2) take the dot product, then truncate the result ([vec]⌉ Σ′ ⨰ Σ ⌈⸢ ⟨ 1 ⟩ ⸣ × p)
    -- both operations also involve potential "scaling" of the constant p by 0 or 1
  truncDotTrichotomy : ∀ {N} {p k : Priv} → (Σ′ Σ : Σ[ N ])
    -- the possible outcomes are in three categories:
    -- at least one of the vectors is the constant zero vector, so both operations equal zero
    → ([vec]⌉ Σ′ ⌈⸢ ⟨ 1 ⟩ ⸣ ⨰ [vec]⌉ Σ ⌈⸢ p ⸣ ) ≡ zero ∧ (⌉ Σ′ ⨰ Σ ⌈⸢ ⟨ 1 ⟩ ⸣ × p) ≡ zero
    -- there is at most one dot product "match", i.e. all other elements of the product equal zero
    -- both operations equal the constant p
    ∨ ([vec]⌉ Σ′ ⌈⸢ ⟨ 1 ⟩ ⸣ ⨰ [vec]⌉ Σ ⌈⸢ p ⸣ ) ≡ p ∧ (⌉ Σ′ ⨰ Σ ⌈⸢ ⟨ 1 ⟩ ⸣ × p) ≡ p
    -- there is at least one dot product match
    -- operation (1) equals k·p where 1 ≤ k
    -- operation (2) equals p
    ∨ ([vec]⌉ Σ′ ⌈⸢ ⟨ 1 ⟩ ⸣ ⨰ [vec]⌉ Σ ⌈⸢ p ⸣ ) ≡ k × p ∧ one ≤ k ∧ (⌉ Σ′ ⨰ Σ ⌈⸢ ⟨ 1 ⟩ ⸣ × p) ≡ p

-- Theorem 1.1.2 (Fundamental Property / (Metric Preservation in Fuzz)).
fp₂ : ∀ {N} {Γ : Γ[ N ]} {ℾ e τ Σ Σ₀ γ₁ γ₂ Σ′} → ℾ ⊢ γ₁ → ℾ ⊢ γ₂
  → Γ , Σ₀ ⊢ₚ e ⦂ τ , Σ
  → ⟨ γ₁ , γ₂ ⟩∈𝒢⟦ Σ′ ː ℾ ⟧
  → ⟨ γ₁ ⊢ e , γ₂ ⊢ e ⟩∈ℰₚ⟦ [vec]⌉ Σ′ ⌈⸢ one ⸣ ⨰ Σ ː (Σ′ ⟨⟨ τ ⟩⟩) ⟧
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
... | IH′′ rewrite lzero[⨰]< Σ′ >
    -- | runit[+][qty]< ([vec]⌉ Σ′ ⌈⸢ ⟨ 1 ⟩ ⸣ ⨰ Σ₁) >
    | L0-3 (([vec]⌉ Σ′ ⌈⸢ ⟨ 1 ⟩ ⸣ ⨰ Σ₁) +[qty] ⟨ 0 ⟩) = {! IH′′  !}
