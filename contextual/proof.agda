{-# OPTIONS --allow-unsolved-metas #-}
module proof where

open import rules public

mutual
  data ⟨_,_⟩∈𝒱⟦_ː_⟧ : 𝓋 → 𝓋 → Sens → 𝓋τ ᴢ → Set where

    𝒱ℝ : ∀ {r₁ r₂ : ℕ} {s : Sens}
      → ⟨ ∣ r₁ - r₂ ∣ ⟩ ≤ s
      ------------------------------
      → ⟨ 𝓇 r₁ , 𝓇 r₂ ⟩∈𝒱⟦ s ː ℝT ⟧

    𝒱⊕₁ : ∀ {v₁ v₂ τ₁ τ₂ s s₁ s₂}
      → ⟨ v₁ , v₂ ⟩∈𝒱⟦ s + s₁ ː τ₁ ⟧
      ------------------------------
      → ⟨ inl v₁ , inl v₂ ⟩∈𝒱⟦ s ː τ₁ ∥ s₁ ∔ [] ⊕ s₂ ∔ [] ∥ τ₂ ⟧

    𝒱⊕₂ : ∀ {v₁ v₂ τ₁ τ₂ s s₁ s₂}
      → ⟨ v₁ , v₂ ⟩∈𝒱⟦ s + s₂ ː τ₁ ⟧
      ------------------------------
      → ⟨ inr v₁ , inr v₂ ⟩∈𝒱⟦ s ː τ₁ ∥ s₁ ∔ [] ⊕ s₂ ∔ [] ∥ τ₂ ⟧

    𝒱⊕₃ : ∀ {v₁ v₂ τ₁ τ₂ s s₁ s₂}
      → s ≡ `∞
      ------------------------------
      → ⟨ inl v₁ , inr v₂ ⟩∈𝒱⟦ s ː τ₁ ∥ s₁ ∔ [] ⊕ s₂ ∔ [] ∥ τ₂ ⟧

    𝒱⊗ : ∀ {v₁₁ v₁₂ v₂₁ v₂₂ s s₁ s₂ τ₁ τ₂}
      → ⟨ v₁₁ , v₂₁ ⟩∈𝒱⟦ s + s₁ ː τ₁ ⟧
      → ⟨ v₁₂ , v₂₂ ⟩∈𝒱⟦ s + s₂ ː τ₂ ⟧
      ----------------------------------------------------------------
      → ⟨ (v₁₁ pair v₁₂) , (v₂₁ pair v₂₂) ⟩∈𝒱⟦ s ː τ₁ ∥ s₁ ∔ [] ⊗ s₂ ∔ [] ∥ τ₂ ⟧

    𝒱λ : ∀ {N e₁ e₂ γ₁ γ₂ τ₁ τ₂ s s′ s′′′ Σ Σ′}
      → (∀ {v₁ v₂ s′′} → ∃ ℾ ⦂ (ℾ[ N ]) ST ⟨ γ₁ , γ₂ ⟩∈𝒢⟦ Σ′ ː ℾ ⟧
      → ⟨ v₁ , v₂ ⟩∈𝒱′⟦ {!   !} ː {!   !} , {!   !} ː {!   !} ⟧
      → ⟨ (v₁ ∷ γ₁) ⊢ e₁ , (v₂ ∷ γ₂) ⊢ e₂ ⟩∈ℰ⟦ (s + (Σ ⨰ Σ′) + (s′ × s′′)) ː (substSx/τ s′′ τ₂) ⟧)
      ---------------------------------------------------------------------------------
      → ⟨ ƛ⦂ e₁ ∥ γ₁ , ƛ⦂ e₂ ∥ γ₂ ⟩∈𝒱⟦ s ː ƛ⦂ τ₁ ⇒[ (s′ + Σ ⨰ Σ′ ) ∔ [ s′′′ ] ] τ₂ ⟧

  -- this is for sensitivity, we will need another one for privacy
  ⟨_⊢_,_⊢_⟩∈ℰ⟦_ː_⟧ : ∀ {N} → γ[ N ] → Term N → γ[ N ] → Term N → Sens → 𝓋τ ᴢ → Set
  ⟨ γ₁ ⊢ e₁ , γ₂ ⊢ e₂ ⟩∈ℰ⟦ s ː τ ⟧ = ∀ v₁ v₂ → (γ₁ ⊢ e₁ ⇓ v₁) ∧ (γ₂ ⊢ e₂ ⇓ v₂) → ⟨ v₁ , v₂ ⟩∈𝒱⟦ s ː τ ⟧

  ⟨_,_⟩∈𝒢⟦_ː_⟧ : ∀ {N} → γ[ N ] → γ[ N ] → Σ[ N ] → ℾ[ N ] → Set
  ⟨ γ₁ , γ₂ ⟩∈𝒢⟦ Σ ː ℾ ⟧ = ∀ x → ⟨ γ₁ #[ x ] , γ₂ #[ x ] ⟩∈𝒱⟦ Σ #[ x ] ː ℾ #[ x ] ⟧

  ⟨_,_⟩∈𝒱′⟦_ː_,_ː_⟧ : ∀ (v₁ v₂ : 𝓋) (t : 𝓋τ ᴢ) → [] ⊢ v₁ ⦂ t → [] ⊢ v₂ ⦂ t → Sens →  Set
  ⟨ v₁ , v₂ ⟩∈𝒱′⟦ ƛ⦂ x ⇒[ x₁ ∔ x₂ ] τ₁ ː δ₁ , δ₂ ː s ⟧ = {!   !} -- ∀ s″ v₁ v₂ → {!   !} → {!   !}
  ⟨ v₁₁ pair v₁₂ , v₂₁ pair v₂₂ ⟩∈𝒱′⟦ τ₁ ∥ s₁ ∔ [] ⊗ s₂ ∔ [] ∥ τ₂ ː ⊢pair δ₁₁ δ₁₂ , ⊢pair δ₂₁ δ₂₂ ː s ⟧ =
    ⟨ v₁₁ , v₂₁ ⟩∈𝒱′⟦ τ₁ ː δ₁₁ , δ₂₁ ː s + s₁ ⟧
    ∧
    ⟨ v₁₂ , v₂₂ ⟩∈𝒱′⟦ τ₂ ː δ₁₂ , δ₂₂ ː s + s₂ ⟧
  ⟨ v₁ , v₂ ⟩∈𝒱′⟦ τ₁ ∥ x ∔ x₁ ⊕ x₂ ∔ x₃ ∥ τ₂ ː δ₁ , δ₂ ː s ⟧ = {!!}
  ⟨ v₁ , v₂ ⟩∈𝒱′⟦ unit ː δ₁ , δ₂ ː s ⟧ = {!!}
  ⟨ v₁ , v₂ ⟩∈𝒱′⟦ ℝT ː δ₁ , δ₂ ː s ⟧ = {!!}
  ⟨ v₁ , v₂ ⟩∈𝒱′⟦ 𝔹T ː δ₁ , δ₂ ː s ⟧ = {!!}

_⟨⟨_⟩⟩ : ∀ {N} → Σ[ N ] → τ N → 𝓋τ ᴢ
Σ ⟨⟨ ƛ⦂ τ₁ ⇒[ x ] τ₂ ⟩⟩ = {!!}
Σ ⟨⟨ τ₁ ∥ x ⊗ x₁ ∥ τ₂ ⟩⟩ = {!!}
Σ ⟨⟨ τ₁ ∥ x ⊕ x₁ ∥ τ₂ ⟩⟩ = {!!}
Σ ⟨⟨ unit ⟩⟩ = {!!}
Σ ⟨⟨ ℝT ⟩⟩ = ℝT
Σ ⟨⟨ 𝔹T ⟩⟩ = {!!}

-- Theorem 1.1 (Fundamental Property / (Metric Preservation in Fuzz)).

postulate
  L1 : ∀ (N : ℕ) → ∣ N - N ∣ ≡ 0

fp : ∀ {N} {Γ : Γ[ N ]} {ℾ e τ Σ γ₁ γ₂ Σ′} → Γ ⊢ e ⦂ τ , Σ → ⟨ γ₁ , γ₂ ⟩∈𝒢⟦ Σ′ ː ℾ ⟧ → ⟨ γ₁ ⊢ e , γ₂ ⊢ e ⟩∈ℰ⟦ Σ ⨰ Σ′ ː (Σ′ ⟨⟨ τ ⟩⟩) ⟧
fp {Σ′ = Σ′} ⊢`ℝ b (𝓇 r₁) (𝓇 r₁) ⟨ ⊢`ℝ , ⊢`ℝ ⟩ rewrite lzero[⨰]< Σ′ > with λ (ε : ⟨ ∣ r₁ - r₁ ∣ ⟩ ≡ ⟨ 0 ⟩) → 𝒱ℝ (xRx[≡] ε)
… | P rewrite L1 r₁ = P ↯
fp ⊢`𝔹 b = {!   !}
fp (⊢ a `+ a₁) b = {!   !}
fp (⊢ a `× a₁) b = {!   !}
fp (⊢ a `≤ a₁) b = {!   !}
fp (⊢`var x) b = {!   !}
fp ⊢`tt b = {!   !}
fp (⊢`inl a) b = {!   !}
fp (⊢`inr a) b = {!   !}
fp (⊢`case a a₁ a₂ x) b = {!   !}
fp (⊢`if a a₁ a₂) b = {!   !}
fp (⊢`let a a₁) b = {!   !}
fp (⊢`λ a) b = {!   !}
fp (⊢`app a a₁) b = {!   !}
fp (⊢` a pair a₁) b = {!   !}
fp (⊢`fst a) b = {!   !}
fp (⊢`snd a) b = {!   !}

-- Corrolary 1.1.1 (FP for closed terms).

fpc : ∀ {Γ : Γ[ ᴢ ]} {ø : γ[ ᴢ ]} {e τ} → Γ ⊢ e ⦂ τ , zero → ⟨ ø ⊢ e , ø ⊢ e ⟩∈ℰ⟦ zero ː (zero ⟨⟨ τ ⟩⟩) ⟧
fpc e₁ = {!   !}

∣_-_|ᶠ : 𝔽 → 𝔽 → 𝔽
∣_-_|ᶠ a b with (primFloatNumericalLess (primFloatMinus a b) 0.0)
∣ a - b |ᶠ | ᴏ = primFloatMinus a b
∣ a - b |ᶠ | ɪ = (primFloatMinus a b) × -1.0

∣_-_|ᶠ≤_ : 𝔽 → 𝔽 → Sens → 𝔹
∣ a - b |ᶠ≤ ⟨ x ⟩ = let r = ∣ a - b |ᶠ in primFloatNumericalLess r (natToFloat x)
∣ a - b |ᶠ≤ `∞ = ᴏ

∣_-_∣ᴺ : ℕ → ℕ → ℕ
∣ ᴢ - ᴢ ∣ᴺ = ᴢ
∣ ᴢ - ꜱ n ∣ᴺ = ꜱ n
∣ ꜱ m - ᴢ ∣ᴺ = ꜱ m
∣ ꜱ m - ꜱ n ∣ᴺ = ∣ m - n ∣ᴺ

∣_-_|ᴺ≤_ : ℕ → ℕ → Sens → Set
∣ n₁ - n₂ |ᴺ≤ s = ⟨ ∣ n₁ - n₂ ∣ᴺ ⟩ ≤ s

-- Theorem 1.2 (Sensitivity Type Soundness at Base Types).

sound : ∀ {Γ : Γ[ ᴢ ]} {ø : γ[ ᴢ ]} {e s s′ r₁ r₂ r′₁ r′₂} → Γ ⊢ e ⦂ (ƛ⦂ ℝT ⇒[ [ s ] ] ℝT) , zero → ∣ r₁ - r₂ |ᴺ≤ s′ → ø ⊢ e `app (`ℝ r₁) ⇓ 𝓇 r′₁ → ø ⊢ e `app (`ℝ r₂) ⇓ 𝓇 r′₂ → ∣ r′₁ - r′₂ |ᴺ≤ (s × s′)
sound a b c d = {!   !}
