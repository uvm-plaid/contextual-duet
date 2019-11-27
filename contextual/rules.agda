
{-# OPTIONS --allow-unsolved-metas #-}
module rules where

open import lang public

mutual

  -- TYPING JUDGEMENT FOR PRIVACY TERMS --
  infix 6 _,_⊢ₚ_⦂_,_

  data _,_⊢ₚ_⦂_,_ : ∀ {N} → Γ[ N ] → Σ[ N ] → PTerm N → τ N → Σ[ N ] → Set where

    -- P-APP
    ⊢`papp : ∀ {N} {i : idx (ꜱ N)} {Σ₀ : Σ[ N ]} {Γ : Γ[ N ]} {Σ₁ : Σ[ N ]} {Σ₂ : Σ[ N ]} {e₁ e₂ : Term N} {τ₁ : τ N} {τ₂ : τ (ꜱ N)} {p : Priv} {sb : Sens}
      → Γ , Σ₀ ⊢ e₁ ⦂ (pƛ⦂ τ₁ ∥ sb ⇒[ zero ∔ p ∷ Σ₁ ] τ₂) , zero
      → Γ , Σ₀ ⊢ e₂ ⦂ τ₁ , Σ₂
      -----------------------------------------------------------
      → Γ , Σ₀ ⊢ₚ (e₁ `papp e₂) ⦂ cut Σ₂ τ₂ , (Σ₁ + ([vec]⌉ Σ₂ ⌈⸢ p ⸣))

  -- TYPING JUDGEMENT FOR SENSITIVITY TERMS --
  infix 6 _,_⊢_⦂_,_

  data _,_⊢_⦂_,_ : ∀ {N} → Γ[ N ] → Σ[ N ] → Term N → τ N → Σ[ N ] → Set where

    -- RLIT
    ⊢`ℝ : ∀ {N} {Γ : Γ[ N ]} {Σ₀ : Σ[ N ]} {r : ℕ}
        --------------------------------
      → Γ , Σ₀ ⊢ (`ℝ r) ⦂ ℝT , zero

    -- BLIT
    ⊢`𝔹 : ∀ {N} {Γ : Γ[ N ]} {Σ₀ : Σ[ N ]} {b : 𝔹}
        --------------------------------
      → Γ , Σ₀ ⊢ (`𝔹 b) ⦂ 𝔹T , zero

    -- PLUS
    ⊢_`+_ : ∀ {N} {Γ : Γ[ N ]} {Σ₀ : Σ[ N ]} {Σ₁ Σ₂ : Σ[ N ]} {e₁ e₂ : Term N}
        → Γ , Σ₀ ⊢ e₁ ⦂ ℝT , Σ₁
        → Γ , Σ₀ ⊢ e₂ ⦂ ℝT , Σ₂
        --------------------------------
        → Γ , Σ₀ ⊢ e₁ `+ e₂ ⦂ ℝT , Σ₁ + Σ₂

    -- TIMES
    ⊢_`×_ : ∀ {N} {Γ : Γ[ N ]} {Σ₀ : Σ[ N ]} {Σ₁ Σ₂ : Σ[ N ]} {e₁ e₂ : Term N}
        → Γ , Σ₀ ⊢ e₁ ⦂ ℝT , Σ₁
        → Γ , Σ₀ ⊢ e₂ ⦂ ℝT , Σ₂
        --------------------------------
        → Γ , Σ₀ ⊢ e₁ `× e₂ ⦂ ℝT , [vec]⌉ (Σ₁ + Σ₂) ⌈⸢ `∞ ⸣

    -- LEQ
    ⊢_`≤_ : ∀ {N} {Γ : Γ[ N ]} {Σ₀ : Σ[ N ]} {Σ₁ Σ₂ : Σ[ N ]} {e₁ e₂ : Term N}
        → Γ , Σ₀ ⊢ e₁ ⦂ ℝT , Σ₁
        → Γ , Σ₀ ⊢ e₂ ⦂ ℝT , Σ₂
        --------------------------------
        → Γ , Σ₀ ⊢ e₁ `≤ e₂ ⦂ 𝔹T , [vec]⌉ (Σ₁ + Σ₂) ⌈⸢ `∞ ⸣

    -- VAR
    ⊢`var_ : ∀ {N} {Γ : Γ[ N ]} {Σ₀ : Σ[ N ]} {Σ : Σ[ N ]} {i : idx N} {τ : τ N}
      → Γ #[ i ] ≡ τ
      --------------------------------------------------
      → Γ , Σ₀ ⊢  ` i ⦂ τ , Σ + zero #[ i ↦ ⟨ 1 ⟩ ]

    -- UNIT
    ⊢`tt : ∀ {N} {Γ : Γ[ N ]} {Σ₀ : Σ[ N ]} {i : idx N} -- {τ : τ N}
      --------------------------------------------------
      → Γ , Σ₀ ⊢  tt ⦂ unit , zero

    -- INL
    ⊢`inl : ∀ {N} {Γ : Γ[ N ]} {Σ₀ : Σ[ N ]} {Σ₁ : Σ[ N ]} {Σ₂ : Σ[ N ]} {e : Term N} {τ₁ τ₂ : τ N}
      → Γ , Σ₀ ⊢ e ⦂ τ₁ , Σ₁
      --------------------------------------------------
      → Γ , Σ₀ ⊢ (inl τ₂ ∥ e) ⦂ (τ₁ ∥ zero ∔ Σ₁ ⊕ zero ∔ zero ∥ τ₂) , zero

    -- INR
    ⊢`inr : ∀ {N} {Γ : Γ[ N ]} {Σ₀ : Σ[ N ]} {Σ₂ : Σ[ N ]} {e : Term N} {τ₁ τ₂ : τ N}
      → Γ , Σ₀ ⊢ e ⦂ τ₂ , Σ₂
      --------------------------------------------------
      → Γ , Σ₀ ⊢ (inr τ₁ ∥ e) ⦂ τ₁ ∥ zero ∔ zero ⊕ zero ∔ Σ₂ ∥ τ₂  , zero

    -- CASE
    ⊢`case : ∀ {N} {Γ : Γ[ N ]} {Σ₀ : Σ[ N ]} {Σ₁ Σ₁₁ Σ₁₂ Σ₂ Σ₃ : Σ[ N ]} {i : idx (ꜱ N)} {e₁ : Term N} {e₂ e₃ : Term (ꜱ N)} {τ₁₁ τ₁₂ τ₂ τ₃ τ₄ : τ N} {s₂ s₃ : Sens}
      → Γ , Σ₀ ⊢ e₁ ⦂ τ₁₁ ∥ zero ∔ Σ₁₁ ⊕ zero ∔ Σ₁₂ ∥ τ₁₂ , Σ₁
      → (mapⱽ ⇧ᵗ (τ₁₁ ∷ Γ)) , ⇧ˢ Σ₀ ⊢ e₂ ⦂ (⇧ᵗ τ₂) , s₂ ∷ Σ₂
      → (mapⱽ ⇧ᵗ (τ₁₂ ∷ Γ)) , ⇧ˢ Σ₀ ⊢ e₃ ⦂ (⇧ᵗ τ₃) , s₃ ∷ Σ₃
      → (cut (Σ₁ + Σ₁₁) (⇧ᵗ τ₂)) τ[⊔] (cut (Σ₁ + Σ₁₂) (⇧ᵗ τ₃)) ≡ ⟨ τ₄ ⟩
    ------------------------------------------------------------------------------------
      → Γ , Σ₀ ⊢ case e₁ of e₂ ∥ e₃ ⦂ τ₄ , [vec]⌉ Σ₁ ⌈⸢ `∞ ⸣ + ((s₂ ⨵ Σ₁₁) + Σ₂) ⊔ ((s₃ ⨵ Σ₁₂) + Σ₃)

    -- IF
    ⊢`if : ∀ {N} {Γ : Γ[ N ]} {Σ₀ : Σ[ N ]} {Σ₁ Σ₂ Σ₃ : Σ[ N ]} {e₁ e₂ e₃ : Term N}  {τ : τ N}
      → Γ , Σ₀ ⊢ e₁ ⦂ 𝔹T , Σ₁
      → Γ , Σ₀ ⊢ e₂ ⦂ τ , Σ₂
      → Γ , Σ₀ ⊢ e₃ ⦂ τ , Σ₃
    ------------------------------------------------------------------------------------
      → Γ , Σ₀ ⊢ if e₁ ∥ e₂ ∥ e₃ ⦂ τ , Σ₁ + (Σ₂ ⊔ Σ₃)

    -- LET
    ⊢`let : ∀ {N} {Γ : Γ[ N ]} {Σ₀ : Σ[ N ]} {Σ₁ Σ₂ : Σ[ N ]} {e₁ : Term N} {e₂ : Term (ꜱ N)} {τ₁ : τ N} {τ₂ : τ (ꜱ N)} {s : Sens}
      →  Γ , Σ₀ ⊢ e₁ ⦂ τ₁ , Σ₁
      →  (mapⱽ ⇧ᵗ (τ₁ ∷ Γ)) , ⇧ˢ Σ₀ ⊢ e₂ ⦂ τ₂ , s ∷ Σ₂
      -----------------------------------------------
      → Γ , Σ₀ ⊢ (`let e₁ ∥ e₂) ⦂  cut Σ₁ τ₂ , (s ⨵ Σ₁) + Σ₂

    -- S-LAM
    ⊢`sλ : ∀ {N} {Γ : Γ[ N ]} {Σ₀ : Σ[ N ]} {s : Sens} {Σ₁ : Σ[ N ]} {i : idx N} {e : Term (ꜱ N)} {τ₁ : τ N} {τ₂ : τ (ꜱ N)} {sb : Sens}
      →  (mapⱽ ⇧ᵗ (τ₁ ∷ Γ)) , sb ∷ Σ₀ ⊢ e ⦂ τ₂ , s ∷ Σ₁
      -----------------------------------------------
      → Γ , Σ₀ ⊢ (sƛ⦂ τ₁ ∥ sb ⇒ e) ⦂ (sƛ⦂ τ₁ ∥ sb ⇒[ zero ∔ s ∷ Σ₁ ] τ₂) , zero

    -- P-LAM
    ⊢`pλ : ∀ {N} {Γ : Γ[ N ]} {Σ₀ : Σ[ N ]} {p : Priv} {Σ₁ : Σₚ[ N ]} {i : idx N} {e : PTerm (ꜱ N)} {τ₁ : τ N} {τ₂ : τ (ꜱ N)} {sb : Sens}
      →  (mapⱽ ⇧ᵗ (τ₁ ∷ Γ)) , sb ∷ Σ₀ ⊢ₚ e ⦂ τ₂ , p ∷ Σ₁
      -----------------------------------------------
      → Γ , Σ₀ ⊢ (pƛ⦂ τ₁ ∥ sb ⇒ e) ⦂ (pƛ⦂ τ₁ ∥ sb ⇒[ zero ∔ p ∷ Σ₁ ] τ₂) , zero

    -- S-APP
    ⊢`app : ∀ {N} {i : idx (ꜱ N)} {Σ₀ : Σ[ N ]} {Γ : Γ[ N ]} {Σ₁ Σ₂ : Σ[ N ]} {e₁ e₂ : Term N} {τ₁ : τ N} {τ₂ : τ (ꜱ N)} {s sb : Sens}
      → Γ , Σ₀ ⊢ e₁ ⦂ (sƛ⦂ τ₁ ∥ sb ⇒[ zero ∔ s ∷ Σ₁ ] τ₂) , zero
      → Γ , Σ₀ ⊢ e₂ ⦂ τ₁ , Σ₂
      -----------------------------------------------------------
      → Γ , Σ₀ ⊢ (e₁ `app e₂) ⦂ cut Σ₂ τ₂ , (Σ₁ + (s ⨵ Σ₂))

    -- PAIR
    ⊢`_pair_ : ∀ {N} {Γ : Γ[ N ]} {Σ₀ : Σ[ N ]} {Σ₁ Σ₂ : Σ[ N ]} {e₁ e₂ : Term N} {τ₁ τ₂ : τ N}
      → Γ , Σ₀ ⊢ e₁ ⦂ τ₁ , Σ₁
      → Γ , Σ₀ ⊢ e₂ ⦂ τ₂ , Σ₂
      -----------------------------------------------------------
      → Γ , Σ₀ ⊢ e₁ `pair e₂ ⦂ τ₁ ∥ zero ∔ Σ₁ ⊗ zero ∔ Σ₂ ∥ τ₂ , zero

    -- PROJ1
    ⊢`fst : ∀ {N} {Γ : Γ[ N ]} {Σ₀ : Σ[ N ]} {Σ Σ₁ Σ₂ : Σ[ N ]} {e : Term N} {τ₁ τ₂ : τ N}
      → Γ , Σ₀ ⊢ e ⦂ τ₁ ∥ zero ∔ Σ₁ ⊗ zero ∔ Σ₂ ∥ τ₂ , Σ
    --------------------------------------
      → Γ , Σ₀ ⊢ fst e ⦂ τ₁ , Σ + Σ₁

    -- PROJ2
    ⊢`snd : ∀ {N} {Γ : Γ[ N ]} {Σ₀ : Σ[ N ]} {Σ Σ₁ Σ₂ : Σ[ N ]} {e : Term N} {τ₁ τ₂ : τ N}
      → Γ , Σ₀ ⊢ e ⦂ τ₁ ∥ zero ∔ Σ₁ ⊗ zero ∔ Σ₂ ∥ τ₂ , Σ
    -----------------------------------------
      → Γ , Σ₀ ⊢ snd e ⦂ τ₂ , Σ + Σ₂

two : Term 0
two = `ℝ 2

⊢two : ∀ {Γ : Γ[ 0 ]} → Γ , zero ⊢ two ⦂ ℝT , []
⊢two = ⊢`ℝ

_ : ⟬ ℕ ⟭[ 2 ]
_ = 1 ∷ 0 ∷ []

_ : ⟬ ℕ ⟭[ 2 ]
_ = 1 ∷ 0 ∷ [] + 1 ∷ 0 ∷ []

_ : (1 ∷ 0 ∷ [] AT ⟬ ℕ ⟭[ 2 ]) + (1 ∷ 0 ∷ [] AT ⟬ ℕ ⟭[ 2 ]) ≡ (2 ∷ 0 ∷ [])
_ = ↯

postulate
  ∣_-_∣ : ℕ → ℕ → ℕ

-- ℾ[ N ] =  Γ[ N ]

-- TYPING JUDGEMENT FOR VALUE ENVIRONMENT --

mutual
  infix 6 _⊢_

  data _⊢_ : ∀ {N} → ℾ[ N ] → γ[ N ] → Set where

    ⊢z : [] ⊢ []

    ⊢s : ∀ {N} {ℾ : ℾ[ N ]} {γ : γ[ N ]} {𝓋 : 𝓋} {τ : τ 0}
      → ⊢ 𝓋 ⦂ τ
      → ℾ ⊢ γ
      --------------------------------
      → (τ ∷ ℾ) ⊢ 𝓋 ∷ γ

  -- TYPING JUDGEMENT FOR VALUES --
  infix 6 ⊢_⦂_

  data ⊢_⦂_ : 𝓋 → τ ᴢ → Set where

    ⊢𝓇 : ∀ {r : ℕ}
        --------------------------------
      → ⊢ (𝓇 r) ⦂ ℝT

    ⊢𝒷 : ∀ {b : 𝔹}
        --------------------------------
      → ⊢ (𝒷 b) ⦂ 𝔹T

    ⊢tt :
        --------------------------------
        ⊢ tt ⦂ unit

    ⊢inl : ∀ {v τ₁ τ₂ s₁ s₂}
      → ⊢ v ⦂ τ₁
        --------------------------------
      → ⊢ (inl v) ⦂ τ₁ ∥ s₁ ∔ zero ⊕ s₂ ∔ zero ∥ τ₂

    ⊢inr : ∀ {v τ₁ τ₂ s₁ s₂}
      → ⊢ v ⦂ τ₂
        --------------------------------
      → ⊢ (inr v) ⦂ τ₁ ∥ s₁ ∔ zero ⊕ s₂ ∔ zero ∥ τ₂

    ⊢pair : ∀ {v₁ v₂ τ₁ τ₂ s₁ s₂}
      → ⊢ v₁ ⦂ τ₁
      → ⊢ v₂ ⦂ τ₂
        --------------------------------
      → ⊢ (v₁ pair v₂) ⦂ τ₁ ∥ s₁ ∔ zero ⊗ s₂ ∔ zero ∥ τ₂

    ⊢sλ : ∀ {N} {Γ : Γ[ N ]} {Σ₀ : Σ[ N ]} {e : Term (ꜱ N)} {γ : γ[ N ]} {τ₁ : τ N} {τ₂ : τ (ꜱ N)} {τ₁′ τ₂′} {s s′ sb} {Σ : Σ[ N ]}
      → mapⱽ (instantiateΣ/τ zero) Γ ⊢ γ
      → Γ , Σ₀ ⊢ sƛ⦂ τ₁ ∥ sb ⇒ e ⦂ (sƛ⦂ τ₁ ∥ sb ⇒[ zero ∔ s ∷ Σ ] τ₂) , zero
      → τ₁′ ≡ instantiateΣ/τ zero τ₁
      → τ₂′ ≡ instantiateΣ/τ zero τ₂
      → s′ ≡ zero
        --------------------------------
      → ⊢ (sƛ⦂ e ∥ γ ) ⦂ (sƛ⦂ τ₁′ ∥ sb ⇒[ s′ ∔ [ s ] ] τ₂′)

    ⊢pλ : ∀ {N} {Γ : Γ[ N ]} {Σ₀ : Σ[ N ]} {e : PTerm (ꜱ N)} {γ : γ[ N ]} {τ₁ : τ N} {τ₂ : τ (ꜱ N)} {τ₁′ τ₂′} {p p′ sb} {Σ : Σₚ[ N ]}
      → mapⱽ (instantiateΣ/τ zero) Γ ⊢ γ
      → Γ , Σ₀ ⊢ pƛ⦂ τ₁ ∥ sb ⇒ e ⦂ (pƛ⦂ τ₁ ∥ sb ⇒[ zero ∔ p ∷ Σ ] τ₂) , zero
      → τ₁′ ≡ instantiateΣ/τ zero τ₁
      → τ₂′ ≡ instantiateΣ/τ zero τ₂
      → p′ ≡ zero
        --------------------------------
      → ⊢ (pƛ⦂ e ∥ γ ) ⦂ (pƛ⦂ τ₁′ ∥ sb ⇒[ p′ ∔ [ p ] ] τ₂′)

-- postulate
--   -- sensitivity evaluation
--   ⟦_ː_⟧ˢ[_ː_] : ∀ {N} {Γ : Γ[ N ]} {ℾ Σ₀ τ Σ Σ′} → (e : Term N) → (⊢e : Γ , Σ₀ ⊢ e ⦂ τ , Σ) → (γ : γ[ N ]) → ℾ ⊢ γ → ∃ v ⦂ 𝓋 ST ⊢ v ⦂  Σ′ ⟨⟨ τ ⟩⟩
--   corr : ∀ {N} {Γ : Γ[ N ]} {ℾ Σ₀ τ Σ Σ′ v ⊢v} → (e : Term N) → (⊢e : (Γ , Σ₀ ⊢ e ⦂ τ , Σ )) → (γ : γ[ N ]) → (⊢γ : ℾ ⊢ γ) → γ ⊢ e ⇓ v → ⟦ e ː ⊢e ⟧ˢ[ γ ː ⊢γ ] ≡ ⟨∃ v , ⊢v ⟩
--
-- -- privacy evaluation
--
--
-- ⟦_ː_⟧ᵖ[_ː_] : ∀ {N} {Γ : Γ[ N ]} {ℾ Σ₀ e τ Σ Σ′} → (e : PTerm N) → Γ , Σ₀ ⊢ₚ e ⦂ τ , Σ → (γ : γ[ N ]) → ℾ ⊢ γ → 𝒟 (∃ v ⦂ 𝓋 ST ⊢ v ⦂ Σ′ ⟨⟨ τ ⟩⟩)
-- ⟦_ː_⟧ᵖ[_ː_] {N = N} (_`papp_ e₁ e₂) (⊢`papp δ₁ δ₂) γ  ⊢γ
--   with ⟦ e₁ ː δ₁ ⟧ˢ[ γ ː ⊢γ ] | ⟦ e₂ ː δ₂ ⟧ˢ[ γ ː ⊢γ ]
-- ... | ⟨∃  (pƛ⦂ e′ ∥ γ′) , (⊢pλ {N = N₁} ⊢γ′ ⊢e′ i₁ i₂ pz) ⟩ | ⟨∃ v , ⊢v ⟩ = ⟦ {! e′ !} ː {!⊢e′   !} ⟧ᵖ[ {!   !} ː {!   !} ]

mutual

  -- PROBABILISTIC SEMANTICS

  infix 6 _⊢_⇓ₚ_

  data _⊢_⇓ₚ_ : ∀ {N τ} → γ[ N ] → PTerm N → 𝒟 (∃ v ⦂ 𝓋 ST ⊢ v ⦂ τ) → Set where

    -- APP
    ⊢`papp : ∀ {N} {γ : γ[ N ]} {e′ : PTerm (ꜱ N)} {e₁ e₂ : Term N} {𝓋₁ : 𝓋} {τ} {𝓋₂ : 𝒟 (∃ v ⦂ 𝓋 ST ⊢ v ⦂ τ )}
      → γ ⊢ e₁ ⇓ (pƛ⦂ e′ ∥ γ )
      → γ ⊢ e₂ ⇓ 𝓋₁
      → 𝓋₁ ∷ γ ⊢ e′ ⇓ₚ 𝓋₂
      -----------------------------------------------------------
      → γ ⊢ (e₁ `papp e₂) ⇓ₚ 𝓋₂

  -- GROUND TRUTH DYNAMIC SEMANTICS

  infix 6 _⊢_⇓_

  data _⊢_⇓_ : ∀ {N} → γ[ N ] → Term N → 𝓋 → Set where

    -- RLIT
    ⊢`ℝ : ∀ {N} {γ : γ[ N ]} {r : ℕ}
        --------------------------------
      → γ ⊢ (`ℝ r) ⇓ 𝓇 r

    -- BLIT
    ⊢`𝔹 : ∀ {N} {γ : γ[ N ]} {b : 𝔹}
        --------------------------------
      → γ ⊢ (`𝔹 b) ⇓ 𝒷 b

    -- PLUS
    ⊢_`+_ : ∀ {N} {γ : γ[ N ]} {e₁ e₂ : Term N} {r₁ r₂ : ℕ}
        → γ ⊢ e₁ ⇓ 𝓇 r₁
        → γ ⊢ e₂ ⇓ 𝓇 r₂
        --------------------------------
        → γ ⊢ e₁ `+ e₂ ⇓ 𝓇 (r₁ + r₂)

    -- TIMES
    ⊢_`×_ : ∀ {N} {γ : γ[ N ]}  {e₁ e₂ : Term N} {r₁ r₂ : ℕ}
        → γ ⊢ e₁ ⇓ 𝓇 r₁
        → γ ⊢ e₂ ⇓ 𝓇 r₂
        --------------------------------
        → γ ⊢ e₁ `× e₂ ⇓ 𝓇 (r₁ × r₂)

    -- LEQ
    ⊢_`≤_ : ∀ {N} {γ : γ[ N ]}  {e₁ e₂ : Term N} {r₁ r₂ : ℕ}
        → γ ⊢ e₁ ⇓ 𝓇 r₁
        → γ ⊢ e₂ ⇓ 𝓇 r₂
        --------------------------------
        → γ ⊢ e₁ `≤ e₂ ⇓ 𝒷 (r₁ ≤? r₂)

    -- VAR
    ⊢`var_ : ∀ {N} {γ : γ[ N ]} {i : idx N} {𝓋 : 𝓋}
      → γ #[ i ] ≡ 𝓋
      --------------------------------------------------
      → γ ⊢  ` i ⇓ 𝓋

    -- UNIT
    ⊢`tt : ∀ {N} {γ : γ[ N ]}
      ----------------------------
      → γ ⊢  tt ⇓ tt

    -- INL
    ⊢`inl : ∀ {N} {γ : γ[ N ]} {e : Term N} {𝓋 : 𝓋} {τ₂ : τ N}
      → γ ⊢ e ⇓ 𝓋
      --------------------------------------------------
      → γ ⊢ (inl τ₂ ∥ e) ⇓ inl 𝓋

    -- INR
    ⊢`inr : ∀ {N} {γ : γ[ N ]} {e : Term N} {𝓋 : 𝓋} {τ₁ : τ N}
      → γ ⊢ e ⇓ 𝓋
      --------------------------------------------------
      → γ ⊢ (inr τ₁ ∥ e) ⇓ inr 𝓋

    -- CASE-LEFT
    ⊢`case/l : ∀ {N} {γ : γ[ N ]} {e₁ : Term N} {e₂ e₃ : Term (ꜱ N)} {𝓋₁ 𝓋₂ : 𝓋}
      → γ ⊢ e₁ ⇓ inl 𝓋₁
      → (𝓋₁ ∷ γ) ⊢ e₂ ⇓ 𝓋₂
    ------------------------------------------------------------------------------------
      → γ ⊢ case e₁ of e₂ ∥ e₃ ⇓ 𝓋₂

    -- CASE-RIGHT
    ⊢`case/r : ∀ {N} {γ : γ[ N ]} {i : idx (ꜱ N)} {e₁ : Term N} {e₂ e₃ : Term (ꜱ N)} {𝓋₁ 𝓋₂ : 𝓋}
      → γ ⊢ e₁ ⇓ inr 𝓋₁
      → (𝓋₁ ∷ γ) ⊢ e₃ ⇓ 𝓋₂
    ------------------------------------------------------------------------------------
      → γ ⊢ case e₁ of e₂ ∥ e₃ ⇓ 𝓋₂

    -- IF-TRUE
    ⊢`if-true : ∀ {N} {γ : γ[ N ]} {e₁ e₂ e₃ : Term N} {𝓋 : 𝓋}
      → γ ⊢ e₁ ⇓ 𝒷 ɪ
      → γ ⊢ e₂ ⇓ 𝓋
    ------------------------------------------------------------------------------------
      → γ ⊢ if e₁ ∥ e₂ ∥ e₃ ⇓ 𝓋

    -- IF-FALSE
    ⊢`if-false : ∀ {N} {γ : γ[ N ]} {e₁ e₂ e₃ : Term N} {𝓋 : 𝓋}
      → γ ⊢ e₁ ⇓ 𝒷 ᴏ
      → γ ⊢ e₃ ⇓ 𝓋
    ------------------------------------------------------------------------------------
      → γ ⊢ if e₁ ∥ e₂ ∥ e₃ ⇓ 𝓋

    -- LET
    ⊢`let : ∀ {N} {γ : γ[ N ]} {e₁ : Term N} {e₂ : Term (ꜱ N)} {𝓋₁ 𝓋₂ : 𝓋}
      →  γ ⊢ e₁ ⇓ 𝓋₁
      →  (𝓋₁ ∷ γ) ⊢ e₂ ⇓ 𝓋₂
      -----------------------------------------------
      → γ ⊢ (`let e₁ ∥ e₂) ⇓ 𝓋₂

    -- LAM
    ⊢`λ : ∀ {N} {γ : γ[ N ]} {e : Term (ꜱ N)} {τ : τ N} {s : Sens}
      -----------------------------------------------
      → γ ⊢ (sƛ⦂ τ ∥ s ⇒ e) ⇓ (sƛ⦂ e ∥ γ )


    -- P-LAM
    ⊢`pλ : ∀ {N} {γ : γ[ N ]} {e : PTerm (ꜱ N)} {τ : τ N} {s : Sens}
      -----------------------------------------------
      → γ ⊢ (pƛ⦂ τ ∥ s ⇒ e) ⇓ (pƛ⦂ e ∥ γ )

    -- APP
    ⊢`app : ∀ {N} {γ : γ[ N ]} {e′ : Term (ꜱ N)} {e₁ e₂ : Term N} {𝓋₁ 𝓋₂ : 𝓋}
      → γ ⊢ e₁ ⇓ (sƛ⦂ e′ ∥ γ )
      → γ ⊢ e₂ ⇓ 𝓋₁
      → 𝓋₁ ∷ γ ⊢ e′ ⇓ 𝓋₂
      -----------------------------------------------------------
      → γ ⊢ (e₁ `app e₂) ⇓ 𝓋₂

    -- PAIR
    ⊢`_pair_ : ∀ {N} {γ : γ[ N ]} {e₁ e₂ : Term N} {𝓋₁ 𝓋₂ : 𝓋}
      → γ ⊢ e₁ ⇓ 𝓋₁
      → γ ⊢ e₂ ⇓ 𝓋₂
      -----------------------------------------------------------
      → γ ⊢ e₁ `pair e₂ ⇓ 𝓋₁ pair 𝓋₂

    -- PROJ1
    ⊢`fst : ∀ {N} {γ : γ[ N ]} {e : Term N} {𝓋₁ 𝓋₂ : 𝓋}
      → γ ⊢ e ⇓ 𝓋₁ pair 𝓋₂
    --------------------------------------
      → γ ⊢ fst e ⇓ 𝓋₁

    -- PROJ2
    ⊢`snd : ∀ {N} {γ : γ[ N ]} {e : Term N} {𝓋₁ 𝓋₂ : 𝓋}
      → γ ⊢ e ⇓ 𝓋₁ pair 𝓋₂
    -----------------------------------------
      → γ ⊢ snd e ⇓ 𝓋₂
