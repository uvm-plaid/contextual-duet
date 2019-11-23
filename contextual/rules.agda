
{-# OPTIONS --allow-unsolved-metas #-}
module rules where

open import lang public

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
    → γ ⊢ (sƛ⦂ τ ∥ s ⇒ e) ⇓ (ƛ⦂ e ∥ γ )

  -- APP
  ⊢`app : ∀ {N} {γ : γ[ N ]} {e′ : Term (ꜱ N)} {e₁ e₂ : Term N} {𝓋₁ 𝓋₂ : 𝓋}
    → γ ⊢ e₁ ⇓ (ƛ⦂ e′ ∥ γ )
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


-- TYPING JUDGEMENT FOR TERMS --
infix 6 _⊢_⦂_,_

data _⊢_⦂_,_ : ∀ {N} → Γ[ N ] → Term N → τ N → Σ[ N ] → Set where

  -- RLIT
  ⊢`ℝ : ∀ {N} {Γ : Γ[ N ]} {r : ℕ}
      --------------------------------
    → Γ ⊢ (`ℝ r) ⦂ ℝT , zero

  -- BLIT
  ⊢`𝔹 : ∀ {N} {Γ : Γ[ N ]} {b : 𝔹}
      --------------------------------
    → Γ ⊢ (`𝔹 b) ⦂ 𝔹T , zero

  -- PLUS
  ⊢_`+_ : ∀ {N} {Γ : Γ[ N ]} {Σ₁ Σ₂ : Σ[ N ]} {e₁ e₂ : Term N}
      → Γ ⊢ e₁ ⦂ ℝT , Σ₁
      → Γ ⊢ e₂ ⦂ ℝT , Σ₂
      --------------------------------
      → Γ ⊢ e₁ `+ e₂ ⦂ ℝT , Σ₁ + Σ₂

  -- TIMES
  ⊢_`×_ : ∀ {N} {Γ : Γ[ N ]} {Σ₁ Σ₂ : Σ[ N ]} {e₁ e₂ : Term N}
      → Γ ⊢ e₁ ⦂ ℝT , Σ₁
      → Γ ⊢ e₂ ⦂ ℝT , Σ₂
      --------------------------------
      → Γ ⊢ e₁ `× e₂ ⦂ ℝT , [vec]⌉ (Σ₁ + Σ₂) ⌈⸢ `∞ ⸣

  -- LEQ
  ⊢_`≤_ : ∀ {N} {Γ : Γ[ N ]} {Σ₁ Σ₂ : Σ[ N ]} {e₁ e₂ : Term N}
      → Γ ⊢ e₁ ⦂ ℝT , Σ₁
      → Γ ⊢ e₂ ⦂ ℝT , Σ₂
      --------------------------------
      → Γ ⊢ e₁ `≤ e₂ ⦂ 𝔹T , [vec]⌉ (Σ₁ + Σ₂) ⌈⸢ `∞ ⸣

  -- VAR
  ⊢`var_ : ∀ {N} {Γ : Γ[ N ]} {Σ : Σ[ N ]} {i : idx N} {τ : τ N}
    → Γ #[ i ] ≡ τ
    --------------------------------------------------
    → Γ ⊢  ` i ⦂ τ , Σ + zero #[ i ↦ ⟨ 1 ⟩ ]

  -- UNIT
  ⊢`tt : ∀ {N} {Γ : Γ[ N ]} {i : idx N} -- {τ : τ N}
    --------------------------------------------------
    → Γ ⊢  tt ⦂ unit , zero

  -- INL
  ⊢`inl : ∀ {N} {Γ : Γ[ N ]} {Σ₁ : Σ[ N ]} {Σ₂ : Σ[ N ]} {e : Term N} {τ₁ τ₂ : τ N}
    → Γ ⊢ e ⦂ τ₁ , Σ₁
    --------------------------------------------------
    → Γ ⊢ (inl τ₂ ∥ e) ⦂ (τ₁ ∥ zero ∔ Σ₁ ⊕ zero ∔ zero ∥ τ₂) , zero

  -- INR
  ⊢`inr : ∀ {N} {Γ : Γ[ N ]} {Σ₂ : Σ[ N ]} {e : Term N} {τ₁ τ₂ : τ N}
    → Γ ⊢ e ⦂ τ₂ , Σ₂
    --------------------------------------------------
    → Γ ⊢ (inr τ₁ ∥ e) ⦂ τ₁ ∥ zero ∔ zero ⊕ zero ∔ Σ₂ ∥ τ₂  , zero

  -- CASE
  ⊢`case : ∀ {N} {Γ : Γ[ N ]} {Σ₁ Σ₁₁ Σ₁₂ Σ₂ Σ₃ : Σ[ N ]} {i : idx (ꜱ N)} {e₁ : Term N} {e₂ e₃ : Term (ꜱ N)} {τ₁₁ τ₁₂ τ₂ τ₃ τ₄ : τ N} {s₂ s₃ : Sens}
    → Γ ⊢ e₁ ⦂ τ₁₁ ∥ zero ∔ Σ₁₁ ⊕ zero ∔ Σ₁₂ ∥ τ₁₂ , Σ₁
    → (mapⱽ ⇧ᵗ (τ₁₁ ∷ Γ)) ⊢ e₂ ⦂ (⇧ᵗ τ₂) , s₂ ∷ Σ₂
    → (mapⱽ ⇧ᵗ (τ₁₂ ∷ Γ)) ⊢ e₃ ⦂ (⇧ᵗ τ₃) , s₃ ∷ Σ₃
    → (cut (Σ₁ + Σ₁₁) (⇧ᵗ τ₂)) τ[⊔] (cut (Σ₁ + Σ₁₂) (⇧ᵗ τ₃)) ≡ ⟨ τ₄ ⟩
  ------------------------------------------------------------------------------------
    → Γ ⊢ case e₁ of e₂ ∥ e₃ ⦂ τ₄ , [vec]⌉ Σ₁ ⌈⸢ `∞ ⸣ + ((s₂ ⨵ Σ₁₁) + Σ₂) ⊔ ((s₃ ⨵ Σ₁₂) + Σ₃)

  -- IF
  ⊢`if : ∀ {N} {Γ : Γ[ N ]} {Σ₁ Σ₂ Σ₃ : Σ[ N ]} {e₁ e₂ e₃ : Term N}  {τ : τ N}
    → Γ ⊢ e₁ ⦂ 𝔹T , Σ₁
    → Γ ⊢ e₂ ⦂ τ , Σ₂
    → Γ ⊢ e₃ ⦂ τ , Σ₃
  ------------------------------------------------------------------------------------
    → Γ ⊢ if e₁ ∥ e₂ ∥ e₃ ⦂ τ , Σ₁ + (Σ₂ ⊔ Σ₃)

  -- LET
  ⊢`let : ∀ {N} {Γ : Γ[ N ]} {Σ₁ Σ₂ : Σ[ N ]} {e₁ : Term N} {e₂ : Term (ꜱ N)} {τ₁ : τ N} {τ₂ : τ (ꜱ N)} {s : Sens}
    →  Γ ⊢ e₁ ⦂ τ₁ , Σ₁
    →  (mapⱽ ⇧ᵗ (τ₁ ∷ Γ)) ⊢ e₂ ⦂ τ₂ , s ∷ Σ₂
    -----------------------------------------------
    → Γ ⊢ (`let e₁ ∥ e₂) ⦂  cut Σ₁ τ₂ , (s ⨵ Σ₁) + Σ₂

  -- LAM
  ⊢`λ : ∀ {N} {Γ : Γ[ N ]} {s} {Σ₁ : Σ[ N ]} {i : idx N} {e : Term (ꜱ N)} {τ₁ : τ N} {τ₂ : τ (ꜱ N)} {s : Sens}
    →  (mapⱽ ⇧ᵗ (τ₁ ∷ Γ)) ⊢ e ⦂ τ₂ , s ∷ Σ₁
    -----------------------------------------------
    → Γ ⊢ (sƛ⦂ τ₁ ∥ s ⇒ e) ⦂ (sƛ⦂ τ₁ ∥ s ⇒[ zero ∔ s ∷ Σ₁ ] τ₂) , zero

  -- APP
  ⊢`app : ∀ {N} {i : idx (ꜱ N)} {Γ : Γ[ N ]} {Σ₁ Σ₂ : Σ[ N ]} {e₁ e₂ : Term N} {τ₁ : τ N} {τ₂ : τ (ꜱ N)} {s sb : Sens}
    → Γ ⊢ e₁ ⦂ (sƛ⦂ τ₁ ∥ sb ⇒[ zero ∔ s ∷ Σ₁ ] τ₂) , zero
    → Γ ⊢ e₂ ⦂ τ₁ , Σ₂
    -----------------------------------------------------------
    → Γ ⊢ (e₁ `app e₂) ⦂ cut Σ₂ τ₂ , (Σ₁ + (s ⨵ Σ₂))

  -- PAIR
  ⊢`_pair_ : ∀ {N} {Γ : Γ[ N ]} {Σ₁ Σ₂ : Σ[ N ]} {e₁ e₂ : Term N} {τ₁ τ₂ : τ N}
    → Γ ⊢ e₁ ⦂ τ₁ , Σ₁
    → Γ ⊢ e₂ ⦂ τ₂ , Σ₂
    -----------------------------------------------------------
    → Γ ⊢ e₁ `pair e₂ ⦂ τ₁ ∥ zero ∔ Σ₁ ⊗ zero ∔ Σ₂ ∥ τ₂ , zero

  -- PROJ1
  ⊢`fst : ∀ {N} {Γ : Γ[ N ]} {Σ Σ₁ Σ₂ : Σ[ N ]} {e : Term N} {τ₁ τ₂ : τ N}
    → Γ ⊢ e ⦂ τ₁ ∥ zero ∔ Σ₁ ⊗ zero ∔ Σ₂ ∥ τ₂ , Σ
  --------------------------------------
    → Γ ⊢ fst e ⦂ τ₁ , Σ + Σ₁

  -- PROJ2
  ⊢`snd : ∀ {N} {Γ : Γ[ N ]} {Σ Σ₁ Σ₂ : Σ[ N ]} {e : Term N} {τ₁ τ₂ : τ N}
    → Γ ⊢ e ⦂ τ₁ ∥ zero ∔ Σ₁ ⊗ zero ∔ Σ₂ ∥ τ₂ , Σ
  -----------------------------------------
    → Γ ⊢ snd e ⦂ τ₂ , Σ + Σ₂

two : Term 0
two = `ℝ 2

⊢two : ∀ {Γ : Γ[ 0 ]} → Γ ⊢ two ⦂ ℝT , []
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

    ⊢λ : ∀ {N} {Γ : Γ[ N ]} {e : Term (ꜱ N)} {γ : γ[ N ]} {τ₁ : τ N} {τ₂ : τ (ꜱ N)} {τ₁′ τ₂′} {s s′ sb} {Σ : Σ[ N ]}
      → mapⱽ (instantiateΣ/τ zero) Γ ⊢ γ
      → Γ ⊢ sƛ⦂ τ₁ ∥ sb ⇒ e ⦂ (sƛ⦂ τ₁ ∥ sb ⇒[ zero ∔ s ∷ Σ ] τ₂) , zero
      -- → mapⱽ ⇧ᵗ (τ₁ ∷ ℾ) ⊢ e ⦂ τ₂ , Σ₂
      → τ₁′ ≡ instantiateΣ/τ zero τ₁
      → τ₂′ ≡ instantiateΣ/τ zero τ₂
      → s′ ≡ zero
        --------------------------------
      → ⊢ (ƛ⦂ e ∥ γ ) ⦂ sƛ⦂ τ₁′ ∥ sb ⇒[ s′ ∔ [ s ] ] τ₂′
