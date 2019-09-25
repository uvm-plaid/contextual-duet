-- CITATION: Jacob Wunder's proof of metric space conservation for Duet 1.0

-- QUESTION: how to adjust N soundly
-- QUESTION: Σ substitution

module contextual where

open import UVMVS public

_ : ℕ
_ = 2

_ : 𝔽
_ = 2.0

_ : 𝔹
_ = ɪ

_ : 𝔹
_ = ᴏ

-- QUANTITIES --
data qty {ℓ} (A : Set ℓ) : Set ℓ where
  ⟨_⟩ : A → qty A
  `∞ : qty A

module _ {ℓ} {A : Set ℓ} {{_ : has[+] A}} {{_ : cor[+] A}} {{_ : has[≡?] A}} where
  zero[qty] : qty A
  zero[qty] = ⟨ zero ⟩

  _+[qty]_ : qty A → qty A → qty A
  _ +[qty] `∞ = `∞
  `∞ +[qty] _ = `∞
  ⟨ x ⟩ +[qty] ⟨ y ⟩ = ⟨ x + y ⟩

  {-# DISPLAY _+[qty]_ = _+_ #-}

  instance
    has[+][qty] : has[+] (qty A)
    has[+][qty] = record { zero = zero[qty] ; _+_ = _+[qty]_ }


  abstract
    lunit[+][qty]<_> : ∀ (x : qty A) → zero + x ≡ x
    lunit[+][qty]< ⟨ x ⟩ > rewrite lunit[+]< x > = ↯
    lunit[+][qty]< `∞ > = ↯

    runit[+][qty]<_> : ∀ (x : qty A) → x + zero ≡ x
    runit[+][qty]< ⟨ x ⟩ > rewrite runit[+]< x > = ↯
    runit[+][qty]< `∞ > = ↯

    commu[+][qty]<_,_> : ∀ (x y : qty A) → x + y ≡ y + x
    commu[+][qty]< ⟨ x ⟩ , ⟨ y ⟩ > rewrite commu[+]< x , y > = ↯
    commu[+][qty]< ⟨ x ⟩ , `∞ > = ↯
    commu[+][qty]< `∞ , ⟨ y ⟩ > = ↯
    commu[+][qty]< `∞ , `∞ > = ↯

    assoc[+][qty]<_,_,_> : ∀ (x y z : qty A) → x + (y + z) ≡ (x + y) + z
    assoc[+][qty]< ⟨ x ⟩ , ⟨ y ⟩ , ⟨ z ⟩ > rewrite assoc[+]< x , y , z > = ↯
    assoc[+][qty]< ⟨ x ⟩ , ⟨ y ⟩ , `∞ > = ↯
    assoc[+][qty]< ⟨ x ⟩ , `∞ , ⟨ z ⟩ > = ↯
    assoc[+][qty]< ⟨ x ⟩ , `∞ , `∞ > = ↯
    assoc[+][qty]< `∞ , ⟨ y ⟩ , ⟨ z ⟩ > = ↯
    assoc[+][qty]< `∞ , ⟨ y ⟩ , `∞ > = ↯
    assoc[+][qty]< `∞ , `∞ , ⟨ z ⟩ > = ↯
    assoc[+][qty]< `∞ , `∞ , `∞ > = ↯

  instance
    cor[+][qty] : cor[+] (qty A)
    cor[+][qty] = record
      { lunit[+]<_> = lunit[+][qty]<_>
      ; runit[+]<_> = runit[+][qty]<_>
      ; assoc[+]<_,_,_> = assoc[+][qty]<_,_,_>
      ; commu[+]<_,_> = commu[+][qty]<_,_>
      }

  module _ {{_ : has[×] A}} where
    one[qty] : qty A
    one[qty] = ⟨ one ⟩

    _×[qty]_ : qty A → qty A → qty A
    `∞ ×[qty] _ = `∞
    _ ×[qty] `∞ = `∞
    ⟨ x ⟩ ×[qty] ⟨ y ⟩ = ⟨ x × y ⟩

    {-# DISPLAY _×[qty]_ = _×_ #-}

    instance
      has[×][qty] : has[×] (qty A)
      has[×][qty] = record { one = one[qty] ; _×_ = _×[qty]_ }

    postulate
      instance
        cor[×][qty] : cor[×] (qty A)

module _ {ℓ} {A : Set ℓ} {{_ : has[≡?] A}} where

  _≡?[qty]_ : qty A → qty A → ≡!
  ⟨ x₁ ⟩ ≡?[qty] ⟨ x₂ ⟩ = x₁ ≡? x₂
  ⟨ x₁ ⟩ ≡?[qty] `∞ = [≢]
  `∞ ≡?[qty] ⟨ x₁ ⟩ = [≢]
  `∞ ≡?[qty] `∞ = [≡]

  instance
    has[≡?][qty] : has[≡?] (qty A)
    has[≡?][qty] = record { _≡?_ = _≡?[qty]_ }

  module _ {{_ : cor[≡?] A}} where
    postulate
      instance
        cor[≡?][qty] : cor[≡?] (qty A)

⌉_⌈⸢_⸣ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂}
  {{_ : has[+] A}} {{_ : has[≡?] A}} {{_ : has[+] B}}
  → qty A → qty B → qty B
⌉ x ⌈⸢ y ⸣ with x ≡? ⟨ zero ⟩
… | [≢] = y
… | [≡] = ⟨ zero ⟩

[vec]⌉_⌈⸢_⸣ : ∀ {ℓ₁ ℓ₂} {N} {A : Set ℓ₁} {B : Set ℓ₂} {{_ : has[+] A}} {{_ : has[≡?] A}} {{_ : has[+] B}}
  → ⟬ qty A ⟭[ N ] → qty B → ⟬ qty B ⟭[ N ]
[vec]⌉ xs ⌈⸢ q ⸣ = mapⱽ (λ x → ⌉ x ⌈⸢ q ⸣) xs

-- SENSITIVITIES --
Sens : Set
Sens = qty ℕ

-- sensitivity environment
Σ[_] : ℕ → Set
Σ[ N ] = ⟬ Sens ⟭[ N ]

infix 5 ƛ_⦂_⇒[_]_
infix 6 _∥_⊗_∥_
infix 6 _∥_⊕_∥_

-- TYPES --
data τ : ℕ → Set where
  ƛ⦂_⇒[_]_ : ∀ {N} → τ N → Σ[ ꜱ N ] → τ (ꜱ N) → τ N
  _∥_⊗_∥_ : ∀ {N} → τ N → Σ[ N ] → Σ[ N ] → τ N → τ N
  _∥_⊕_∥_ : ∀ {N} → τ N → Σ[ N ] → Σ[ N ] → τ N → τ N
  unit : ∀ {N} → τ N
  ℝT : ∀ {N} → τ N
  𝔹T : ∀ {N} → τ N

-- type environment
Γ[_] : ℕ → Set
Γ[ N ] =  ⟬ τ N ⟭[ N ]

infix 9 `ℝ_
infix 9 `𝔹_
infix 7 _`+_
infix 8 _`×_
infix 6 _`≤_
infix 9 `_
infix 5 ƛ_⦂_⇒_
infix 7 _`·_
infix 6 inl_⦂_
infix 6 inr_⦂_
infix 6 case_of_⦂_∥_⦂_
infix 6 fst_
infix 6 snd_
infix 4 _::_
infix 6 if_∥_∥_
infix 6 _←_∥_

-- TERMS --

data Term : ℕ → Set where
  -- real numbers
  `ℝ_ : ∀ {N} → 𝔽 → Term N
  _`+_ : ∀ {N} → Term N → Term N → Term N
  _`×_ : ∀ {N} → Term N → Term N → Term N
  _`≤_ : ∀ {N} → Term N → Term N → Term N
  -- variables, functions, application
  `_ : ∀ {N} → idx N → Term N
  ƛ⦂_⇒_ : ∀ {N} → τ N → Term (ꜱ N) → Term N
  _`·_ : ∀ {N} → Term N → Term N
  -- unit
  tt : ∀ {N} → Term N
  -- sums
  inl_⦂_ : ∀ {N} → τ N → Term N → Term N
  inr_⦂_ : ∀ {N} → τ N → Term N → Term N
  case_of_⦂_∥_⦂_ : ∀ {N} → Term N → idx N → Term (N + 1) → idx N → Term (N + 1) → Term N
  -- products
  _〈_,_〉_ : ∀ {N} → Term N → Term N → Term N
  fst_ : ∀ {N} → Term N → Term N
  snd_ : ∀ {N} → Term N → Term N
  -- ascription
  _::_ : ∀ {N} → Term N → τ N → Term N
  -- booleans
  `𝔹_ : ∀ {N} → 𝔹 → Term N
  if_∥_∥_ : ∀ {N} → Term N → Term N → Term N → Term N
  -- let
  _←_∥_ : ∀ {N} → idx N → Term N → Term N

infix 9 inl_
infix 9 inr_
infix 9 𝓇_
infix 9 𝒷_
infix 9 _〈_,_〉_
infix 5 ƛ_⦂_∥_

-- VALUES --
mutual
  data 𝓋 : ℕ → Set where
    tt : ∀ {N} → 𝓋 N
    inl_ : ∀ {N} → 𝓋 N → 𝓋 N
    inr_ : ∀ {N} → 𝓋 N → 𝓋 N
    _〈_,_〉_ : ∀ {N} → 𝓋 N → 𝓋 N → 𝓋 N
    ƛ_⦂_∥_ : ∀ {N} → idx N → Term N → γ[ N ] → 𝓋 N
    𝒷_ : ∀ {N} → 𝔹 → 𝓋 N
    𝓇_ : ∀ {N} → 𝔽 → 𝓋 N

  -- value environment
  γ[_] : ℕ → Set
  γ[ N ] = ⟬ 𝓋 N ⟭[ N ]

-- !!next thing to work on!! --

substΣ/Σ : ∀ {N} → idx (ꜱ N) → Σ[ N ] → Σ[ ꜱ N ] → Σ[ N ]
substΣ/Σ ι Σ₁ Σ₂ = {!!}

substΣ/τ : ∀ {N} → idx (ꜱ N) → Σ[ N ] → τ (ꜱ N) → τ N
substΣ/τ i Σ (ƛ⦂ τ₁ ⇒[ x₁ ] τ₂) = {!   !}
substΣ/τ i Σ (τ₁ ∥ x ⊗ x₁ ∥ τ₂) = {!   !}
substΣ/τ i Σ (τ₁ ∥ x ⊕ x₁ ∥ τ₂) = {!   !}
substΣ/τ i Σ unit = unit
substΣ/τ i Σ ℝT = ℝT
substΣ/τ i Σ 𝔹T = 𝔹T

⇧ˢ′<_> : ∀ {N} → idx N → Σ[ N ] → Σ[ ꜱ N ]
⇧ˢ′< ᴢ > Σ = zero ∷ Σ
⇧ˢ′< ꜱ ι > (σ ∷ Σ) = σ ∷ ⇧ˢ′< ι > Σ

⇧ˢ<_> : ∀ {N} → idx (ꜱ N) → Σ[ N ] → Σ[ ꜱ N ]
⇧ˢ< ᴢ > Σ = zero ∷ Σ
⇧ˢ< ꜱ ι > Σ = ⇧ˢ′< ι > Σ

⇧ᵗ<_> : ∀ {N} → idx (ꜱ N) → τ N → τ (ꜱ N)
⇧ᵗ< ι > (ƛ⦂ τ₁ ⇒[ Σ ] τ₂) = ƛ⦂ ⇧ᵗ< ι > τ₁ ⇒[ ⇧ˢ< ꜱ ι > Σ ] ⇧ᵗ< ꜱ ι > τ₂
⇧ᵗ< ι > (τ₁ ∥ Σ₁ ⊗ Σ₂ ∥ τ₂) = ⇧ᵗ< ι > τ₁ ∥ ⇧ˢ< ι > Σ₁ ⊗ ⇧ˢ< ι > Σ₂ ∥ ⇧ᵗ< ι > τ₂
⇧ᵗ< ι > (τ₁ ∥ Σ₁ ⊕ Σ₂ ∥ τ₂) = {!!}
⇧ᵗ< ι > unit = {!!}
⇧ᵗ< ι > ℝT = {!!}
⇧ᵗ< ι > 𝔹T = {!!}

⇧ᵗ : ∀ {N} → τ N → τ (ꜱ N)
⇧ᵗ = ⇧ᵗ< ᴢ >

-- TYPING JUDGEMENT --
infix 6 _⊢_⦂_,_

data _⊢_⦂_,_ : ∀ {N} → Γ[ N ] → Term N → τ N → Σ[ N ] → Set where

  -- RLIT
  ⊢`ℝ : ∀ {Γ : Γ[ 0 ]} {r : 𝔽}
      --------------------------------
    → Γ ⊢ (`ℝ r) ⦂ ℝT , []

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
  ⊢`_ : ∀ {N} {Γ : Γ[ N ]} {Σ : Σ[ N ]} {i : idx N} {τ : τ N}
    → Γ #[ i ] ≡ τ
    --------------------------------------------------
    → Γ ⊢  ` i ⦂ τ , Σ + zero #[ i ↦ ⟨ 1 ⟩ ]

  -- LAM
  ⊢`λ : ∀ {N} {Γ : Γ[ N ]} {Σ₁ : Σ[ ꜱ N ]} {i : idx N} {e : Term (ꜱ N)} {τ₁ : τ N} {τ₂ : τ (ꜱ N)}
    -- weakenτ ∷ τ N → τ (ꜱ N)
    -- weakenΓ ∷ Γ[ N ] → Γ[ ꜱ N ]
    →  (mapⱽ ⇧ᵗ (τ₁ ∷ Γ)) ⊢ e ⦂ τ₂ , Σ₁
    -----------------------------------------------
    → Γ ⊢ (ƛ⦂ τ₁ ⇒ e) ⦂ (ƛ⦂ τ₁ ⇒[ Σ₁ ] τ₂) , zero

  -- APP
  -- _`⋅_ : ∀ {N} {Γ : Γ[ N ]} {Σ₁ Σ₂ : Σ[ N ]} {e₁ e₂ : Term N} {τ₁ τ₂ : τ N} {s : sens}
  --   → Γ ⊢ e₁ ⦂ τ₁ ⊸[ s ] τ₂, Σ₁
  --   → Γ ⊢ e₂ ⦂ τ₁, Σ₂
  --   -----------------------------------------------
  --   → Γ , (Σ₁ + (s ⨵ Σ₂)) [s]⊢ e₁ `⋅ e₂ ⦂ τ₂


two : Term 0
two = `ℝ 2.0

⊢two : ∀ {Γ : Γ[ 0 ]} → Γ ⊢ two ⦂ ℝT , []
⊢two = ⊢`ℝ

_ : ⟬ ℕ ⟭[ 2 ]
_ = 1 ∷ 0 ∷ []

_ : ⟬ ℕ ⟭[ 2 ]
_ = 1 ∷ 0 ∷ [] + 1 ∷ 0 ∷ []

_ : (1 ∷ 0 ∷ [] AT ⟬ ℕ ⟭[ 2 ]) + (1 ∷ 0 ∷ [] AT ⟬ ℕ ⟭[ 2 ]) ≡ (2 ∷ 0 ∷ [])
_ = ↯
