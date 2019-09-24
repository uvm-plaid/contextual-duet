module contextual where

open import UVMVS.Core public
open import UVMVS.Lib public

_ : ℕ
_ = 2

_ : 𝔽
_ = 2.0

_ : 𝔹
_ = ɪ

_ : 𝔹
_ = ᴏ

𝕏 : Set
𝕏 = ℕ

infix 9 𝕤_
-- sensitivity
data Sens : Set where
  ∞  : Sens
  𝕤_ : 𝔽 → Sens

infix 7 _+̂_

_+̂_ : Sens → Sens → Sens
∞ +̂ _ = ∞
_ +̂ ∞ = ∞
𝕤 x +̂ 𝕤 x₁ = 𝕤 (primFloatPlus x x₁)

infix 8 _×̂_

_×̂_ : Sens → Sens → Sens
𝕤 0.0 ×̂ _ = 𝕤 0.0
_ ×̂ 𝕤 0.0 = 𝕤 0.0
∞ ×̂ _ = ∞
_ ×̂ ∞ = ∞
𝕤 x ×̂ 𝕤 x₁ = 𝕤 (primFloatTimes x x₁)

-- sensitivity environment
Σ[_] : ℕ → Set
Σ[ N ] = ⟬ Sens ⟭[ N ]

infix 5 ƛ_⦂_⇒[_]_
infix 6 _∥_⊗_∥_
infix 6 _∥_⊕_∥_

-- types
data τ : ℕ → Set where
  ƛ_⦂_⇒[_]_ : ∀ {N} → 𝕏 → τ N → Σ[ N ] → τ N → τ N
  _∥_⊗_∥_ : ∀ {N} → τ N → Σ[ N ] → Σ[ N ] → τ N → τ N
  _∥_⊕_∥_ : ∀ {N} → τ N → Σ[ N ] → Σ[ N ] → τ N → τ N
  unit : ∀ {N} → τ N
  ℝT : ∀ {N} → τ N
  𝔹T : ∀ {N} → τ N

-- type environment
Γ[_] : ℕ → Set
Γ[ N ] =  ⟬ τ N ⟭[ N ]

-- type environment lookup judgement
-- infix 4 _∋Γ⟨_↦_⟩
-- data _∋Γ⟨_↦_⟩ : ∀ {N : ℕ} → Γ[ N ] → idx N → τ → Set where
-- -- data _∋Γ_ : Γ → τ → Set where
--
--   Z : ∀ {Γ N M A}
--       ---------
--     → Γ[ N ] ∋Γ⟨ ⌊ M ⌋ ↦ A ⟩
--
--   S_ : ∀ {Γ A B}
--     → Γ ∋Γ A
--       ---------
--     → Γ , B ∋Γ A
--
-- _ : ∅ , 𝔹T , unit ∋Γ unit
-- _ = Z
--
-- _ : ∅ , 𝔹T , ℝT , unit ∋Γ ℝT
-- _ = S Z

infix 9 𝕣_
infix 9 𝕓_
infix 7 _⊞̂_
infix 8 _·_
infix 6 _≤_
infix 9 `_
infix 5 ƛ_⦂_⇒_
infix 7 _⊚̂_
infix 6 inl_⦂_
infix 6 inr_⦂_
infix 6 case_of_⦂_∥_⦂_
infix 6 fst_
infix 6 snd_
infix 4 _::_
infix 6 if_∥_∥_
infix 6 _←_∥_


data Term : ℕ → Set where
  -- real numbers
  𝕣_ : ∀ {N} → 𝔽 → Term N
  _⊞̂_ : ∀ {N} → Term N → Term N → Term N
  _·_ : ∀ {N} → Term N → Term N → Term N
  _≤_ : ∀ {N} → Term N → Term N → Term N
  -- variables, functions, application
  `_ : ∀ {N} → 𝕏 → Term N
  ƛ_⦂_⇒_ : ∀ {N} → 𝕏 → τ N → Term N → Term N
  _⊚̂_ : ∀ {N} → Term N → Term N
  -- unit
  tt : ∀ {N} → Term N
  -- sums
  inl_⦂_ : ∀ {N} → τ N → Term N → Term N
  inr_⦂_ : ∀ {N} → τ N → Term N → Term N
  case_of_⦂_∥_⦂_ : ∀ {N} → Term N → 𝕏 → Term N → 𝕏 → Term N → Term N
  -- products
  _〈_,_〉_ : ∀ {N} → Term N → Term N → Term N
  fst_ : ∀ {N} → Term N → Term N
  snd_ : ∀ {N} → Term N → Term N
  -- ascription
  _::_ : ∀ {N} → Term N → τ N → Term N
  -- booleans
  𝕓_ : ∀ {N} → 𝔹 → Term N
  if_∥_∥_ : ∀ {N} → Term N → Term N → Term N → Term N
  -- let
  _←_∥_ : ∀ {N} → 𝕏 → Term N → Term N

infix 9 inl_
infix 9 inr_
infix 9 𝓇_
infix 9 𝒷_
infix 9 _〈_,_〉_
infix 5 ƛ_⦂_∥_

-- values
mutual
  data 𝓋 : ℕ → Set where
    tt : ∀ {N} → 𝓋 N
    inl_ : ∀ {N} → 𝓋 N → 𝓋 N
    inr_ : ∀ {N} → 𝓋 N → 𝓋 N
    _〈_,_〉_ : ∀ {N} → 𝓋 N → 𝓋 N → 𝓋 N
    ƛ_⦂_∥_ : ∀ {N} → 𝕏 → Term N → γ[ N ] → 𝓋 N
    𝒷_ : ∀ {N} → 𝔹 → 𝓋 N
    𝓇_ : ∀ {N} → 𝔽 → 𝓋 N

  -- value environment
  γ[_] : ℕ → Set
  γ[ N ] = ⟬ 𝓋 N ⟭[ N ]

-- typing judgement
infix 6 _⊢_⦂_,_

data _⊢_⦂_,_ : ∀ {N} → Γ[ N ] → Term N → τ N → Σ[ N ] → Set where

  -- RLIT
  ⊢rlit : ∀ {Γ : Γ[ 0 ]} {r : 𝔽}
      -----------
    → Γ ⊢ (𝕣 r) ⦂ ℝT , []

two : Term 0
two = 𝕣 2.0

⊢two : ∀ {Γ : Γ[ 0 ]} → Γ ⊢ two ⦂ ℝT , []
⊢two = ⊢rlit

_ : ⟬ ℕ ⟭[ 2 ]
_ = 1 ∷ 0 ∷ []

_ : ⟬ ℕ ⟭[ 2 ]
_ = 1 ∷ 0 ∷ [] + 1 ∷ 0 ∷ []

_ : (1 ∷ 0 ∷ [] AT ⟬ ℕ ⟭[ 2 ]) + (1 ∷ 0 ∷ [] AT ⟬ ℕ ⟭[ 2 ]) ≡ (2 ∷ 0 ∷ [])
_ = ↯
