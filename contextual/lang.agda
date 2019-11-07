-- CITATION: Jacob Wunder's proof of metric space conservation for Duet 1.0

{-# OPTIONS --allow-unsolved-metas #-}
module lang where

open import UVMVS public

_ : ℕ
_ = 2

_ : 𝔽
_ = 2.0

_ : 𝔽
_ = primNatToFloat 2

natToFloat : ℕ → 𝔽
natToFloat = primNatToFloat

_ : 𝔹
_ = ɪ

_ : 𝔹
_ = ᴏ

data _≤_ {ℓ ℓᴿ} {A : Set ℓ} {{_ : has[<][ ℓᴿ ] A}} (x y : A) : Set ℓᴿ where
  [≡] : x ≡ y → x ≤ y
  [<] : x < y → x ≤ y

_≤?_ : ℕ → ℕ → 𝔹
ᴢ ≤? _ = ɪ
ꜱ m ≤? ᴢ = ᴏ
ꜱ m ≤? ꜱ n = m ≤? n

module _ {ℓ ℓᴿ} {A : Set ℓ} {{_ : has[<][ ℓᴿ ] A}} {{_ : cor[<] A}} where
  postulate
    instance
      reflexive[≤] : reflexive (_≤_ AT (A → A → Set ℓᴿ))
      antisymmetric[≤] : antisymmetric (_≤_ AT (A → A → Set ℓᴿ))
      transitive[≤] : transitive (_≤_ AT (A → A → Set ℓᴿ))

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

  absorb[∞/+]<_> : ∀ (x : qty A) → x + `∞ ≡ `∞
  absorb[∞/+]< x > = ↯

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

module _ {ℓ} {A : Set ℓ} where
  module _ {{_ : has[⊔] A}} where
    _⊔[qty]_ : qty A → qty A → qty A
    _ ⊔[qty] `∞ = `∞
    `∞ ⊔[qty] _ = `∞
    ⟨ x ⟩ ⊔[qty] ⟨ y ⟩ = ⟨ x ⊔ y ⟩

    instance
      has[⊔][qty] : has[⊔] (qty A)
      has[⊔][qty] = record { _⊔_ = _⊔[qty]_ }

  module _ {{_ : has[⋚?] A}} where
    _⋚?[qty]_ : qty A → qty A → ⋚!
    ⟨ x ⟩ ⋚?[qty] ⟨ y ⟩ = x ⋚? y
    ⟨ _ ⟩ ⋚?[qty] `∞ = [<]
    `∞ ⋚?[qty] ⟨ _ ⟩ = [>]
    `∞ ⋚?[qty] `∞ = [≡]

    instance
      has[⋚?][qty] : has[⋚?] (qty A)
      has[⋚?][qty] = record { _⋚?_ = _⋚?[qty]_ }


module _ {ℓ ℓᴿ} {A : Set ℓ} {{_ : has[<][ ℓᴿ ] A}} where

  data _<[qty]_ : qty A → qty A → Set ℓᴿ where
    `∞ : {x : A} → ⟨ x ⟩ <[qty] `∞
    ⟨_⟩ : ∀ {x y : A} (ε : x < y) → ⟨ x ⟩ <[qty] ⟨ y ⟩

  instance
    has[<][qty] : has[<][ ℓᴿ ] (qty A)
    has[<][qty] = record { _<_ = _<[qty]_ }

  module _ {{_ : cor[<] A}} where
    postulate
      instance
        cor[<][qty] : cor[<] (qty A)
    module _ {{_ : has[⋚?] A}} {{_ : cor[⋚?] A}} where
      postulate
        instance
          cor[⋚?][qty] : cor[⋚?] (qty A)

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

-- TYPES --
data τ : ℕ → Set where
  ƛ⦂_⇒[_∔_]_ : ∀ {N} → τ N → Sens → Σ[ ꜱ N ] → τ (ꜱ N) → τ N
  _∥_∔_⊗_∔_∥_ : ∀ {N} → τ N → Sens → Σ[ N ] → Sens → Σ[ N ] → τ N → τ N
  _∥_∔_⊕_∔_∥_ : ∀ {N} → τ N → Sens → Σ[ N ] → Sens → Σ[ N ] → τ N → τ N
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
infix 5 ƛ⦂_⇒_
infix 7 _`app_
infix 6 inl_∥_
infix 6 inr_∥_
infix 6 case_of_∥_
infix 6 _`pair_
infix 6 fst_
infix 6 snd_
infix 4 _::_
infix 6 if_∥_∥_
infix 6 `let_∥_

-- TERMS --

data Term : ℕ → Set where
  -- real numbers
  `ℝ_ : ∀ {N} → ℕ → Term N
  _`+_ : ∀ {N} → Term N → Term N → Term N
  _`×_ : ∀ {N} → Term N → Term N → Term N
  _`≤_ : ∀ {N} → Term N → Term N → Term N
  -- variables, functions, application
  `_ : ∀ {N} → idx N → Term N
  ƛ⦂_⇒_ : ∀ {N} → τ N → Term (ꜱ N) → Term N
  _`app_ : ∀ {N} → Term N → Term N → Term N
  -- unit
  tt : ∀ {N} → Term N
  -- sums
  inl_∥_ : ∀ {N} → τ N → Term N → Term N
  inr_∥_ : ∀ {N} → τ N → Term N → Term N
  case_of_∥_ : ∀ {N} → Term N → Term (ꜱ N) → Term (ꜱ N) → Term N
  -- products
  _`pair_ : ∀ {N} → Term N → Term N → Term N
  fst_ : ∀ {N} → Term N → Term N
  snd_ : ∀ {N} → Term N → Term N
  -- ascription
  _::_ : ∀ {N} → Term N → τ N → Term N
  -- booleans
  `𝔹_ : ∀ {N} → 𝔹 → Term N
  if_∥_∥_ : ∀ {N} → Term N → Term N → Term N → Term N
  -- let
  `let_∥_ : ∀ {N} → Term N → Term (ꜱ N) → Term N

infix 9 inl_
infix 9 inr_
infix 9 𝓇_
infix 9 𝒷_
infix 9 _pair_
infix 5 ƛ⦂_∥_

-- VALUES --
mutual
  data 𝓋 : Set where
    tt : 𝓋
    inl_ : 𝓋 → 𝓋
    inr_ : 𝓋 → 𝓋
    _pair_ : 𝓋 → 𝓋 → 𝓋
    ƛ⦂_∥_ : ∀ {N} → Term (ꜱ N) → γ[ N ] → 𝓋
    𝒷_ : 𝔹 → 𝓋
    𝓇_ : ℕ → 𝓋

  -- value environment
  γ[_] : ℕ → Set
  γ[ N ] = ⟬ 𝓋 ⟭[ N ]

pred : ∀ (N : ℕ) → idx N → ℕ
pred (ꜱ N) ᴢ = N
pred (ꜱ N) (ꜱ ι) = ꜱ (pred N ι)

infix 6 _⊟_

_⊟_ : ∀ {ℓ} {A : Set ℓ} {N} (ι : idx N) → ⟬ A ⟭[ N ] → ⟬ A ⟭[ pred N ι ]
ᴢ ⊟ x ∷ xs = xs
ꜱ ι ⊟ x ∷ xs = x ∷ (ι ⊟ xs)
-- ᴢ ⊟ x ∷ vec = vec
-- ꜱ () ⊟ [ x ]
-- ꜱ ι ⊟ x ∷ y ∷ vec = x ∷ (ι ⊟ (y ∷ vec))

substΣ/Σ : ∀ {N} → (ι : idx N) → Σ[ pred N ι ] → Σ[ N ] → Σ[ pred N ι ]
substΣ/Σ ι Σ₁ Σ₂ =
  let s = Σ₂ #[ ι ] in
  let scaled = s ⨵ Σ₁ in
  (ι ⊟ Σ₂) + scaled

wkΣ : ∀ {N} → (ι : idx N) → Σ[ pred N ι ] → Σ[ N ]
wkΣ ᴢ Σ = zero ∷ Σ
wkΣ (ꜱ ι) (x ∷ Σ) = x ∷ wkΣ ι Σ

substΣ/τ : ∀ {N} → (ι : idx N) → Σ[ pred N ι ] → τ N → τ (pred N ι)
substΣ/τ i Σ (ƛ⦂ τ₁ ⇒[ x₀ ∔ Σ′ ] τ₂) = ƛ⦂ substΣ/τ i Σ τ₁ ⇒[  x₀ ∔ substΣ/Σ (ꜱ i) (wkΣ ᴢ Σ) Σ′ ] substΣ/τ (ꜱ i) (wkΣ ᴢ Σ) τ₂
substΣ/τ i Σ (τ₁ ∥ x₀₀ ∔ x ⊗ x₀₁ ∔ x₁ ∥ τ₂) = substΣ/τ i Σ τ₁ ∥ x₀₀ ∔ substΣ/Σ i Σ x ⊗ x₀₁ ∔ substΣ/Σ i Σ x₁ ∥ substΣ/τ i Σ τ₂
substΣ/τ i Σ (τ₁ ∥ x₀₀ ∔ x ⊕ x₀₁ ∔ x₁ ∥ τ₂) =  substΣ/τ i Σ τ₁ ∥ x₀₀ ∔ substΣ/Σ i Σ x ⊕ x₀₁ ∔ substΣ/Σ i Σ x₁ ∥ substΣ/τ i Σ τ₂
substΣ/τ i Σ unit = unit
substΣ/τ i Σ ℝT = ℝT
substΣ/τ i Σ 𝔹T = 𝔹T

cut : ∀ {N} → Σ[ N ] → τ (ꜱ N) → τ N
cut Σ τ = substΣ/τ ᴢ Σ τ

instantiateΣ/Σ : ∀ {N N′} → Σ[ N ] → Σ[ N′ + N ] → qty ℕ ∧ Σ[ N′ ]
instantiateΣ/Σ {N′ = ᴢ} Σ₁ Σ₂ = ⟨ Σ₁ ⨰ Σ₂ , [] ⟩
instantiateΣ/Σ {N′ = ꜱ N′} Σ₁ (s ∷ Σ₂) = let ⟨ s′ , Σ′ ⟩ = instantiateΣ/Σ Σ₁ Σ₂ in ⟨ s′ , s ∷ Σ′ ⟩

instantiateΣ/τ : ∀ {N N′} → Σ[ N ] → τ (N′ + N) → τ N′
instantiateΣ/τ Σ (ƛ⦂ τ₁ ⇒[ s ∔ Σ′ ] τ₂) = let ⟨ s′ , Σ′ ⟩ = instantiateΣ/Σ Σ Σ′ in ƛ⦂ instantiateΣ/τ Σ τ₁ ⇒[ s + s′ ∔ Σ′ ] instantiateΣ/τ Σ τ₂
instantiateΣ/τ Σ (τ₁ ∥ x ∔ x₁ ⊗ x₂ ∔ x₃ ∥ τ₂) = {!!}
instantiateΣ/τ Σ (τ₁ ∥ x ∔ x₁ ⊕ x₂ ∔ x₃ ∥ τ₂) = {!!}
instantiateΣ/τ Σ unit = {!!}
instantiateΣ/τ Σ ℝT = {!!}
instantiateΣ/τ Σ 𝔹T = {!!}

⇧ˢ′<_> : ∀ {N} → idx N → Σ[ N ] → Σ[ ꜱ N ]
⇧ˢ′< ᴢ > Σ = zero ∷ Σ
⇧ˢ′< ꜱ ι > (σ ∷ Σ) = σ ∷ ⇧ˢ′< ι > Σ

⇧ˢ<_> : ∀ {N} → idx (ꜱ N) → Σ[ N ] → Σ[ ꜱ N ]
⇧ˢ< ᴢ > Σ = zero ∷ Σ
⇧ˢ< ꜱ ι > Σ = ⇧ˢ′< ι > Σ

⇧ᵗ<_> : ∀ {N} → idx (ꜱ N) → τ N → τ (ꜱ N)
⇧ᵗ< ι > (ƛ⦂ τ₁ ⇒[  x₀ ∔ Σ ] τ₂) = ƛ⦂ ⇧ᵗ< ι > τ₁ ⇒[  x₀ ∔ ⇧ˢ< ꜱ ι > Σ ] ⇧ᵗ< ꜱ ι > τ₂
⇧ᵗ< ι > (τ₁ ∥ x₀₀ ∔ Σ₁ ⊗ x₀₁ ∔  Σ₂ ∥ τ₂) = ⇧ᵗ< ι > τ₁ ∥ x₀₀ ∔  ⇧ˢ< ι > Σ₁ ⊗ x₀₁ ∔ ⇧ˢ< ι > Σ₂ ∥ ⇧ᵗ< ι > τ₂
⇧ᵗ< ι > (τ₁ ∥ x₀₀ ∔ Σ₁ ⊕ x₀₁ ∔  Σ₂ ∥ τ₂) = ⇧ᵗ< ι > τ₁ ∥ x₀₀ ∔  ⇧ˢ< ι > Σ₁ ⊕ x₀₁ ∔ ⇧ˢ< ι > Σ₂ ∥ ⇧ᵗ< ι > τ₂
⇧ᵗ< ι > unit = unit
⇧ᵗ< ι > ℝT = ℝT
⇧ᵗ< ι > 𝔹T = 𝔹T

⇧ᵗ : ∀ {N} → τ N → τ (ꜱ N)
⇧ᵗ = ⇧ᵗ< ᴢ >

⇧ˢ : ∀ {N} → Σ[ N ] → Σ[ (ꜱ N) ]
⇧ˢ = ⇧ˢ< ᴢ >

-- -- JOINS AND MEETS
-- _⊔ᴺ_ : ℕ → ℕ → ℕ
-- ᴢ ⊔ᴺ ᴢ = ᴢ
-- ᴢ ⊔ᴺ ꜱ n = ꜱ n
-- ꜱ m ⊔ᴺ ᴢ = ꜱ m
-- ꜱ m ⊔ᴺ ꜱ n = ꜱ (m ⊔ᴺ n)

instance
  has[⊥][ℕ] : has[⊥] ℕ
  has[⊥][ℕ] = record { ⊥ = 0 }

  has[⊔][ℕ] : has[⊔] ℕ
  has[⊔][ℕ] = record { _⊔_ = _⩏_ }

  has[⊓][ℕ] : has[⊓] ℕ
  has[⊓][ℕ] = record { _⊓_ = _⩎_ }

mutual
  _τ[⊔]_ : ∀ {N} → τ N → τ N → ⦉ τ N ⦊
  (ƛ⦂ τ₁₁ ⇒[  x₀₀ ∔ Σ₁ ] τ₁₂) τ[⊔] (ƛ⦂ τ₂₁ ⇒[  x₀₁ ∔ Σ₂ ] τ₂₂) with τ₁₁ τ[⊓] τ₂₁ | τ₁₂ τ[⊔] τ₂₂
  … | ⟨ τ₁′ ⟩ | ⟨ τ₂′ ⟩ = ⟨ ƛ⦂ τ₁′ ⇒[ (x₀₀ ⊔ x₀₁) ∔ Σ₁ ⊔ Σ₂ ] τ₂′  ⟩
  … | _ | _ = •
  (τ₁₁ ∥ x₀₀ ∔ Σ₁₁ ⊗ x₀₁ ∔ Σ₁₂ ∥ τ₁₂) τ[⊔] (τ₂₁ ∥ x₀₂ ∔ Σ₂₁ ⊗ x₀₃ ∔ Σ₂₂ ∥ τ₂₂) with τ₁₁ τ[⊔] τ₂₁ | τ₁₂ τ[⊔] τ₂₂
  … | ⟨ τ₁′ ⟩ | ⟨ τ₂′ ⟩ = ⟨ τ₁′ ∥ (x₀₀ ⊔ x₀₂) ∔ Σ₁₁ ⊔ Σ₂₁ ⊗ (x₀₁ ⊔ x₀₃) ∔ Σ₁₂ ⊔ Σ₂₂ ∥ τ₂′ ⟩
  … | _ | _ = •
  (τ₁₁ ∥  x₀₀ ∔ Σ₁₁ ⊕ x₀₁ ∔ Σ₁₂ ∥ τ₁₂) τ[⊔] (τ₂₁ ∥ x₀₂ ∔ Σ₂₁ ⊕ x₀₃ ∔ Σ₂₂ ∥ τ₂₂) with τ₁₁ τ[⊔] τ₂₁ | τ₁₂ τ[⊔] τ₂₂
  … | ⟨ τ₁′ ⟩ | ⟨ τ₂′ ⟩ = ⟨ τ₁′ ∥  (x₀₀ ⊔ x₀₂)  ∔ Σ₁₁ ⊔ Σ₂₁ ⊕  (x₀₁ ⊔ x₀₃)  ∔ Σ₁₂ ⊔ Σ₂₂ ∥ τ₂′ ⟩
  … | _ | _ = •
  unit τ[⊔] unit = ⟨ unit ⟩
  ℝT τ[⊔] ℝT = ⟨ ℝT ⟩
  𝔹T τ[⊔] 𝔹T = ⟨ 𝔹T ⟩
  _ τ[⊔] _ = •

  _τ[⊓]_ : ∀ {N} → τ N → τ N → ⦉ τ N ⦊
  (ƛ⦂ τ₁₁ ⇒[  x₀₀ ∔ Σ₁ ] τ₁₂) τ[⊓] (ƛ⦂ τ₂₁ ⇒[ x₀₁ ∔ Σ₂ ] τ₂₂) = {!   !}
  (τ₁₁ ∥ x₀₀ ∔ Σ₁₁ ⊗ x₀₁ ∔ Σ₁₂ ∥ τ₁₂) τ[⊓] (τ₂₁ ∥ x₀₂ ∔ Σ₂₁ ⊗ x₀₃ ∔ Σ₂₂ ∥ τ₂₂) = {!   !}
  (τ₁₁ ∥ x₀₀ ∔ Σ₁₁ ⊕ x₀₁ ∔ Σ₁₂ ∥ τ₁₂) τ[⊓] (τ₂₁ ∥ x₀₂ ∔ Σ₂₁ ⊕ x₀₃ ∔ Σ₂₂ ∥ τ₂₂) = {!   !} -- τ₁₁ τ[⊔] τ₂₁ ∥ Σ₁₁ ⊔ Σ₂₁ ⊕ Σ₁₂ ⊔ Σ₂₂ ∥ τ₁₂ τ[⊔] τ₂₂
  unit τ[⊓] unit = ⟨ unit ⟩
  ℝT τ[⊓] ℝT = ⟨ ℝT ⟩
  𝔹T τ[⊓] 𝔹T = ⟨ 𝔹T ⟩
  _  τ[⊓] _ = •
