-- CITATION: Jacob Wunder's proof of metric space conservation for Duet 1.0

module contextual where

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

infix 5 ƛ⦂_⇒[_]_
infix 7 _∥_⊗_∥_
infix 7 _∥_⊕_∥_

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
substΣ/τ i Σ (ƛ⦂ τ₁ ⇒[ Σ′ ] τ₂) = ƛ⦂ substΣ/τ i Σ τ₁ ⇒[ substΣ/Σ (ꜱ i) (wkΣ ᴢ Σ) Σ′ ] substΣ/τ (ꜱ i) (wkΣ ᴢ Σ) τ₂
substΣ/τ i Σ (τ₁ ∥ x ⊗ x₁ ∥ τ₂) = substΣ/τ i Σ τ₁ ∥ substΣ/Σ i Σ x ⊗ substΣ/Σ i Σ x₁ ∥ substΣ/τ i Σ τ₂
substΣ/τ i Σ (τ₁ ∥ x ⊕ x₁ ∥ τ₂) =  substΣ/τ i Σ τ₁ ∥ substΣ/Σ i Σ x ⊕ substΣ/Σ i Σ x₁ ∥ substΣ/τ i Σ τ₂
substΣ/τ i Σ unit = unit
substΣ/τ i Σ ℝT = ℝT
substΣ/τ i Σ 𝔹T = 𝔹T

cut : ∀ {N} → Σ[ N ] → τ (ꜱ N) → τ N
cut Σ τ = substΣ/τ ᴢ Σ τ

⇧ˢ′<_> : ∀ {N} → idx N → Σ[ N ] → Σ[ ꜱ N ]
⇧ˢ′< ᴢ > Σ = zero ∷ Σ
⇧ˢ′< ꜱ ι > (σ ∷ Σ) = σ ∷ ⇧ˢ′< ι > Σ

⇧ˢ<_> : ∀ {N} → idx (ꜱ N) → Σ[ N ] → Σ[ ꜱ N ]
⇧ˢ< ᴢ > Σ = zero ∷ Σ
⇧ˢ< ꜱ ι > Σ = ⇧ˢ′< ι > Σ

⇧ᵗ<_> : ∀ {N} → idx (ꜱ N) → τ N → τ (ꜱ N)
⇧ᵗ< ι > (ƛ⦂ τ₁ ⇒[ Σ ] τ₂) = ƛ⦂ ⇧ᵗ< ι > τ₁ ⇒[ ⇧ˢ< ꜱ ι > Σ ] ⇧ᵗ< ꜱ ι > τ₂
⇧ᵗ< ι > (τ₁ ∥ Σ₁ ⊗ Σ₂ ∥ τ₂) = ⇧ᵗ< ι > τ₁ ∥ ⇧ˢ< ι > Σ₁ ⊗ ⇧ˢ< ι > Σ₂ ∥ ⇧ᵗ< ι > τ₂
⇧ᵗ< ι > (τ₁ ∥ Σ₁ ⊕ Σ₂ ∥ τ₂) = ⇧ᵗ< ι > τ₁ ∥ ⇧ˢ< ι > Σ₁ ⊕ ⇧ˢ< ι > Σ₂ ∥ ⇧ᵗ< ι > τ₂
⇧ᵗ< ι > unit = unit
⇧ᵗ< ι > ℝT = ℝT
⇧ᵗ< ι > 𝔹T = 𝔹T

⇧ᵗ : ∀ {N} → τ N → τ (ꜱ N)
⇧ᵗ = ⇧ᵗ< ᴢ >

⇧ˢ : ∀ {N} → Σ[ N ] → Σ[ (ꜱ N) ]
⇧ˢ = ⇧ˢ< ᴢ >

-- JOINS AND MEETS
_⊔ᴺ_ : ℕ → ℕ → ℕ
ᴢ ⊔ᴺ ᴢ = ᴢ
ᴢ ⊔ᴺ ꜱ n = ꜱ n
ꜱ m ⊔ᴺ ᴢ = ꜱ m
ꜱ m ⊔ᴺ ꜱ n = ꜱ (m ⊔ᴺ n)

instance
  has[⊥][ℕ] : has[⊥] ℕ
  has[⊥][ℕ] = record { ⊥ = 0 }

  has[⊔][ℕ] : has[⊔] ℕ
  has[⊔][ℕ] = record { _⊔_ = _⊔ᴺ_ }

mutual
  _τ[⊔]_ : ∀ {N} → τ N → τ N → ⦉ τ N ⦊
  (ƛ⦂ τ₁₁ ⇒[ Σ₁ ] τ₁₂) τ[⊔] (ƛ⦂ τ₂₁ ⇒[ Σ₂ ] τ₂₂) with τ₁₁ τ[⊓] τ₂₁ | τ₁₂ τ[⊔] τ₂₂
  … | ⟨ τ₁′ ⟩ | ⟨ τ₂′ ⟩ = ⟨ ƛ⦂ τ₁′ ⇒[ Σ₁ ⊔ Σ₂ ] τ₂′  ⟩
  … | _ | _ = •
  (τ₁₁ ∥ Σ₁₁ ⊗ Σ₁₂ ∥ τ₁₂) τ[⊔] (τ₂₁ ∥ Σ₂₁ ⊗ Σ₂₂ ∥ τ₂₂) with τ₁₁ τ[⊔] τ₂₁ | τ₁₂ τ[⊔] τ₂₂
  … | ⟨ τ₁′ ⟩ | ⟨ τ₂′ ⟩ = ⟨ τ₁′ ∥ Σ₁₁ ⊔ Σ₂₁ ⊗ Σ₁₂ ⊔ Σ₂₂ ∥ τ₂′ ⟩
  … | _ | _ = •
  (τ₁₁ ∥ Σ₁₁ ⊕ Σ₁₂ ∥ τ₁₂) τ[⊔] (τ₂₁ ∥ Σ₂₁ ⊕ Σ₂₂ ∥ τ₂₂) with τ₁₁ τ[⊔] τ₂₁ | τ₁₂ τ[⊔] τ₂₂
  … | ⟨ τ₁′ ⟩ | ⟨ τ₂′ ⟩ = ⟨ τ₁′ ∥ Σ₁₁ ⊔ Σ₂₁ ⊕ Σ₁₂ ⊔ Σ₂₂ ∥ τ₂′ ⟩
  … | _ | _ = •
  unit τ[⊔] unit = ⟨ unit ⟩
  ℝT τ[⊔] ℝT = ⟨ ℝT ⟩
  𝔹T τ[⊔] 𝔹T = ⟨ 𝔹T ⟩
  _ τ[⊔] _ = •

  _τ[⊓]_ : ∀ {N} → τ N → τ N → ⦉ τ N ⦊
  (ƛ⦂ τ₁₁ ⇒[ Σ₁ ] τ₁₂) τ[⊓] (ƛ⦂ τ₂₁ ⇒[ Σ₂ ] τ₂₂) = {!   !}
  (τ₁₁ ∥ Σ₁₁ ⊗ Σ₁₂ ∥ τ₁₂) τ[⊓] (τ₂₁ ∥ Σ₂₁ ⊗ Σ₂₂ ∥ τ₂₂) = {!   !}
  (τ₁₁ ∥ Σ₁₁ ⊕ Σ₁₂ ∥ τ₁₂) τ[⊓] (τ₂₁ ∥ Σ₂₁ ⊕ Σ₂₂ ∥ τ₂₂) = {!   !} -- τ₁₁ τ[⊔] τ₂₁ ∥ Σ₁₁ ⊔ Σ₂₁ ⊕ Σ₁₂ ⊔ Σ₂₂ ∥ τ₁₂ τ[⊔] τ₂₂
  unit τ[⊓] unit = ⟨ unit ⟩
  ℝT τ[⊓] ℝT = ⟨ ℝT ⟩
  𝔹T τ[⊓] 𝔹T = ⟨ 𝔹T ⟩
  _  τ[⊓] _ = •

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
      → γ ⊢ e₁ `≤ e₂ ⇓ 𝒷 (r₁ ≤? r₂) -- NOTE: strict inequality

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
    → γ ⊢ e₁ ⇓ inl 𝓋₁
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
  ⊢`λ : ∀ {N} {γ : γ[ N ]} {e : Term (ꜱ N)} {τ : τ N}
    -----------------------------------------------
    → γ ⊢ (ƛ⦂ τ ⇒ e) ⇓ (ƛ⦂ e ∥ γ )

  -- APP
  ⊢`app : ∀ {N} {γ γ′ : γ[ N ]} {e′ : Term (ꜱ N)} {e₁ e₂ : Term N} {𝓋₁ 𝓋₂ : 𝓋}
    → γ ⊢ e₁ ⇓ (ƛ⦂ e′ ∥ γ′ )
    → γ ⊢ e₂ ⇓ 𝓋₁
    → 𝓋₁ ∷ γ′ ⊢ e′ ⇓ 𝓋₂
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
    → γ ⊢ fst e ⇓ 𝓋₂


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
    → Γ ⊢ (inl τ₂ ∥ e) ⦂ (τ₁ ∥ Σ₁ ⊕ zero ∥ τ₂)  , zero

  -- INR
  ⊢`inr : ∀ {N} {Γ : Γ[ N ]} {Σ₂ : Σ[ N ]} {e : Term N} {τ₁ τ₂ : τ N}
    → Γ ⊢ e ⦂ τ₂ , Σ₂
    --------------------------------------------------
    → Γ ⊢ (inr τ₁ ∥ e) ⦂ τ₁ ∥ zero ⊕ Σ₂ ∥ τ₂  , zero

  -- CASE
  ⊢`case : ∀ {N} {Γ : Γ[ N ]} {Σ₁ Σ₁₁ Σ₁₂ Σ₂ Σ₃ : Σ[ N ]} {i : idx (ꜱ N)} {e₁ : Term N} {e₂ e₃ : Term (ꜱ N)} {τ₁₁ τ₁₂ τ₂ τ₃ τ₄ : τ N} {s₂ s₃ : Sens}
    → Γ ⊢ e₁ ⦂ τ₁₁ ∥ Σ₁₁ ⊕ Σ₁₂ ∥ τ₁₂ , Σ₁
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
  ⊢`λ : ∀ {N} {Γ : Γ[ N ]} {Σ₁ : Σ[ ꜱ N ]} {i : idx N} {e : Term (ꜱ N)} {τ₁ : τ N} {τ₂ : τ (ꜱ N)}
    →  (mapⱽ ⇧ᵗ (τ₁ ∷ Γ)) ⊢ e ⦂ τ₂ , Σ₁
    -----------------------------------------------
    → Γ ⊢ (ƛ⦂ τ₁ ⇒ e) ⦂ (ƛ⦂ τ₁ ⇒[ Σ₁ ] τ₂) , zero

  -- APP
  ⊢`app : ∀ {N} {i : idx (ꜱ N)} {Γ : Γ[ N ]} {Σ₁ Σ₂ : Σ[ N ]} {e₁ e₂ : Term N} {τ₁ τ₂ : τ N} {s : Sens}
    → Γ ⊢ e₁ ⦂ (ƛ⦂ τ₁ ⇒[ s ∷ Σ₁ ] ⇧ᵗ τ₂) , zero
    → Γ ⊢ e₂ ⦂ τ₁ , Σ₂
    -----------------------------------------------------------
    → Γ ⊢ (e₁ `app e₂) ⦂ cut Σ₂ (⇧ᵗ τ₂) , (Σ₁ + (s ⨵ Σ₂))

  -- PAIR
  ⊢`_pair_ : ∀ {N} {Γ : Γ[ N ]} {Σ₁ Σ₂ : Σ[ N ]} {e₁ e₂ : Term N} {τ₁ τ₂ : τ N}
    → Γ ⊢ e₁ ⦂ τ₁ , Σ₁
    → Γ ⊢ e₂ ⦂ τ₂ , Σ₂
    -----------------------------------------------------------
    → Γ ⊢ e₁ `pair e₂ ⦂ τ₁ ∥ Σ₁ ⊗ Σ₂ ∥ τ₂ , zero

  -- PROJ1
  ⊢`fst : ∀ {N} {Γ : Γ[ N ]} {Σ Σ₁ Σ₂ : Σ[ N ]} {e : Term N} {τ₁ τ₂ : τ N}
    → Γ ⊢ e ⦂ τ₁ ∥ Σ₁ ⊗ Σ₂ ∥ τ₂ , Σ
  --------------------------------------
    → Γ ⊢ fst e ⦂ τ₁ , Σ + Σ₁

  -- PROJ2
  ⊢`snd : ∀ {N} {Γ : Γ[ N ]} {Σ Σ₁ Σ₂ : Σ[ N ]} {e : Term N} {τ₁ τ₂ : τ N}
    → Γ ⊢ e ⦂ τ₁ ∥ Σ₁ ⊗ Σ₂ ∥ τ₂ , Σ
  -----------------------------------------
    → Γ ⊢ fst e ⦂ τ₂ , Σ + Σ₂

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
--   instance
--     has[<] : ∀ {ℓ ℓᴿ} {A : Set ℓ} {{_ : has[<][ ℓᴿ ] A}} → has[<][ ℓᴿ ] (qty A)

data 𝓋τ : ℕ → Set where
  ƛ⦂_⇒[_∔_]_ : ∀ {N} → 𝓋τ N → Sens → Σ[ ꜱ N ] → 𝓋τ (ꜱ N) → 𝓋τ N
  _∥_∔_⊗_∔_∥_ : ∀ {N} → 𝓋τ N → Sens → Σ[ N ] → Sens → Σ[ N ] → 𝓋τ N → 𝓋τ N
  _∥_∔_⊕_∔_∥_ : ∀ {N} → 𝓋τ N → Sens → Σ[ N ] → Sens → Σ[ N ] → 𝓋τ N → 𝓋τ N
  unit : ∀ {N} → 𝓋τ N
  ℝT : ∀ {N} → 𝓋τ N
  𝔹T : ∀ {N} → 𝓋τ N

substSx/τ : Sens → 𝓋τ 1 → 𝓋τ ᴢ
substSx/τ s (ƛ⦂ x ⇒[ x₁ ∔ x₂ ] τ₁) = {!   !} -- ƛ⦂ substSx/τ s x ⇒[ (x₁ × s) ∔ x₂ ] τ₁
substSx/τ s (τ₁ ∥ x ∔ x₁ ⊗ x₂ ∔ x₃ ∥ τ₂) = {!   !} -- (τ₁ ∥ x ∔ x₁ ⊗ x₂ ∔ x₃ ∥ τ₂)
substSx/τ s (τ₁ ∥ x ∔ x₁ ⊕ x₂ ∔ x₃ ∥ τ₂) = {!   !} -- (τ₁ ∥ x ∔ x₁ ⊕ x₂ ∔ x₃ ∥ τ₂)
substSx/τ s unit = unit
substSx/τ s ℝT = ℝT
substSx/τ s 𝔹T = 𝔹T

-- value type environment
ℾ[_] : ℕ → Set
ℾ[ N ] =  ⟬ 𝓋τ ᴢ ⟭[ N ]

-- TYPING JUDGEMENT FOR VALUES --
infix 6 _⊢_⦂_

data _⊢_⦂_ : ∀ {N} → ℾ[ N ] → 𝓋 → 𝓋τ N → Set where

  ⊢𝓇 : ∀ {N} {ℾ : ℾ[ N ]} {r : ℕ}
      --------------------------------
    → ℾ ⊢ (𝓇 r) ⦂ ℝT

  ⊢𝒷 : ∀ {N} {ℾ : ℾ[ N ]} {b : 𝔹}
      --------------------------------
    → ℾ ⊢ (𝒷 b) ⦂ 𝔹T

  ⊢tt : ∀ {N} {ℾ : ℾ[ N ]}
      --------------------------------
    → ℾ ⊢ tt ⦂ unit

  ⊢inl : ∀ {N} {ℾ : ℾ[ N ]} {v τ₁ τ₂ s₁}
      --------------------------------
    → ℾ ⊢ (inl v) ⦂ τ₁ ∥ s₁ ∔ zero ⊕ zero ∔ zero ∥ τ₂

  ⊢inr : ∀ {N} {ℾ : ℾ[ N ]} {v τ₁ τ₂ s₂}
      --------------------------------
    → ℾ ⊢ (inr v) ⦂ τ₁ ∥ zero ∔ zero ⊕ s₂ ∔ zero ∥ τ₂

  ⊢pair : ∀ {N} {ℾ : ℾ[ N ]} {v₁ v₂ τ₁ τ₂ s₁ s₂}
    → ℾ ⊢ v₁ ⦂ τ₁
    → ℾ ⊢ v₂ ⦂ τ₂
      --------------------------------
    → ℾ ⊢ (v₁ pair v₂) ⦂ τ₁ ∥ s₁ ∔ zero ⊗ s₂ ∔ zero ∥ τ₂

  ⊢λ : ∀ {N} {ℾ : ℾ[ N ]} {e : Term (ꜱ N)} {γ : γ[ N ]} {τ₁ τ₂ s′}
      --------------------------------
    → ℾ ⊢ (ƛ⦂ e ∥ γ ) ⦂ ƛ⦂ τ₁ ⇒[ s′ ∔ zero ] τ₂


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

    𝒱λ : ∀ {e₁ e₂ γ₁ γ₂ v₁ v₂ τ₁ τ₂ s s′ s′′ s′′′ Σ Σ′}
      →  ∃ Γ ST ⟨ γ₁ , γ₂ ⟩∈𝒢⟦ Σ′ ː Γ ⟧
      → ⟨ v₁ , v₂ ⟩∈𝒱⟦ s′′ ː τ₁ ⟧
      → ⟨ (v₁ ∷ γ₁) ⊢ e₁ , (v₂ ∷ γ₂) ⊢ e₂ ⟩∈ℰ⟦ (s + (Σ ⨰ Σ′) + (s′ × s′′)) ː (substSx/τ s′′ τ₂) ⟧
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
