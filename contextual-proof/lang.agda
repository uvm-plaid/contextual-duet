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

    -- DCD: worried about this... we will want to fix this eventually
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

-- PRIVACIES --
Priv : Set
Priv = qty ℕ

-- privacy environment
Σₚ[_] : ℕ → Set
Σₚ[ N ] = ⟬ Priv ⟭[ N ]

L1N : ∀ {N} → Σₚ[ N ] → Priv
L1N σ = foldrⱽ ⟨ zero ⟩ _+_ σ

infix 5 sƛ⦂_∥_⇒[_∔_]_
infix 5 pƛ⦂_∥_⇒[_∔_]_

-- TYPES --
data τ : ℕ → Set where
  sƛ⦂_∥_⇒[_∔_]_ : ∀ {N} → τ N → Sens → Sens → Σ[ ꜱ N ] → τ (ꜱ N) → τ N
  pƛ⦂_∥_⇒[_∔_]_ : ∀ {N} → τ N → Sens → Priv → Σₚ[ ꜱ N ] → τ (ꜱ N) → τ N
  _∥_∔_⊗_∔_∥_ : ∀ {N} → τ N → Sens → Σ[ N ] → Sens → Σ[ N ] → τ N → τ N
  _∥_∔_⊕_∔_∥_ : ∀ {N} → τ N → Sens → Σ[ N ] → Sens → Σ[ N ] → τ N → τ N
  unit : ∀ {N} → τ N
  ℝT : ∀ {N} → τ N
  𝔹T : ∀ {N} → τ N

-- type environment
Γ[_] : ℕ → Set
Γ[ N ] =  ⟬ τ N ⟭[ N ]

-- value type environment
ℾ[_] : ℕ → Set
ℾ[ N ] =  ⟬ τ ᴢ ⟭[ N ]

infix 9 `ℝ_
infix 9 `𝔹_
infix 7 _`+_
infix 8 _`×_
infix 6 _`≤_
infix 9 `_
infix 5 sƛ⦂_∥_⇒_
infix 5 pƛ⦂_∥_⇒_
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

mutual

  data PTerm : ℕ → Set where
    _`papp_ : ∀ {N} → Term N → Term N → PTerm N
    `return_ : ∀ {N} → Term N → PTerm N
    `bind_∥_ : ∀ {N} → PTerm N → PTerm (ꜱ N) → PTerm N
    pcase_of_∥_ : ∀ {N} → Term N → PTerm (ꜱ N) → PTerm (ꜱ N) → PTerm N

  data Term : ℕ → Set where
    -- real numbers
    `ℝ_ : ∀ {N} → ℕ → Term N
    _`+_ : ∀ {N} → Term N → Term N → Term N
    _`×_ : ∀ {N} → Term N → Term N → Term N
    _`≤_ : ∀ {N} → Term N → Term N → Term N
    -- variables, functions, application
    `_ : ∀ {N} → idx N → Term N
    sƛ⦂_∥_⇒_ : ∀ {N} → τ N → Sens → Term (ꜱ N) → Term N
    pƛ⦂_∥_⇒_ : ∀ {N} → τ N → Sens → PTerm (ꜱ N) → Term N
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
infix 6 sƛ⦂_∥_
infix 6 pƛ⦂_∥_

-- VALUES --
mutual
  data 𝓋 : Set where
    tt : 𝓋
    inl_ : 𝓋 → 𝓋
    inr_ : 𝓋 → 𝓋
    _pair_ : 𝓋 → 𝓋 → 𝓋
    sƛ⦂_∥_ : ∀ {N} → Term (ꜱ N) → γ[ N ] → 𝓋
    pƛ⦂_∥_ : ∀ {N} → PTerm (ꜱ N) → γ[ N ] → 𝓋
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

substΣ/Σ : ∀ {N} → (ι : idx N) → Σ[ pred N ι ] → Σ[ N ] → Σ[ pred N ι ]
substΣ/Σ ι Σ₁ Σ₂ =
  let s = Σ₂ #[ ι ] in
  let scaled = s ⨵ Σ₁ in
  (ι ⊟ Σ₂) + scaled

substΣ/Σₚ : ∀ {N} → (ι : idx N) → Σ[ pred N ι ] → Σₚ[ N ] → Σₚ[ pred N ι ]
substΣ/Σₚ ι Σ₁ Σ₂ =
  let p = Σ₂ #[ ι ] in
  let tr = [vec]⌉ Σ₁ ⌈⸢ p ⸣ in
  (ι ⊟ Σ₂) + tr

wkΣ : ∀ {N} → (ι : idx N) → Σ[ pred N ι ] → Σ[ N ]
wkΣ ᴢ Σ = zero ∷ Σ
wkΣ (ꜱ ι) (x ∷ Σ) = x ∷ wkΣ ι Σ

substΣ/τ : ∀ {N} → (ι : idx N) → Σ[ pred N ι ] → τ N → τ (pred N ι)
substΣ/τ i Σ (sƛ⦂ τ₁ ∥ s ⇒[ x₀ ∔ Σ′ ] τ₂) = sƛ⦂ substΣ/τ i Σ τ₁ ∥ s ⇒[  x₀ ∔ substΣ/Σ (ꜱ i) (wkΣ ᴢ Σ) Σ′ ] substΣ/τ (ꜱ i) (wkΣ ᴢ Σ) τ₂
substΣ/τ i Σ (pƛ⦂ τ₁ ∥ s ⇒[ x₀ ∔ Σ′ ] τ₂) = pƛ⦂ substΣ/τ i Σ τ₁ ∥ s ⇒[  x₀ ∔ substΣ/Σₚ (ꜱ i) (wkΣ ᴢ Σ) Σ′ ] substΣ/τ (ꜱ i) (wkΣ ᴢ Σ) τ₂
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


instantiateΣ/Σₚ : ∀ {N N′} → Σ[ N ] → Σ[ N′ + N ] → qty ℕ ∧ Σ[ N′ ]
instantiateΣ/Σₚ {N′ = ᴢ} Σ₁ Σ₂ = ⟨ [vec]⌉ Σ₁ ⌈⸢ one ⸣ ⨰ Σ₂ , [] ⟩
instantiateΣ/Σₚ {N′ = ꜱ N′} Σ₁ (s ∷ Σ₂) = let ⟨ s′ , Σ′ ⟩ = instantiateΣ/Σ Σ₁ Σ₂ in ⟨ s′ , s ∷ Σ′ ⟩

instantiateΣ/τ : ∀ {N N′} → Σ[ N ] → τ (N′ + N) → τ N′
instantiateΣ/τ Σ (sƛ⦂ τ₁ ∥ s₁ ⇒[ s ∔ Σ′ ] τ₂) = let ⟨ s′ , Σ′ ⟩ = instantiateΣ/Σ Σ Σ′ in sƛ⦂ instantiateΣ/τ Σ τ₁ ∥ s₁ ⇒[ s + s′ ∔ Σ′ ] instantiateΣ/τ Σ τ₂
instantiateΣ/τ Σ (pƛ⦂ τ₁ ∥ s₁ ⇒[ s ∔ Σ′ ] τ₂) = let ⟨ s′ , Σ′ ⟩ = instantiateΣ/Σₚ Σ Σ′ in pƛ⦂ instantiateΣ/τ Σ τ₁ ∥ s₁ ⇒[ s + s′ ∔ Σ′ ] instantiateΣ/τ Σ τ₂
instantiateΣ/τ Σ (τ₁ ∥ x ∔ x₁ ⊗ x₂ ∔ x₃ ∥ τ₂) = {!!}
instantiateΣ/τ Σ (τ₁ ∥ x ∔ x₁ ⊕ x₂ ∔ x₃ ∥ τ₂) = {!!}
instantiateΣ/τ Σ unit = unit
instantiateΣ/τ Σ ℝT = ℝT
instantiateΣ/τ Σ 𝔹T = 𝔹T

⇧ˢ′<_> : ∀ {N} → idx N → Σ[ N ] → Σ[ ꜱ N ]
⇧ˢ′< ᴢ > Σ = zero ∷ Σ
⇧ˢ′< ꜱ ι > (σ ∷ Σ) = σ ∷ ⇧ˢ′< ι > Σ

⇧ˢ<_> : ∀ {N} → idx (ꜱ N) → Σ[ N ] → Σ[ ꜱ N ]
⇧ˢ< ᴢ > Σ = zero ∷ Σ
⇧ˢ< ꜱ ι > Σ = ⇧ˢ′< ι > Σ

⇧ᵗ<_> : ∀ {N} → idx (ꜱ N) → τ N → τ (ꜱ N)
⇧ᵗ< ι > (sƛ⦂ τ₁ ∥ s₁ ⇒[  x₀ ∔ Σ ] τ₂) = sƛ⦂ ⇧ᵗ< ι > τ₁ ∥ s₁ ⇒[  x₀ ∔ ⇧ˢ< ꜱ ι > Σ ] ⇧ᵗ< ꜱ ι > τ₂
⇧ᵗ< ι > (pƛ⦂ τ₁ ∥ s₁ ⇒[  x₀ ∔ Σ ] τ₂) = pƛ⦂ ⇧ᵗ< ι > τ₁ ∥ s₁ ⇒[  x₀ ∔ ⇧ˢ< ꜱ ι > Σ ] ⇧ᵗ< ꜱ ι > τ₂
⇧ᵗ< ι > (τ₁ ∥ x₀₀ ∔ Σ₁ ⊗ x₀₁ ∔  Σ₂ ∥ τ₂) = ⇧ᵗ< ι > τ₁ ∥ x₀₀ ∔  ⇧ˢ< ι > Σ₁ ⊗ x₀₁ ∔ ⇧ˢ< ι > Σ₂ ∥ ⇧ᵗ< ι > τ₂
⇧ᵗ< ι > (τ₁ ∥ x₀₀ ∔ Σ₁ ⊕ x₀₁ ∔  Σ₂ ∥ τ₂) = ⇧ᵗ< ι > τ₁ ∥ x₀₀ ∔  ⇧ˢ< ι > Σ₁ ⊕ x₀₁ ∔ ⇧ˢ< ι > Σ₂ ∥ ⇧ᵗ< ι > τ₂
⇧ᵗ< ι > unit = unit
⇧ᵗ< ι > ℝT = ℝT
⇧ᵗ< ι > 𝔹T = 𝔹T

⇧ᵗ : ∀ {N} → τ N → τ (ꜱ N)
⇧ᵗ = ⇧ᵗ< ᴢ >

⇧ˢ : ∀ {N} → Σ[ N ] → Σ[ (ꜱ N) ]
⇧ˢ = ⇧ˢ< ᴢ >

instance
  has[⊥][ℕ] : has[⊥] ℕ
  has[⊥][ℕ] = record { ⊥ = 0 }

  has[⊔][ℕ] : has[⊔] ℕ
  has[⊔][ℕ] = record { _⊔_ = _⩏_ }

  has[⊓][ℕ] : has[⊓] ℕ
  has[⊓][ℕ] = record { _⊓_ = _⩎_ }

mutual
  postulate
    _τ[⊔]_ : ∀ {N} → τ N → τ N → ⦉ τ N ⦊
    _τ[⊓]_ : ∀ {N} → τ N → τ N → ⦉ τ N ⦊
    _τ[≤]_ : ∀ {N} → τ N → τ N → Set

-- DCD: could define τ[≤] as
--
--     τ₁ ≤ τ₂ ⟺ (τ₁ ⊔ τ₂ ≡ τ₂)
--
-- but this might not give you good inversion principles, e.g., if you
-- know (τ₁₁ × τ₁₂) ≤ (τ₂₁ × τ₂₂) then it should be that (τ₁₁ ≤ τ₂₁)
-- and (τ₁₂ ≤ τ₂₂). To get easy access to all of these inversion
-- principles, we are probably better off defining ≤ on types directly
-- as an inductive datatype. It should still be the case that
-- τ₁ ≤ τ₂ ⟺ (τ₁ ⊔ τ₂ ≡ τ₂), and we could prove this correspondance if
-- we wanted, although it most likely it be necessary.


_⟨⟨_⟩⟩ : ∀ {N} → Σ[ N ] → τ N → τ ᴢ
Σ ⟨⟨ sƛ⦂ τ₁ ∥ s ⇒[ a₀ ∔ a ∷ x ] τ₂ ⟩⟩ = sƛ⦂ (Σ ⟨⟨ τ₁ ⟩⟩) ∥ s ⇒[ ((Σ ⨰ x) + a₀) ∔ a ∷ [] ] ⇧ᵗ (⇧ˢ Σ ⟨⟨ τ₂ ⟩⟩)
Σ ⟨⟨ pƛ⦂ τ₁ ∥ s ⇒[ a₀ ∔ a ∷ x ] τ₂ ⟩⟩ = pƛ⦂ (Σ ⟨⟨ τ₁ ⟩⟩) ∥ s ⇒[ (([vec]⌉ Σ ⌈⸢ one ⸣ ⨰ x) + a₀) ∔ a ∷ [] ] ⇧ᵗ (⇧ˢ Σ ⟨⟨ τ₂ ⟩⟩)
Σ ⟨⟨ τ₁ ∥ a₀ ∔ x ⊗ b₀ ∔ x₁ ∥ τ₂ ⟩⟩ = (Σ ⟨⟨ τ₁ ⟩⟩) ∥ (a₀ + (Σ ⨰ x)) ∔ zero ⊗ (b₀ + (Σ ⨰ x₁)) ∔ zero ∥  (Σ ⟨⟨ τ₂ ⟩⟩)
Σ ⟨⟨ τ₁ ∥ a₀ ∔ x ⊕ b₀ ∔ x₁ ∥ τ₂ ⟩⟩ = (Σ ⟨⟨ τ₁ ⟩⟩) ∥ (a₀ + (Σ ⨰ x)) ∔ zero ⊕ (b₀ + (Σ ⨰ x₁)) ∔ zero ∥  (Σ ⟨⟨ τ₂ ⟩⟩)
Σ ⟨⟨ unit ⟩⟩ = unit
Σ ⟨⟨ ℝT ⟩⟩ = ℝT
Σ ⟨⟨ 𝔹T ⟩⟩ = 𝔹T


substSx/τ<_> : ∀ {N} (ι : idx N) → Sens → τ N → τ (pred N ι)
substSx/τ< ι > s (sƛ⦂ τ₁ ∥ s₁ ⇒[ c ∔ Σ ] τ₂) =
  sƛ⦂ substSx/τ< ι > s τ₁ ∥ s₁ ⇒[ c + s × Σ #[ ꜱ ι ] ∔ ꜱ ι ⊟ Σ  ] substSx/τ< ꜱ ι > s τ₂
substSx/τ< ι > s (pƛ⦂ τ₁ ∥ s₁ ⇒[ c ∔ Σ ] τ₂) =
  pƛ⦂ substSx/τ< ι > s τ₁ ∥ s₁ ⇒[ c + ([vec]⌉ [ s ] ⌈⸢ one ⸣ ⨰ [ Σ #[ ꜱ ι ] ])  ∔ ꜱ ι ⊟ Σ  ] substSx/τ< ꜱ ι > s τ₂
substSx/τ< ι > s (τ₁ ∥ c₁ ∔ Σ₁ ⊗ c₂ ∔ Σ₂ ∥ τ₂) =
  substSx/τ< ι > s τ₁ ∥ c₁ + s × Σ₁ #[ ι ] ∔ ι ⊟ Σ₁ ⊗ c₂ + s × Σ₂ #[ ι ] ∔ ι ⊟ Σ₂ ∥ substSx/τ< ι > s τ₂
substSx/τ< ι > s (τ₁ ∥ c₁ ∔ Σ₁ ⊕ c₂ ∔ Σ₂ ∥ τ₂) =
  substSx/τ< ι > s τ₁ ∥ c₁ + s × Σ₁ #[ ι ] ∔ ι ⊟ Σ₁ ⊕ c₂ + s × Σ₂ #[ ι ] ∔ ι ⊟ Σ₂ ∥ substSx/τ< ι > s τ₂
substSx/τ< ι > s unit = unit
substSx/τ< ι > s ℝT = ℝT
substSx/τ< ι > s 𝔹T = 𝔹T

substSx/τ : ∀ {N} → Sens → τ (ꜱ N) → τ N
substSx/τ = substSx/τ< ᴢ >

_ : (do x ← return $ 𝕣 1
        y ← laplace
        return $ x + y)
  ≡ (do y ← laplace
        return $ 𝕣 1 + y)
_ = lunit[≫=]
