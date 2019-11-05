{-# OPTIONS --allow-unsolved-metas #-}
module proof where

open import rules public

mutual
  -- this is for sensitivity, we will need another one for privacy
  ⟨_⊢_,_⊢_⟩∈ℰ⟦_ː_⟧ : ∀ {N} → γ[ N ] → Term N → γ[ N ] → Term N → Sens → τ ᴢ → Set
  ⟨ γ₁ ⊢ e₁ , γ₂ ⊢ e₂ ⟩∈ℰ⟦ s ː τ ⟧ = ∀ v₁ v₂ → (ε₁ : ⊢ v₁ ⦂ τ) → (ε₂ : ⊢ v₂ ⦂ τ) → (γ₁ ⊢ e₁ ⇓ v₁) ∧ (γ₂ ⊢ e₂ ⇓ v₂) → ⟨ v₁ , v₂ ⟩∈𝒱′⟦ τ ː ε₁ , ε₂ ː s ⟧

  ⟨_,_⟩∈𝒢⟦_ː_⟧ : ∀ {N} → γ[ N ] → γ[ N ] → Σ[ N ] → ℾ[ N ] → Set
  ⟨ γ₁ , γ₂ ⟩∈𝒢⟦ Σ ː ℾ ⟧ = ∀ x → (ε₁ : ⊢ γ₁ #[ x ] ⦂ ℾ #[ x ]) → (ε₂ : ⊢ γ₂ #[ x ] ⦂ ℾ #[ x ]) → ⟨ γ₁ #[ x ] , γ₂ #[ x ] ⟩∈𝒱′⟦ ℾ #[ x ] ː ε₁ , ε₂ ː Σ #[ x ] ⟧

  {-# TERMINATING #-}
  ⟨_,_⟩∈𝒱′⟦_ː_,_ː_⟧ : ∀ (v₁ v₂ : 𝓋) (t : τ ᴢ) → ⊢ v₁ ⦂ t → ⊢ v₂ ⦂ t → Sens →  Set
  ⟨ .(ƛ⦂ e₁ ∥ γ₁) , .(ƛ⦂ e₂ ∥ γ₂) ⟩∈𝒱′⟦ ƛ⦂ τ₁ ⇒[ s′′ ∔ s‴ ] τ₂
                                 ː ⊢λ {N = N₁} {ℾ = ℾ₁} {e = e₁} {γ = γ₁} H₁₁ H₁₂ H₁₃ H₁₄ H₁₅
                                 , ⊢λ {N = N₂} {ℾ = ℾ₂} {e = e₂} {γ = γ₂} H₂₁ H₂₂ H₂₃ H₂₄ H₂₅
                                 ː s ⟧ =
    ∃ ε ⦂ N₁ ≡ N₂ ST
    subst[(λ N → ⟬ τ N ⟭[ N ] )] ε ℾ₁ ≡ ℾ₂
    ∧
    (∀ {v₁ v₂ ε₁ ε₂ s s′ s′′ s′′′ Σ Σ′} → ⟨ subst[(λ N → γ[ N ] )] ε γ₁ , γ₂ ⟩∈𝒢⟦ Σ′ ː mapⱽ (instantiateΣ/τ Σ′) ℾ₂ ⟧
    → ⟨ v₁ , v₂ ⟩∈𝒱′⟦ τ₁ ː ε₁ , ε₂ ː s′′ ⟧
    → ⟨ (v₁ ∷ subst[(λ N → γ[ N ] )] ε γ₁) ⊢ subst[(λ N → Term (ꜱ N) )] ε e₁ , (v₂ ∷ γ₂) ⊢ e₂ ⟩∈ℰ⟦ (s + (Σ ⨰ Σ′) + (s′ × s′′)) ː (substSx/τ s′′ τ₂) ⟧)
  ⟨ v₁₁ pair v₁₂ , v₂₁ pair v₂₂ ⟩∈𝒱′⟦ τ₁ ∥ s₁ ∔ [] ⊗ s₂ ∔ [] ∥ τ₂ ː ⊢pair δ₁₁ δ₁₂ , ⊢pair δ₂₁ δ₂₂ ː s ⟧ =
    ⟨ v₁₁ , v₂₁ ⟩∈𝒱′⟦ τ₁ ː δ₁₁ , δ₂₁ ː s + s₁ ⟧
    ∧
    ⟨ v₁₂ , v₂₂ ⟩∈𝒱′⟦ τ₂ ː δ₁₂ , δ₂₂ ː s + s₂ ⟧
  ⟨ inl v₁ , inl v₂ ⟩∈𝒱′⟦ τ₁ ∥ s₁ ∔ [] ⊕ s₂ ∔ [] ∥ τ₂ ː ⊢inl δ₁ , ⊢inl δ₂ ː s ⟧ =
    ⟨ v₁ , v₂ ⟩∈𝒱′⟦ τ₁ ː δ₁ , δ₂ ː s + s₁ ⟧
  ⟨ inl v₁ , inr v₂ ⟩∈𝒱′⟦ τ₁ ∥ s₁ ∔ [] ⊕ s₂ ∔ [] ∥ τ₂ ː ⊢inl δ₁ , ⊢inr δ₂ ː s ⟧ = s ≡ `∞
  ⟨ inr v₁ , inl v₂ ⟩∈𝒱′⟦ τ₁ ∥ s₁ ∔ [] ⊕ s₂ ∔ [] ∥ τ₂ ː ⊢inr δ₁ , ⊢inl δ₂ ː s ⟧ = s ≡ `∞
  ⟨ inr v₁ , inr v₂ ⟩∈𝒱′⟦ τ₁ ∥ s₁ ∔ [] ⊕ s₂ ∔ [] ∥ τ₂ ː ⊢inr δ₁ , ⊢inr δ₂ ː s ⟧ =
    ⟨ v₁ , v₂ ⟩∈𝒱′⟦ τ₂ ː δ₁ , δ₂ ː s + s₂ ⟧
  ⟨ v₁ , v₂ ⟩∈𝒱′⟦ unit ː δ₁ , δ₂ ː s ⟧ = v₁ ≡ tt ∧ v₂ ≡ tt
  ⟨ (𝓇 r₁) , (𝓇 r₂) ⟩∈𝒱′⟦ ℝT ː ⊢𝓇 , ⊢𝓇 ː s ⟧ = ⟨ ∣ r₁ - r₂ ∣ ⟩ ≤ s
  ⟨ v₁ , v₂ ⟩∈𝒱′⟦ 𝔹T ː δ₁ , δ₂ ː s ⟧ = {!!}

_⟨⟨_⟩⟩ : ∀ {N} → Σ[ N ] → τ N → τ ᴢ
Σ ⟨⟨ ƛ⦂ τ₁ ⇒[ a₀ ∔ x ] τ₂ ⟩⟩ = ƛ⦂ (Σ ⟨⟨ τ₁ ⟩⟩) ⇒[ (((⇧ˢ Σ) ⨰ x) + a₀) ∔ zero ] ⇧ᵗ (⇧ˢ Σ ⟨⟨ τ₂ ⟩⟩)
Σ ⟨⟨ τ₁ ∥ a₀ ∔ x ⊗ b₀ ∔ x₁ ∥ τ₂ ⟩⟩ = (Σ ⟨⟨ τ₁ ⟩⟩) ∥ (a₀ + (Σ ⨰ x)) ∔ zero ⊗ (b₀ + (Σ ⨰ x₁)) ∔ zero ∥  (Σ ⟨⟨ τ₂ ⟩⟩)
Σ ⟨⟨ τ₁ ∥ a₀ ∔ x ⊕ b₀ ∔ x₁ ∥ τ₂ ⟩⟩ = (Σ ⟨⟨ τ₁ ⟩⟩) ∥ (a₀ + (Σ ⨰ x)) ∔ zero ⊕ (b₀ + (Σ ⨰ x₁)) ∔ zero ∥  (Σ ⟨⟨ τ₂ ⟩⟩)
Σ ⟨⟨ unit ⟩⟩ = unit
Σ ⟨⟨ ℝT ⟩⟩ = ℝT
Σ ⟨⟨ 𝔹T ⟩⟩ = 𝔹T

-- Theorem 1.1 (Fundamental Property / (Metric Preservation in Fuzz)).

postulate
  L1 : ∀ (N : ℕ) → ∣ N - N ∣ ≡ 0
  L2 : ∀ (N : ℕ) → ⟨ ∣ N - N ∣ ⟩ ≡< qty ℕ > ⟨ 0 ⟩
  L3 : ∀ {a b c d N : ℕ} {Σ₁ Σ₂ Σ₃ : Σ[ N ]} → ⟨ ∣ a - b ∣ ⟩ ≤ (Σ₁ ⨰ Σ₃) → ⟨ ∣ c - d ∣ ⟩ ≤ (Σ₂ ⨰ Σ₃) → ⟨ ∣ (a + c) - (b + d) ∣ ⟩ ≤ ((Σ₁ + Σ₂) ⨰ Σ₃)
  L4 : ∀ {N} (Σ₁ Σ₂ Σ₃ : Σ[ N ]) → (Σ₁ ⨰ Σ₃) + (Σ₂ ⨰ Σ₃) ≡ ((Σ₁ + Σ₂) ⨰ Σ₃)
  L5 : ∀ {N} (Σ₁ Σ₂ : Σ[ N ]) → (Σ₁ ⨰ Σ₂) ≡ (Σ₂ ⨰ Σ₁)
  ◇[≡] : ∀ {A} {x y : A} → x ≡ y → y ≡ x

fp : ∀ {N} {Γ : Γ[ N ]} {ℾ e τ Σ γ₁ γ₂ Σ′} → Γ ⊢ e ⦂ τ , Σ → ⟨ γ₁ , γ₂ ⟩∈𝒢⟦ Σ′ ː ℾ ⟧ → ⟨ γ₁ ⊢ e , γ₂ ⊢ e ⟩∈ℰ⟦ Σ ⨰ Σ′ ː (Σ′ ⟨⟨ τ ⟩⟩) ⟧
fp {Σ′ = Σ′} ⊢`ℝ e₂ (𝓇 r₁) (𝓇 r₁) ⊢𝓇 ⊢𝓇 ⟨ ⊢`ℝ , ⊢`ℝ ⟩ rewrite lzero[⨰]< Σ′ > = [≡] (L2 r₁)
fp ⊢`𝔹 e₂ = {!   !}
fp (⊢ δ₁ `+ δ₂) r[γ₁,γ₂] (𝓇 .(r₁₁ + r₁₂)) (𝓇 .(r₂₁ + r₂₂)) ⊢𝓇 ⊢𝓇 ⟨ ⊢_`+_ {r₁ = r₁₁} {r₂ = r₁₂} jr₁₁ jr₂₁ , ⊢_`+_  {r₁ = r₂₁} {r₂ = r₂₂} jr₁₂ jr₂₂ ⟩
  with fp δ₁ r[γ₁,γ₂] (𝓇 r₁₁) (𝓇 r₂₁) ⊢𝓇 ⊢𝓇 ⟨ jr₁₁ , jr₁₂ ⟩
     | fp δ₂ r[γ₁,γ₂] (𝓇 r₁₂) (𝓇 r₂₂) ⊢𝓇 ⊢𝓇 ⟨ jr₂₁ , jr₂₂ ⟩
… | IH₁ | IH₂ = L3 IH₁ IH₂
fp (⊢ e₁ `× e₂) r[γ₁,γ₂] .(𝓇 (r₁₁ ×ᴺ r₁₂)) .(𝓇 (r₂₁ ×ᴺ r₂₂)) ⊢𝓇 ⊢𝓇 ⟨ ⊢_`×_ {r₁ = r₁₁} {r₁₂} jr₁₁ jr₂₁ , ⊢_`×_ {r₁ = r₂₁} {r₂₂} jr₁₂ jr₂₂ ⟩
  with fp e₁ r[γ₁,γ₂] (𝓇 r₁₁) (𝓇 r₂₁) ⊢𝓇 ⊢𝓇 ⟨ jr₁₁ , jr₁₂ ⟩
     | fp e₂ r[γ₁,γ₂] (𝓇 r₁₂) (𝓇 r₂₂) ⊢𝓇 ⊢𝓇 ⟨ jr₂₁ , jr₂₂ ⟩
… | IH₁ | IH₂ = {!   !}
fp (⊢ e₁ `≤ e₂) r[γ₁,γ₂] = {!   !}
fp (⊢`var_ {i = i} x) r[γ₁,γ₂] .(_ #[ i ]) .(_ #[ i ]) e1 e2 ⟨ ⊢`var ↯ , ⊢`var ↯ ⟩ with r[γ₁,γ₂] i {!  !} {!   !}
... | G = {!   !}
fp ⊢`tt r[γ₁,γ₂] .tt .tt ⊢tt ⊢tt ⟨ ⊢`tt , ⊢`tt ⟩ = ⟨ ↯ , ↯ ⟩
fp {Σ′ = Σ′} (⊢`inl {Σ₁ = Σ₁} e₁) r[γ₁,γ₂] .(inl 𝓋₁) .(inl 𝓋₂) (⊢inl jv₁) (⊢inl jv₂) ⟨ ⊢`inl {𝓋 = 𝓋₁} r₁ , ⊢`inl {𝓋 = 𝓋₂} r₂ ⟩
  with fp e₁ r[γ₁,γ₂] 𝓋₁ 𝓋₂ jv₁ jv₂ ⟨ r₁ , r₂ ⟩
... | IH rewrite lzero[⨰]< Σ′ >
    | lunit[+][qty]< (⟨ 0 ⟩ +[qty] (Σ′ ⨰ Σ₁)) >
    | lunit[+][qty]< (Σ′ ⨰ Σ₁) >
    | L5 Σ′ Σ₁ = IH
fp {Σ′ = Σ′} (⊢`inr {Σ₂ = Σ₂} e₁) r[γ₁,γ₂] .(inr 𝓋₁) .(inr 𝓋₂) (⊢inr jv₁) (⊢inr jv₂) ⟨ ⊢`inr {𝓋 = 𝓋₁} r₁ , ⊢`inr {𝓋 = 𝓋₂} r₂ ⟩
  with fp e₁ r[γ₁,γ₂] 𝓋₁ 𝓋₂ jv₁ jv₂ ⟨ r₁ , r₂ ⟩
... | IH rewrite lzero[⨰]< Σ′ >
  | lunit[+][qty]< (⟨ 0 ⟩ +[qty] (Σ′ ⨰ Σ₂)) >
  | lunit[+][qty]< (Σ′ ⨰ Σ₂) >
  | L5 Σ′ Σ₂ = IH
fp (⊢`case e₁ e₃ e₄ x) r[γ₁,γ₂] = {!   !}
fp (⊢`if e₁ e₃ e₄) r[γ₁,γ₂] = {!   !}
fp (⊢`let e₁ e₃) r[γ₁,γ₂] = {!   !}
fp (⊢`λ e) r[γ₁,γ₂] .(ƛ⦂ e₁ ∥ γ₁) .(ƛ⦂ e₂ ∥ γ₂) (⊢λ {ℾ = ℾ₁} x x₁ x₂ x₃ x₄) (⊢λ {ℾ = ℾ₂} x₅ x₆ x₇ x₈ x₉) ⟨ ⊢`λ {γ = γ₁} {e = e₁} , ⊢`λ {γ = γ₂} {e = e₂} ⟩
  = ⟨∃ ↯ , ⟨ {!   !} , (λ x₁₀ x₁₁ v₃ v₄ ε₃ ε₄ x₁₂ → {!   !}) ⟩ ⟩
fp (⊢`app e₁ e₂) r[γ₁,γ₂] = {!   !}
fp {Σ′ = Σ′} (⊢`_pair_ {Σ₁ = Σ₁} {Σ₂ = Σ₂} e₁ e₂) r[γ₁,γ₂] .(𝓋₁₁ pair 𝓋₁₂) .(𝓋₂₁ pair 𝓋₂₂) (⊢pair t₁ t₂) (⊢pair t₃ t₄) ⟨ ⊢`_pair_ {𝓋₁ = 𝓋₁₁} {𝓋₂ = 𝓋₁₂} r₁ r₂ , ⊢`_pair_ {𝓋₁ = 𝓋₂₁} {𝓋₂ = 𝓋₂₂} r₃ r₄ ⟩
  with fp e₁ r[γ₁,γ₂] 𝓋₁₁ 𝓋₂₁ t₁ t₃ ⟨ r₁ , r₃ ⟩
    | fp e₂ r[γ₁,γ₂] 𝓋₁₂ 𝓋₂₂ t₂ t₄ ⟨ r₂ , r₄ ⟩
... | IH₁ | IH₂ rewrite lzero[⨰]< Σ′ >
    | lunit[+][qty]< (⟨ 0 ⟩ +[qty] (Σ′ ⨰ Σ₁)) >
    | lunit[+][qty]< (⟨ 0 ⟩ +[qty] (Σ′ ⨰ Σ₂)) >
    | lunit[+][qty]< (Σ′ ⨰ Σ₁) >
    | lunit[+][qty]< (Σ′ ⨰ Σ₂) >
    | L5 Σ′ Σ₁
    | L5 Σ′ Σ₂ = ⟨ IH₁ , IH₂ ⟩
fp {Σ′ = Σ′} (⊢`fst {Σ = Σ} {Σ₁ = Σ₁} e₁) r[γ₁,γ₂] v₁ v₂ t₁ t₂ ⟨ ⊢`fst r₁ , ⊢`fst r₂ ⟩
  with fp e₁ r[γ₁,γ₂] (v₁ pair _) (v₂ pair _) (⊢pair t₁ _) (⊢pair t₂ _) ⟨ r₁ , r₂ ⟩
... | ⟨ π₃ , π₄ ⟩ rewrite L5 Σ′ Σ₁
    | lunit[+][qty]< (Σ₁ ⨰ Σ′) >
    | ◇[≡] (L4 Σ Σ₁ Σ′) = π₃
fp {Σ′ = Σ′} (⊢`snd {Σ = Σ} {Σ₂ = Σ₂} e₁) r[γ₁,γ₂] v₁ v₂ t₁ t₂ ⟨ ⊢`snd r₁ , ⊢`snd r₂ ⟩
  with fp e₁ r[γ₁,γ₂] (_ pair v₁) (_ pair v₂) (⊢pair _ t₁) (⊢pair _ t₂) ⟨ r₁ , r₂ ⟩
... | ⟨ π₃ , π₄ ⟩  rewrite L5 Σ′ Σ₂
    | lunit[+][qty]< (Σ₂ ⨰ Σ′) >
    | ◇[≡] (L4 Σ Σ₂ Σ′) = π₄

-- Corrolary 1.1.1 (FP for closed terms).

fpc : ∀ {Γ : Γ[ ᴢ ]} {ø : γ[ ᴢ ]} {e : Term ᴢ} {τ : τ ᴢ} {ℾ} → Γ ⊢ e ⦂ τ , zero → ⟨ ø , ø ⟩∈𝒢⟦ zero ː ℾ ⟧ → ⟨ ø ⊢ e , ø ⊢ e ⟩∈ℰ⟦ zero ː (zero ⟨⟨ τ ⟩⟩) ⟧
fpc e₁ e₂ = fp e₁ e₂

∣_-_∣ᴺ : ℕ → ℕ → ℕ
∣ ᴢ - ᴢ ∣ᴺ = ᴢ
∣ ᴢ - ꜱ n ∣ᴺ = ꜱ n
∣ ꜱ m - ᴢ ∣ᴺ = ꜱ m
∣ ꜱ m - ꜱ n ∣ᴺ = ∣ m - n ∣ᴺ

∣_-_|ᴺ≤_ : ℕ → ℕ → Sens → Set
∣ n₁ - n₂ |ᴺ≤ s = ⟨ ∣ n₁ - n₂ ∣ᴺ ⟩ ≤ s
--
-- -- Theorem 1.2 (Sensitivity Type Soundness at Base Types).
--
sound : ∀ {Γ : Γ[ ᴢ ]} {ø : γ[ ᴢ ]} {e s s′ r₁ r₂ r′₁ r′₂} → Γ ⊢ e ⦂ (ƛ⦂ ℝT ⇒[ zero ∔ [ s ] ] ℝT) , zero → ∣ r₁ - r₂ |ᴺ≤ s′ → ø ⊢ e `app (`ℝ r₁) ⇓ 𝓇 r′₁ → ø ⊢ e `app (`ℝ r₂) ⇓ 𝓇 r′₂ → ∣ r′₁ - r′₂ |ᴺ≤ (s × s′)
sound a b c d = {!   !}
