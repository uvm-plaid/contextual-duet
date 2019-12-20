{-# OPTIONS --allow-unsolved-metas #-}
module red-proof where

open import rules public
open import lemmas public
open import logical-relations public

infixl 6 _⊚[≤ᵣ]_
postulate
  fp : ∀ {N} {Γ : Γ[ N ]} {ℾ e τ Σ γ₁ γ₂ Σ′ Σ₀} → ℾ ⊢ γ₁ → ℾ ⊢ γ₂ → Γ , Σ₀ ⊢ e ⦂ τ , Σ → ⟨ γ₁ , γ₂ ⟩∈𝒢⟦ Σ′ ː ℾ ⟧ → ⟨ γ₁ ⊢ e , γ₂ ⊢ e ⟩∈ℰ⟦ Σ ⨰ Σ′ ː (Σ′ ⟨⟨ τ ⟩⟩) ⟧
  _⊚[≤ᵣ]_ : ∀ {m n p : ℝ} →
    m ≤ᵣ n → n ≤ᵣ p
    ---------------
    → m ≤ᵣ p
  -- given two equal length vectors, and the operations:
    -- (1) truncate each, then take the dot product ([vec]⌉ Σ′ ⌈⸢ ⟨ 1 ⟩ ⸣ ⨰ [vec]⌉ Σ ⌈⸢ ⟨ p ⟩ ⸣ ) or,
    -- (2) take the dot product, then truncate the result ([vec]⌉ Σ′ ⨰ Σ ⌈⸢ ⟨ 1 ⟩ ⸣ × p)
    -- both operations also involve potential "scaling" of the constant p by 0 or 1
  truncDotTrichotomy : ∀ {N} (p : Priv) → (Σ′ Σ : Σ[ N ])
    -- the possible outcomes are in three categories:
    -- at least one of the vectors is the constant zero vector, so both operations equal zero
    → ([vec]⌉ Σ′ ⌈⸢ ⟨ 1 ⟩ ⸣ ⨰ [vec]⌉ Σ ⌈⸢ p ⸣ ) ≡ zero ∧ (⌉ Σ′ ⨰ Σ ⌈⸢ ⟨ 1 ⟩ ⸣ × p) ≡ zero
    -- there is at most one dot product "match", i.e. all other elements of the product equal zero
    -- both operations equal the constant p
    ∨ ([vec]⌉ Σ′ ⌈⸢ ⟨ 1 ⟩ ⸣ ⨰ [vec]⌉ Σ ⌈⸢ p ⸣ ) ≡ p ∧ (⌉ Σ′ ⨰ Σ ⌈⸢ ⟨ 1 ⟩ ⸣ × p) ≡ p
    -- there is at least one dot product match
    -- operation (1) equals k·p where 1 ≤ k
    -- operation (2) equals p
    -- this disjunct should have exists k
    ∨ ([vec]⌉ Σ′ ⌈⸢ ⟨ 1 ⟩ ⸣ ⨰ [vec]⌉ Σ ⌈⸢ p ⸣ ) ≡ {- k × -} p {- ∧ one ≤ k -} ∧ (⌉ Σ′ ⨰ Σ ⌈⸢ ⟨ 1 ⟩ ⸣ × p) ≡ p

-- Theorem 1.1.2 (Fundamental Property / (Metric Preservation in Fuzz)).
fp₂ : ∀ {N} {Γ : Γ[ N ]} {ℾ e τ Σ Σ₀ γ₁ γ₂ Σ′} → ℾ ⊢ γ₁ → ℾ ⊢ γ₂
  → Γ , Σ₀ ⊢ₚ e ⦂ τ , Σ
  → ⟨ γ₁ , γ₂ ⟩∈𝒢⟦ Σ′ ː ℾ ⟧
  → ⟨ γ₁ ⊢ e , γ₂ ⊢ e ⟩∈ℰₚ⟦ [vec]⌉ Σ′ ⌈⸢ one ⸣ ⨰ Σ ː (Σ′ ⟨⟨ τ ⟩⟩) ⟧
{-

-- PRIVACY FUNCTION APPLICATION
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
  rewrite ZZ
  with IH′ {v₁ = 𝓋₁} {v₂ = 𝓋₂} {ε₁ = (typeSafety e₂ ⊢e₁₂)} {ε₂ = (typeSafety e₂ ⊢e₂₂)} {s′ = Σ₂ ⨰ Σ′}
            {Σ₀ = Σ′} (L3′ ⊢γ₁′ ⊢γ₂′ r[γ₁,γ₂]) IH₂ v₁ v₂ r₁ r₂ ε₁
            ε₂ ⟨ ⊢e₁₂′ ,  ⊢e₂₂′ ⟩ pr₁ pr₂
... | IH′′ rewrite lzero[⨰]< Σ′ >
    | L0-3 (([vec]⌉ Σ′ ⌈⸢ ⟨ 1 ⟩ ⸣ ⨰ Σ₁) +[qty] ⟨ 0 ⟩)
    | L-distrib-vec [vec]⌉ Σ′ ⌈⸢ ⟨ 1 ⟩ ⸣ Σ₁ [vec]⌉ Σ₂ ⌈⸢ p ⸣ =
      let n = (𝑒^ᴿ (p2r (((mapⱽ (λ x → ⌉ x ⌈⸢ ⟨ 1 ⟩ ⸣) Σ′ ⨰ Σ₁) +[qty] ⟨ 0 ⟩) +[qty] ((⌉ Σ₂ ⨰ Σ′ ⌈⸢ ⟨ 1 ⟩ ⸣) ×[qty] p))) × r₂)
          p′ = (𝑒^ᴿ (p2r ((([vec]⌉ Σ′ ⌈⸢ ⟨ 1 ⟩ ⸣ ⨰ Σ₁) +[qty] ⟨ 0 ⟩) +[qty] (⌉ Σ₂ ⨰ Σ′ ⌈⸢ ⟨ 1 ⟩ ⸣ ×[qty] p))) × r₂)
      in _⊚[≤ᵣ]_ {m = r₁} {n = n} {p = p′} IH′′ (LPAPP {r = r₂} {p = p} Σ₁ Σ₂ Σ′)

-}
{-
-- PRIVACY CASE LEFT-LEFT
fp₂ {Σ₀ = Σ₀} {Σ′ = Σ′} ⊢γ₁ ⊢γ₂ (⊢`pcase {Σ₁₁ = Σ₁₁} {Σ₁₂ = Σ₁₂} {Σ₂ = Σ₂} e₁ e₂ e₃ τε) r[γ₁,γ₂]
  v₁ v₂ r₁ r₂ ε₁ ε₂
  ⟨ ⊢`pcase/l {𝓋₁ = 𝓋₁₁} re₁ re₂ , ⊢`pcase/l {𝓋₁ = 𝓋₁₂} re₃ re₄ ⟩
  pr₁ pr₂ with typeSafety {Σ′ = Σ′} e₁ re₁
    | typeSafety {Σ′ = Σ′} e₁ re₃
    | fp ⊢γ₁ ⊢γ₂ e₁ r[γ₁,γ₂] (inl 𝓋₁₁) (inl 𝓋₁₂) (typeSafety {Σ′ = Σ′} e₁ re₁) (typeSafety {Σ′ = Σ′} e₁ re₃) ⟨ re₁ , re₃ ⟩
... | ⊢inl ⊢v₁ | ⊢inl ⊢v₂ | IH₁ with fp₂ (⊢s ⊢v₁ ⊢γ₁) (⊢s ⊢v₂ ⊢γ₂) e₂ ⟨∃ ⊢v₁ , ⟨∃ ⊢v₂ , ⟨ IH₁ , r[γ₁,γ₂] ⟩ ⟩ ⟩ v₁ v₂ r₁ r₂ (typeSafety₂ e₂ re₂) (typeSafety₂ e₂ re₄) ⟨ re₂ , re₄ ⟩ pr₁ pr₂
... | IH₂ rewrite L0-3 (Σ′ ⨰ Σ₁₁) = subsumption₂ τε IH₂
-}

-- PRIVACY CASE LEFT-RIGHT
{-
fp₂ {Σ₀ = Σ₀} {Σ′ = Σ′}
  ⊢γ₁ ⊢γ₂
  (⊢`pcase e₁ e₂ e₃ τε) r[γ₁,γ₂]
  𝓋₁ 𝓋₂ ⊢𝓋₁ ⊢𝓋₂
  ⟨ ⊢`pcase/l {𝓋₁ = 𝓋₁₁} re₁ re₂ , ⊢`pcase/r {𝓋₁ = 𝓋₁₂} re₃ re₄ ⟩
  v r₁ r₂
  ⊢v
  ∈sup𝓋₁
  ∈sup𝓋₂
  pr₁ pr₂
  with  fp ⊢γ₁ ⊢γ₂ e₁ r[γ₁,γ₂] (inl 𝓋₁₁) (inr 𝓋₁₂) (typeSafety {Σ′ = Σ′} e₁ re₁) (typeSafety {Σ′ = Σ′} e₁ re₃) ⟨ re₁ , re₃ ⟩
... | IH with typeSafety {Σ′ = Σ′} e₁ re₁ | typeSafety {Σ′ = Σ′} e₁ re₃
… | ⊢inl X | ⊢inr Y = {! IH !}


-- fp₂ {Σ₀ = Σ₀} {Σ′ = Σ′} ⊢γ₁ ⊢γ₂ (⊢`pcase e₁ e₂ e₃ τε) r[γ₁,γ₂] v₁ v₂ r₁ r₂ ε₁ ε₂ ⟨ ⊢`pcase/r x π₃ , ⊢`pcase/l x₁ π₄ ⟩ pr₁ pr₂ = {!   !}
-- fp₂ {Σ₀ = Σ₀} {Σ′ = Σ′} ⊢γ₁ ⊢γ₂ (⊢`pcase e₁ e₂ e₃ τε) r[γ₁,γ₂] v₁ v₂ r₁ r₂ ε₁ ε₂ ⟨ ⊢`pcase/r x π₃ , ⊢`pcase/r x₁ π₄ ⟩ pr₁ pr₂ = {!   !}

-- RETURN
fp₂ {Σ₀ = Σ₀} {Σ′ = Σ′}
  ⊢γ₁ ⊢γ₂
  (⊢`return e) r[γ₁,γ₂]
  𝓋₁ 𝓋₂ ⊢𝓋₁ ⊢𝓋₂
  ⟨ ⊢`return {𝓋₁ = v₁} e₁⇓ , ⊢`return {𝓋₁ = v₂} e₂⇓ ⟩
  v r₁ r₂
  ⊢v
  ∈sup𝓋₁
  ∈sup𝓋₂
  pr₁ pr₂
  with fp ⊢γ₁ ⊢γ₂ e r[γ₁,γ₂] v₁ v₂ (typeSafety {Σ′ = Σ′} e e₁⇓) (typeSafety {Σ′ = Σ′} e e₂⇓) ⟨ e₁⇓ , e₂⇓ ⟩
… | IH = {! !}

-}

-- BIND
fp₂ {Σ₀ = Σ₀} {Σ′ = Σ′}
  ⊢γ₁ ⊢γ₂
  (⊢`bind {Σ₁ = Σ₁} {Σ₂ = Σ₂} e₁ e₂) r[γ₁,γ₂]
  𝓋₁ 𝓋₂ ⊢𝓋₁ ⊢𝓋₂
  ⟨ ⊢`bind {𝓋₁ = 𝓋₁₁} ε₁ F₁ , ⊢`bind {𝓋₁ = 𝓋₁₂} ε₂ F₂ ⟩  -- v r₁ r₂ ∈sup𝓋₁ ∈sup𝓋₂ pr₁ pr₂
  with typeSafety₂ {Σ′ = Σ′} e₁ ε₁ | typeSafety₂ {Σ′ = Σ′} e₁ ε₂
... | ⊢v₁′ | ⊢v₂′
  with fp₂ ⊢γ₁ ⊢γ₂ e₁ r[γ₁,γ₂] 𝓋₁₁ 𝓋₁₂ ⊢v₁′ ⊢v₂′ ⟨ ε₁ , ε₂ ⟩
... | IH₁
  with sequentialComposition Σ′ 𝓋₁₁ 𝓋₁₂ F₁ F₂ Σ₁ Σ₂
    IH₁ λ x s₁ s₂ ⊢x ⊢ᴰdπ₁₁ ⊢ᴰdπ₁₂
    → fp₂ (⊢s ⊢x ⊢γ₁) (⊢s ⊢x ⊢γ₂) e₂ _ (dπ₁ (F₁ x s₁)) (dπ₁ (F₂ x s₂)) ⊢ᴰdπ₁₁ ⊢ᴰdπ₁₂
    ⟨ (dπ₂ (F₁ x s₁)) , (dπ₂ (F₂ x s₂)) ⟩
... | sC = sC

--   pr₁ pr₂ with typeSafety₂ {Σ′ = Σ′} e₁ ε₁ | typeSafety₂ {Σ′ = Σ′} e₁ ε₂
-- ... | ⊢v₁′ | ⊢v₂′ with fp₂ ⊢γ₁ ⊢γ₂ e₁ r[γ₁,γ₂] 𝓋₁₁ 𝓋₁₂ ⊢v₁′ ⊢v₂′ ⟨ ε₁ , ε₂ ⟩
-- ... | IH₁ = {!!}
-- with fp₂ _ _ e₂ _ 𝓋₁ 𝓋₂ {!⊢𝓋₁   !} _ _  v r₁ r₂ {! ⊢v  !} ∈sup𝓋₁ ∈sup𝓋₂ pr₁ pr₂
-- ... | IH₂ = {!   !}

fp₂ _ = {!   !}

{-

General outline:
- intro (summary of problem, contributions and background)

- introduce key ideas, proofs and techniques

- combine things from (2) to complete the final proof and relate results back to examples shown in background section

Notes:

CORE LANGUAGE FORMALIZATION
  - substitution: predecessor (why?), pluck etc
  - modeling sensitivity/privacy as a "toppable" number
  - modeling sensitivity/privacy arithmetic
  - truncation operation
  - DeBruijn Indices: environment
  - probability monad

  - assumption of well-typing in the logical relation
  - substitution lemmas
  - formalizing: sensitivity/privacy environments, types & type environments, **value** type environments
  - values, value environments
  - mutual: pterms & sterms
  - substitution: substΣ/Σ, substΣ/Σₚ, substΣ/τ, cut
  - substitution of one variable: substSx/τ<_>
  - weakening: wkΣ, ⇧ˢ<_>, ⇧ᵗ<_>
  - instantiation: instantiateΣ/Σ, Σ ⟨⟨ τ ⟩⟩

CORE LANGUAGE RULES
  - mutual: typing judgements for sensitivity and privacy terms
  - typing judgements for values and value environments
  - ground truth dynamic semantics
  - probabilistic semantics

LOGICAL RELATIONS
  - describe each one?

SENSITIVITY LANGUAGE FP PROOF: By induction on language terms

PRIVACY LANGUAGE FP PROOF: By induction on language terms

-}

{-

INTRO

Problem Statement
​
  Implementing a language for differential privacy where researchers/analysts can build new differential privacy techniques into their programs.

​  To solve the above problem, the PLAID lab at UVM created the programming language: Duet.
  This is a general purpose programming language with the rules or differential privacy built into the type system.
  It is therefore very important that the type system correctly follows the fundamental properties and promises of differential privacy.
  We would like to prove the correctness of Duet’s type system. However, writing a proof in english/standard math can be error prone, so we plan to use
  the proof assistant Agda to model and write our proof of correctness for Duet’s type system.

  ​	The process for proving correctness of Duet’s type system is as follows:
  (1) formalize the syntax, typing judgements, and logical relations of the Duet language
  (2) formalize the fundamental property of metric preservation in Agda (3) prove the fundamental property (to the best of our ability)

Novel Contributions

  - Duet Language Contributions
  - Duet Mechanization Contributions

  ​So far the progress made has been making a proof for the correctness of Duet 1 and a proof for the correctness of Duet 2 following the above process.
  The proof for Duet 1 found an issue with the semantics for the treatment of case splitting expressions as well as generally finding correctness for
  most of the Duet type system. The proof for Duet 2 has to consider more complexity in the type system,
  as Duet 2 now has the added features of contextual types and delayed sensitivity and privacy environments.

Background

  - Language-based approach to DP
  - Related Work


-}

{-

OTHER Unique Mechanization Challenges

  - Unification: DeBruijn Indices
  - Vector Arithmetic

-}
