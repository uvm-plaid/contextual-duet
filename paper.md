# General outline:

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
  - substitution: `substΣ/Σ`, `substΣ/Σₚ`, `substΣ/τ`, `cut`
  - substitution of one variable: `substSx/τ<_>`
  - weakening: `wkΣ`, `⇧ˢ<_>`, `⇧ᵗ<_>`
  - instantiation: `instantiateΣ/Σ, Σ ⟨⟨ τ ⟩⟩`

CORE LANGUAGE RULES
  - mutual: typing judgements for sensitivity and privacy terms
  - typing judgements for values and value environments
  - ground truth dynamic semantics
  - probabilistic semantics

LOGICAL RELATIONS
  - describe each one?

SENSITIVITY LANGUAGE FP PROOF: By induction on language terms

PRIVACY LANGUAGE FP PROOF: By induction on language terms



INTRO

Problem Statement
​
  Implementing a language for differential privacy where researchers/analysts can build new differential privacy techniques into their programs.

  To solve the above problem, the PLAID lab at UVM created the programming language: Duet.
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

# Random Latex Stuff

$$
\begin{align*}
fp :\: &\forall\: \lbrace N\rbrace\:\lbrace Γ : Γ[ N ]\rbrace \lbrace ℾ \: e \: τ \: Σ \: γ₁ \: γ₂ \: Σ′ \: Σ₀\rbrace 
 \\& → ℾ ⊢ γ₁ → ℾ ⊢ γ₂ → Γ , Σ₀ ⊢ e ⦂ τ , Σ 
 \\& → \langle γ₁ , γ₂ \rangle\in\cal{G}⟦ Σ′ \:ː\: ℾ ⟧ 
 \\& → ⟨ γ₁ ⊢ e , γ₂ ⊢ e ⟩∈\cal{E}⟦\: Σ \dot \times Σ' \: ː \: Σ' \langle\langle τ \rangle\rangle \:⟧

\\fp_2 :\: &\forall\: \lbrace N\rbrace\:\lbrace Γ : Γ[ N ]\rbrace \lbrace ℾ \: e \: τ \: Σ \: γ₁ \: γ₂ \: Σ′ \: Σ₀\rbrace 
 \\& → ℾ ⊢ γ₁ → ℾ ⊢ γ₂ → Γ , Σ₀ ⊢_p e ⦂ τ , Σ 
 \\& → ⟨ γ₁ , γ₂ ⟩∈\cal{G}⟦ Σ′ ː ℾ ⟧
 \\& → ⟨ γ₁ ⊢ e , γ₂ ⊢ e ⟩∈\cal{E}_p⟦ [vec]⌉ Σ′ ⌈⸢ one ⸣ ⨰ Σ ː (Σ′ ⟨⟨ τ ⟩⟩) ⟧

\end{align*}
$$



```haskell
mutual
  data PTerm : ℕ → Set where
    _`papp_ : ∀ {N} → Term N → Term N → PTerm N

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

```



```haskell
pred : ∀ (N : ℕ) → idx N → ℕ
pred (ꜱ N) ᴢ = N
pred (ꜱ N) (ꜱ ι) = ꜱ (pred N ι)
```



```haskell
pluck : ∀ {ℓ} {A : Set ℓ} {N} (ι : idx N) → ⟬ A ⟭[ N ] → ⟬ A ⟭[ pred N ι ]
substΣ/Σ : ∀ {N} → (ι : idx N) → Σ[ pred N ι ] → Σ[ N ] → Σ[ pred N ι ]
substΣ/ΣP : ∀ {N} → (ι : idx N) → Σ[ pred N ι ] → Σₚ[ N ] → Σₚ[ pred N ι ]
wkΣ : ∀ {N} → (ι : idx N) → Σ[ pred N ι ] → Σ[ N ]
substΣ/τ : ∀ {N} → (ι : idx N) → Σ[ pred N ι ] → τ N → τ (pred N ι)
cut : ∀ {N} → Σ[ N ] → τ (ꜱ N) → τ N
instantiateΣ/Σ : ∀ {N N′} → Σ[ N ] → Σ[ N′ + N ] → qty ℕ ∧ Σ[ N′ ]
instantiateΣ/ΣP : ∀ {N N′} → Σ[ N ] → Σ[ N′ + N ] → qty ℕ ∧ Σ[ N′ ]
instantiateΣ/τ : ∀ {N N′} → Σ[ N ] → τ (N′ + N) → τ N′
⇧ˢ′<_> : ∀ {N} → idx N → Σ[ N ] → Σ[ ꜱ N ]
⇧ˢ<_> : ∀ {N} → idx (ꜱ N) → Σ[ N ] → Σ[ ꜱ N ]
⇧ᵗ<_> : ∀ {N} → idx (ꜱ N) → τ N → τ (ꜱ N)
⇧ᵗ : ∀ {N} → τ N → τ (ꜱ N)
⇧ˢ : ∀ {N} → Σ[ N ] → Σ[ (ꜱ N) ]
_⟨⟨_⟩⟩ : ∀ {N} → Σ[ N ] → τ N → τ ᴢ
substSx/τ<_> : ∀ {N} (ι : idx N) → Sens → τ N → τ (pred N ι)
```









# Write Here





