module contextual where

-- infix 4 _≡_
--
-- data _≡_ {A : Set} (x : A) : A → Set where
--   ↯ : x ≡ x
--
-- {-# BUILTIN EQUALITY _≡_ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

data 𝔹 : Set where
  True : 𝔹
  False : 𝔹

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

open import Agda.Builtin.Float

ℝ : Set
ℝ = Float

_ : ℝ
_ = primNatToFloat 2

_ : ℝ
_ = 2.7

--
-- postulate ℝ : Set
-- {-# BUILTIN FLOAT ℝ #-}

_ : ℕ
_ = 3 + 2

-- xx :
-- primNatToFloat

𝕏 : Set
𝕏 = ℕ


infix 9 𝕤_
-- sensitivity
data 𝕊 : Set where
  ∞  : 𝕊
  𝕤_ : ℝ → 𝕊

infix 7 _+̂_

_+̂_ : 𝕊 → 𝕊 → 𝕊
∞ +̂ _ = ∞
_ +̂ ∞ = ∞
𝕤 x +̂ 𝕤 x₁ = 𝕤 (primFloatPlus x x₁)

infix 8 _×̂_

_×̂_ : 𝕊 → 𝕊 → 𝕊
𝕤 0.0 ×̂ _ = 𝕤 0.0
_ ×̂ 𝕤 0.0 = 𝕤 0.0
∞ ×̂ _ = ∞
_ ×̂ ∞ = ∞
𝕤 x ×̂ 𝕤 x₁ = 𝕤 (primFloatTimes x x₁)

-- sensitivity environment
infixl 5  _,_⦂_

data Σ : Set where
  ∅     : Σ
  _,_⦂_ : Σ → 𝕏 → 𝕊 → Σ

infix 5 ƛ_⦂_⇒[_]_
infix 6 _∥_⊗_∥_
infix 6 _∥_⊕_∥_

-- types
data τ : Set where
  ƛ_⦂_⇒[_]_ : 𝕏 → τ → Σ → τ → τ
  _∥_⊗_∥_ : τ → Σ → Σ → τ → τ
  _∥_⊕_∥_ : τ → Σ → Σ → τ → τ
  unit : τ
  ℝT : τ
  𝔹T : τ

-- type environment
data Γ : Set where
  ∅     : Γ
  _,_⦂_ : Γ → 𝕏 → τ → Γ


infix 9 ℝ_
infix 9 𝔹_
infix 7 _⊞_
infix 8 _·_
infix 6 _≤_
infix 9 `_
infix 5 ƛ_⦂_⇒_
infix 7 _⊚_
infix 6 inl_⦂_
infix 6 inr_⦂_
infix 6 case_of_⦂_∥_⦂_
infix 6 fst_
infix 6 snd_
infix 4 _::_
infix 6 if_∥_∥_
infix 6 _←_∥_


data Term : Set where
  -- real numbers
  ℝ_ : ℝ → Term
  _⊞_ : Term → Term → Term
  _·_ : Term → Term → Term
  _≤_ : Term → Term → Term
  -- variables, functions, application
  `_ : 𝕏 → Term
  ƛ_⦂_⇒_ : 𝕏 → τ → Term → Term
  _⊚_ : Term → Term
  -- unit
  tt : Term
  -- sums
  inl_⦂_ : τ → Term → Term
  inr_⦂_ : τ → Term → Term
  case_of_⦂_∥_⦂_ : Term → 𝕏 → Term → 𝕏 → Term → Term
  -- products
  _〈_,_〉_ : Term → Term → Term
  fst_ : Term → Term
  snd_ : Term → Term
  -- ascription
  _::_ : Term → τ → Term
  -- booleans
  𝔹_ : 𝔹 → Term
  if_∥_∥_ : Term → Term → Term → Term
  -- let
  _←_∥_ : 𝕏 → Term → Term

infix 9 inl_
infix 9 inr_
infix 9 _〈_,_〉_
infix 5 ƛ_⦂_∥_

-- values
mutual
  data 𝓋 : Set where
    r : 𝓋
    b : 𝓋
    tt : 𝓋
    inl_ : 𝓋 → 𝓋
    inr_ : 𝓋 → 𝓋
    _〈_,_〉_ : 𝓋 → 𝓋 → 𝓋
    ƛ_⦂_∥_ : 𝕏 → Term → γ → 𝓋

  -- value environment
  data γ : Set where
    ∅     : γ
    _,_⦂_ : γ → 𝕏 → 𝓋 → γ
