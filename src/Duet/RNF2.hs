module Duet.RNF2 where

import Duet.UVMHS

-- e ∈ RNF ⩴ ⊥ | ⊤ | r | α̇
data RNF = 
    ConstantRNF (AddBT 𝔻)
  | SymRNF RNFMaxs
  deriving (Eq,Ord,Show)

-- α̇ ∈ RNFMaxs ⩴ c ⊔̇ α
-- α ∈ ℘(RNFMins)
data RNFMaxs = RNFMaxs
  { rnfMaxsConstant ∷ AddBot 𝔻
  , rnfMaxsSymbolic ∷ 𝑃 RNFMins -- (at least one inside)
  }
  deriving (Eq,Ord,Show)

-- β̇ ∈ RNFMins ⩴ c ⊓̇ β
-- β ∈ ℘(RNFSums)
data RNFMins = RNFMins
  { rnfMinsConstant ∷ AddTop 𝔻
  , rnfMinsSymbolic ∷ 𝑃 RNFSums -- (at least one inside)
  }
  deriving (Eq,Ord,Show)

-- γ̇ ∈ RNFSums ⩴ c +̇ γ
-- γ ∈ RNFProds ⇰ 𝔻 ᐪ
data RNFSums = RNFSums
  { rnfSumsConstant ∷ AddBot 𝔻
  , rnfSumsSymbolic ∷ RNFProds ⇰ AddTop 𝔻 -- (at least one inside)
  }
  deriving (Eq,Ord,Show)

-- δ̇ ∈ RNFProds ⩴ δ
-- δ ∈ RNFAtom ⇰ 𝔻
data RNFProds = RNFProds
  { rnfProdsSymbolic ∷ RNFAtom ⇰ 𝔻 -- (at least one inside)
  }
  deriving (Eq,Ord,Show)

-- ε ∈ RNFAtom
data RNFAtom =
    VarRA 𝕏
  | PowRA 𝔻 RNFSums -- (at least two in sum)
  | LogRA RNFSums -- (at least two in sum)
  | EfnRA RNFSums -- (at least two in sum)
  deriving (Eq,Ord,Show)

-------------
-- LITERAL --
-------------

litRNF ∷ 𝔻 → RNF
litRNF d 
  | d ≡ 0.0 = ConstantRNF BotBT
  | otherwise = ConstantRNF $ AddBT d

--------------
-- VARIABLE --
--------------

varRNF ∷ 𝕏 → RNF
varRNF x = 
  -- 0 ⊔̇ (⊤ ⊓̇ (0 +̇ (1 ×̇ x¹)))
  SymRNF 
  $ RNFMaxs Bot $ single 
  $ RNFMins Top $ single 
  $ RNFSums Bot $ single $ flip (:*) (AddTop 1.0)
  $ RNFProds $ single $ flip (:*) 1.0
  $ VarRA x

---------
-- MAX --
---------

-- ┌─────┐
-- │e ⊔̃ e│
-- └─────┘
maxRNF ∷ RNF → RNF → RNF
maxRNF e₁ e₂ = case (e₁,e₂) of
  -- ⊤ ⊔̃ e ≜ ⊤
  (ConstantRNF TopBT,_) → ConstantRNF TopBT
  -- e ⊔̃ ⊤ ≜ ⊤
  (_,ConstantRNF TopBT) → ConstantRNF TopBT
  -- ⊥ ⊔̃ e ≜ e
  (ConstantRNF BotBT,_) → e₂
  -- e ⊔̃ ⊥ ≜ e
  (_,ConstantRNF BotBT) → e₁
  -- c₁ ⊔̃ c₂ ≜ c₂ ⊔ c₂
  (ConstantRNF (AddBT c₁),ConstantRNF (AddBT c₂)) → ConstantRNF $ AddBT $ c₁ ⊔ c₂
  -- c₁ ⊔̃ (c₂ ⊔̇ α₂) ≜ (c₁ ⊔ c₂) ⊔̇ α₂
  (ConstantRNF (AddBT c₁),SymRNF (RNFMaxs c₂ α₂)) → SymRNF $ RNFMaxs (AddBot c₁ ⊔ c₂) α₂
  -- (c₁ ⊔̇ α₁) ⊔̃ c₂ ≜ (c₁ ⊔ c₂) ⊔̇ α₁
  (SymRNF (RNFMaxs c₁ α₁),ConstantRNF (AddBT c₂)) → SymRNF $ RNFMaxs (c₁ ⊔ AddBot c₂) α₁
  -- (c₁ ⊔̇ α₁) ⊔̃ (c₂ ⊔̇ α₂) ≜ (c₁ ⊔ c₂) ⊔̇ (α₁ ∪ α₂)
  (SymRNF (RNFMaxs c₁ α₁), SymRNF (RNFMaxs c₂ α₂)) → SymRNF $ RNFMaxs (c₁ ⊔ c₂) (α₁ ∪ α₂)

---------
-- MIN --
---------

-- ┌─────┐
-- │c ⊓̃ α│
-- └─────┘
minRNFMaxsConstant ∷ 𝔻 → 𝑃 RNFMins → 𝑃 RNFMins
minRNFMaxsConstant c α =
  -- c ⊓̃ α ≜ { c ⊓ (c′ ⊓̇ β) | c′ ⊓̇ β ∈ α }
  --       = { (c ⊓ c′) ⊓̇ β | c′ ⊓̇ β ∈ α }
  pow $ do
    RNFMins c' β ← iter α
    return $ RNFMins (AddTop c ⊓ c') β

-- ┌─────┐
-- │α ⊓̃ α│
-- └─────┘
minRNFMaxs ∷ 𝑃 RNFMins → 𝑃 RNFMins → 𝑃 RNFMins
minRNFMaxs α₁ α₂ = 
  -- α₁ ⊓̃ α₂ ≜ { (c₁ ⊓̇ β₁) ⊓ (c₂ ⊓̇ β₂) | c₁ ⊓̇ β₁ ∈ α₁ , c₂ ⊓̇ β₂ ∈ α₂ }
  --         = { (c₁ ⊓ c₂) ⊓̇ (β₁ ∪ β₂) | c₁ ⊓̇ β₁ ∈ α₁ , c₂ ⊓̇ β₂ ∈ α₂ } 
  pow $ do
    RNFMins c₁ β₁ ← iter α₁
    RNFMins c₂ β₂ ← iter α₂
    return $ RNFMins (c₁ ⊓ c₂) (β₁ ∪ β₂)

-- ┌─────┐
-- │e ⊓̃ e│
-- └─────┘
minRNF ∷ RNF → RNF → RNF
minRNF e₁ e₂ = case (e₁,e₂) of
  -- ⊥ ⊓̃ e ≜ ⊥
  (ConstantRNF BotBT,_) → ConstantRNF BotBT
  -- e ⊓̃ ⊥ ≜ ⊥
  (_,ConstantRNF BotBT) → ConstantRNF BotBT
  -- ⊤ ⊓̃ e ≜ e
  (ConstantRNF TopBT,_) → e₂
  -- e ⊓̃ ⊤ ≜ e
  (_,ConstantRNF TopBT) → e₁
  -- c₁ ⊓̃ c₂ ≜ c₁ ⊓ c₂
  (ConstantRNF (AddBT c₁),ConstantRNF (AddBT c₂)) → ConstantRNF $ AddBT $ c₁ ⊓ c₂
  -- c₁ ⊓̃ (c₂ ⊔̇ α₂) ≜ (c₁ ⊓ c₂) ⊔̇ (c₁ ⊓̃ α₂)
  (ConstantRNF (AddBT c₁),SymRNF (RNFMaxs c₂ α₂)) → SymRNF $ RNFMaxs (AddBot c₁ ⊓ c₂) $ minRNFMaxsConstant c₁ α₂
  -- (c₁ ⊔̇ α₁) ⊓̃ c₂ ≜ (c₁ ⊓ c₂) ⊔̇ (c₂ ⊓̃ α₁)
  (SymRNF (RNFMaxs c₁ α₁),ConstantRNF (AddBT c₂)) → SymRNF $ RNFMaxs (c₁ ⊓ AddBot c₂) $ minRNFMaxsConstant c₂ α₁
  -- (c₁ ⊔̇ α₁) ⊓̃ (c₂ ⊔̇ α₂) ≜ (c₁ ⊓ c₂) ⊔̇ [(c₁ ⊓̃ α₂) ∪ (c₂ ⊓̃ α₁) ∪ (α₁ ⊓̃ α₂)]
  (SymRNF (RNFMaxs c₁ α₁),SymRNF (RNFMaxs c₂ α₂)) →  SymRNF $ RNFMaxs (c₁ ⊓ c₂) $ concat
    [ flip (elimAddBot pø) c₁ $ \ c₁' → minRNFMaxsConstant c₁' α₂
    , flip (elimAddBot pø) c₂ $ \ c₂' → minRNFMaxsConstant c₂' α₁
    , minRNFMaxs α₁ α₂ 
    ]

----------
-- PLUS --
----------

-- ┌─────┐
-- │c +̃ α│
-- └─────┘
sumRNFMaxsConstant ∷ 𝔻 → 𝑃 RNFMins → 𝑃 RNFMins
sumRNFMaxsConstant c α = 
  -- c +̃ α ≜ { c + (c′ ⊓̇ β) | c′ ⊓̇ β ∈ α }
  --       = { (c + c′) ⊓̇ (c +̃ β) | c′ ⊓̇ β ∈ α }
  pow $ do
    RNFMins c' β ← iter α
    return $ RNFMins (AddTop c + c') $ sumRNFMinsConstant c β

-- ┌─────┐
-- │c +̃ β│
-- └─────┘
sumRNFMinsConstant ∷ 𝔻 → 𝑃 RNFSums → 𝑃 RNFSums
sumRNFMinsConstant c β = 
  -- c +̃ β ≜ { c + (c′ +̇ γ) | c′ +̇ γ ∈ β }
  --       = { (c + c′) +̇ γ | c′ +̇ γ ∈ β }
  pow $ do
    RNFSums c' γ ← iter β
    return $ RNFSums (AddBot c + c') γ

-- ┌─────┐
-- │α +̃ α│
-- └─────┘
sumRNFMaxs ∷ 𝑃 RNFMins → 𝑃 RNFMins → 𝑃 RNFMins
sumRNFMaxs α₁ α₂ = 
  -- α₁ +̃ α₂ ≜ { (c₁ ⊓̇ β₁) + (c₂ ⊓̇ β₂) | c₁ ⊓̇ β₁ ∈ α₂ , c₂ ⊓̇ β₂ ∈ α₂ }
  --         ≜ { (c₁ + c₂) ⊓ (c₁ + β₁) ⊓ (c₂ + β₂) ⊓ (β₁ + β₂) | c₁ ⊓̇ β₁ ∈ α₂ , c₂ ⊓̇ β₂ ∈ α₂ }
  --         ≜ { (c₁ + c₂) ⊓̇ [(c₁ +̃ β₁) ∪ (c₂ +̃ β₂) ∪ (β₁ +̃ β₂)] | c₁ ⊓̇ β₁ ∈ α₂ , c₂ ⊓̇ β₂ ∈ α₂ }
  pow $ do
    RNFMins c₁ β₁ ← iter α₁
    RNFMins c₂ β₂ ← iter α₂
    return $ RNFMins (c₁ + c₂) $ concat
      [ flip (elimAddTop pø) c₁ $ \ c₁' → sumRNFMinsConstant c₁' β₂
      , flip (elimAddTop pø) c₂ $ \ c₂' → sumRNFMinsConstant c₂' β₁
      , sumRNFMins β₁ β₂
      ]

-- ┌─────┐
-- │β +̃ β│
-- └─────┘
sumRNFMins ∷ 𝑃 RNFSums → 𝑃 RNFSums → 𝑃 RNFSums
sumRNFMins β₁ β₂ =
  -- β₁ +̃ β₂ ≜ { (c₁ +̇ γ₁) + (c₂ +̇ γ₂) | c₁ +̇ γ₁ ∈ β₁ , c₂ +̇ γ₂ ∈ β₂ }
  --         = { (c₁ + c₂) +̇ (γ₁ + γ₂) | c₁ +̇ γ₁ ∈ β₁ , c₂ +̇ γ₂ ∈ β₂ }
  pow $ do
    RNFSums c₁ γ₁ ← iter β₁
    RNFSums c₂ γ₂ ← iter β₂
    return $ RNFSums (c₁ + c₂) (γ₁ + γ₂)

-- ┌─────┐
-- │e +̃ e│
-- └─────┘
sumRNF ∷ RNF → RNF → RNF
sumRNF e₁ e₂ = case (e₁,e₂) of
  -- ⊤ +̃ e ≜ ⊤
  (ConstantRNF TopBT,_) → ConstantRNF TopBT
  -- e +̃ ⊤ ≜ ⊤
  (_,ConstantRNF TopBT) → ConstantRNF TopBT
  -- ⊥ +̃ e ≜ e
  (ConstantRNF BotBT,_) → e₂
  -- e +̃ ⊥ ≜ e
  (_,ConstantRNF BotBT) → e₁
  -- c₁ +̃ c₂ ≜ c₁ + c₂
  (ConstantRNF (AddBT c₁),ConstantRNF (AddBT c₂)) → ConstantRNF $ AddBT $ c₁ + c₂
  -- c₁ +̃ (c₂ ⊔̇ α₂) ≜ (c₁ + c₂) ⊔̇ (c₁ +̃ α₂)
  (ConstantRNF (AddBT c₁),SymRNF (RNFMaxs c₂ α₂)) → SymRNF $ RNFMaxs (AddBot c₁ + c₂) $ sumRNFMaxsConstant c₁ α₂
  -- (c₁ ⊔̇ α₁) +̃ c₂ ≜ (c₁ + c₂) ⊔̇ (c₂ +̃ α₁)
  (SymRNF (RNFMaxs c₁ α₁),ConstantRNF (AddBT c₂)) → SymRNF $ RNFMaxs (c₁ + AddBot c₂) $ sumRNFMaxsConstant c₂ α₁
  -- (c₁ ⊔̇ α₁) +̃ (c₂ ⊔̇ α₂) ≜ (c₁ + c₂) ⊔̇ [(c₁ +̃ α₂) ∪ (c₂ +̃ α₁) ∪ (α₁ +̃ α₂)]
  (SymRNF (RNFMaxs c₁ α₁),SymRNF (RNFMaxs c₂ α₂)) → SymRNF $ RNFMaxs (c₁ + c₂) $ concat
    [ flip (elimAddBot pø) c₁ $ \ c₁' → sumRNFMaxsConstant c₁' α₂
    , flip (elimAddBot pø) c₂ $ \ c₂' → sumRNFMaxsConstant c₂' α₁
    , sumRNFMaxs α₁ α₂ 
    ]

-----------
-- TIMES --
-----------

-- ┌─────┐
-- │⊤ ×̃ α│
-- └─────┘
prodRNFMaxsTop ∷ 𝑃 RNFMins → AddTop (𝑃 RNFMins)
prodRNFMaxsTop α = 
  -- ⊤ ×̃ α ≜ { ⊤ × (c′ ⊓̇ β) | c′ ⊓̇ β ∈ α }
  --       = { ⊤ ⊓̇ (⊤ ×̃ β) | c′ ⊓̇ β ∈ α }
  map pow $ mapM id $ do
    RNFMins _ β ← iter α
    return $ RNFMins Top ^$ prodRNFMinsTop β

-- ┌─────┐
-- │⊤ ×̃ β│
-- └─────┘
prodRNFMinsTop ∷ 𝑃 RNFSums → AddTop (𝑃 RNFSums)
prodRNFMinsTop β = 
  -- ⊤ ×̃ β ≜ { ⊤ ×̃ (c′ +̇ γ) | c′ +̇ γ ∈ β }
  --       = { (⊤ × c′) +̇ (⊤ ×̃ γ) | c′ +̇ γ ∈ β }
  map pow $ mapM id $ do
     RNFSums c γ ← iter β
     return $ case c of
       -- ⊥ +̇ (⊤ ×̃ γ)
       Bot → AddTop $ RNFSums Bot $ prodRNFSumsTop γ
       -- ⊤
       AddBot _ → Top

-- ┌─────┐
-- │⊤ ×̃ γ│
-- └─────┘
prodRNFSumsTop ∷ RNFProds ⇰ AddTop 𝔻 → RNFProds ⇰ AddTop 𝔻
prodRNFSumsTop γ = 
  -- ⊤ ×̃ γ ≜ { ⊤ ×̃ (c′ ×̇ δ) | c′ ×̇ δ ∈ γ }
  --       = { (⊤ × c′) ×̇ δ | c′ ×̇ δ ∈ γ }
  sum $ do
    RNFProds δ :* _c ← iter γ
    return $ RNFProds δ ↦ Top

-- ┌─────┐
-- │c ×̃ α│
-- └─────┘
prodRNFMaxsConstant ∷ 𝔻 → 𝑃 RNFMins → 𝑃 RNFMins
prodRNFMaxsConstant c α = 
  -- c ×̃ α ≜ { c × (c′ ⊓̇ β) | c′ ⊓̇ β ∈ α }
  --       = { (c × c′) ⊓̇ (c ×̃ β) | c′ ⊓̇ β ∈ α }
  pow $ do
    RNFMins c' β ← iter α
    return $ RNFMins (AddTop c × c') $ prodRNFMinsConstant c β


-- ┌─────┐
-- │c ×̃ β│
-- └─────┘
prodRNFMinsConstant ∷ 𝔻 → 𝑃 RNFSums → 𝑃 RNFSums
prodRNFMinsConstant c β = 
  -- c ×̃ β ≜ { c ×̃ (c′ +̇ γ) | c′ +̇ γ ∈ β }
  --       = { (c × c′) +̇ (c ×̃ γ) | c′ +̇ γ ∈ β }
  pow  $ do
     RNFSums c' γ ← iter β
     return $ RNFSums (AddBot c × c') $ prodRNFSumsConstant c γ

-- ┌─────┐
-- │c ×̃ γ│
-- └─────┘
prodRNFSumsConstant ∷ 𝔻 → RNFProds ⇰ AddTop 𝔻 → RNFProds ⇰ AddTop 𝔻
prodRNFSumsConstant c γ = 
  -- c ×̃ γ ≜ { c ×̃ (c′ ×̇ δ) | c′ ×̇ δ ∈ γ }
  --       = { (c × c′) ×̃ δ | c′ ×̇ δ ∈ γ }
  sum $ do
    RNFProds δ :* c' ← iter γ
    return $ RNFProds δ ↦ (AddTop c × c')

-- ┌─────┐
-- │α ×̃ α│
-- └─────┘
prodRNFMaxs ∷ 𝑃 RNFMins → 𝑃 RNFMins → 𝑃 RNFMins
prodRNFMaxs α₁ α₂ = 
  -- α₁ ×̃ α₂ ≜ { (c₁ ⊓̇ β₁) × (c₂ ⊓̇ β₂) | c₁ ⊓̇ β₁ ∈ α₂ , c₂ ⊓̇ β₂ ∈ α₂ }
  --         ≜ { (c₁ × c₂) ⊓ (c₁ × β₁) ⊓ (c₂ × β₂) ⊓ (β₁ × β₂) | c₁ ⊓̇ β₁ ∈ α₂ , c₂ ⊓̇ β₂ ∈ α₂ }
  --         ≜ { (c₁ × c₂) ⊓̇ [(c₁ ×̃ β₁) ∪ (c₂ ×̃ β₂) ∪ (β₁ ×̃ β₂)] | c₁ ⊓̇ β₁ ∈ α₂ , c₂ ⊓̇ β₂ ∈ α₂ }
  pow $ do
    RNFMins c₁ β₁ ← iter α₁
    RNFMins c₂ β₂ ← iter α₂
    return $ RNFMins (c₁ × c₂) $ concat
      [ flip (elimAddTop pø) c₁ $ \ c₁' → prodRNFMinsConstant c₁' β₂
      , flip (elimAddTop pø) c₂ $ \ c₂' → prodRNFMinsConstant c₂' β₁
      , prodRNFMins β₁ β₂
      ]

-- ┌─────┐
-- │β ×̃ β│
-- └─────┘
prodRNFMins ∷ 𝑃 RNFSums → 𝑃 RNFSums → 𝑃 RNFSums
prodRNFMins β₁ β₂ =
  -- β₁ ×̃ β₂ ≜ { (c₁ +̇ γ₁) × (c₂ +̇ γ₂) | c₁ +̇ γ₁ ∈ β₁ , c₂ +̇ γ₂ ∈ β₂ }
  --         = { (c₁ × c₂) + (c₁ × γ₂) + (c₂ × γ₁) + (γ₁ × γ₂) | c₁ +̇ γ₁ ∈ β₁ , c₂ +̇ γ₂ ∈ β₂ }
  --         = { (c₁ × c₂) +̇ [(c₁ ×̃ γ₂) ∪ (c₂ ×̃ γ₁) ∪ (γ₁ ×̃ γ₂)] | c₁ +̇ γ₁ ∈ β₁ , c₂ +̇ γ₂ ∈ β₂ }
  pow $ do
    RNFSums c₁ γ₁ ← iter β₁
    RNFSums c₂ γ₂ ← iter β₂
    return $ RNFSums (c₁ × c₂) $ sum
      [ flip (elimAddBot dø) c₁ $ \ c₁' → prodRNFSumsConstant c₁' γ₂
      , flip (elimAddBot dø) c₂ $ \ c₂' → prodRNFSumsConstant c₂' γ₁
      , prodRNFSums γ₁ γ₂
      ]

-- ┌─────┐
-- │γ ×̃ γ│
-- └─────┘
prodRNFSums ∷ RNFProds ⇰ AddTop 𝔻 → RNFProds ⇰ AddTop 𝔻 → RNFProds ⇰ AddTop 𝔻
prodRNFSums γ₁ γ₂ =
  -- γ₁ ×̃ γ₂ ≜ { (c₁ ×̇ δ₁) × (c₂ ×̇ δ₂) | c₁ ×̇ δ₁ ∈ γ₁ , c₂ ×̇ δ₂ ∈ γ₂ }
  --         = { c₁ × c₂ ×̇ (δ₁ ∪ δ₂) | c₁ ×̇ δ₁ ∈ γ₁ , c₂ ×̇ δ₂ ∈ γ₂ }
  sum $ do
    RNFProds δ₁ :* c₁  ← iter γ₁
    RNFProds δ₂ :* c₂  ← iter γ₂
    return $ RNFProds (δ₁ + δ₂) ↦ (c₁ × c₂)

-- ┌─────┐
-- │e ×̃ e│
-- └─────┘
prodRNF ∷ RNF → RNF → RNF
prodRNF e₁ e₂ = case (e₁,e₂) of
  -- ⊥ ×̃ e ≜ ⊥
  (ConstantRNF BotBT,_) → ConstantRNF BotBT
  -- e ×̃ ⊥ ≜ ⊥
  (_,ConstantRNF BotBT) → ConstantRNF BotBT
  -- ⊤ ×̃ c ≜ ⊤
  (ConstantRNF TopBT,ConstantRNF _) → ConstantRNF TopBT
  -- c ×̃ ⊤ ≜ ⊤
  (ConstantRNF _,ConstantRNF TopBT) → ConstantRNF BotBT
  -- c₁ ×̃ c₂ ≜ c₁ × c₂
  (ConstantRNF (AddBT c₁),ConstantRNF (AddBT c₂)) → ConstantRNF $ AddBT $ c₁ × c₂
  -- ⊤ ×̃ (c₂ ⊔̇ α₂) ≜ (⊤ × c₂) ⊔ (⊤ × α₂) = ⊤
  (ConstantRNF TopBT,SymRNF (RNFMaxs (AddBot _) _)) → ConstantRNF TopBT
  -- (c₁ ⊔̇ α₁) ×̃ ⊤ ≜ (⊤ × c₁) ⊔ (⊤ × α₁) = ⊤
  (SymRNF (RNFMaxs (AddBot _) _),ConstantRNF TopBT) → ConstantRNF TopBT
  -- ⊤ ×̃ (⊥ ⊔̇ α₂) ≜ (⊤ × ⊥) ⊔ (⊤ × α₂) = ⊥ ⊔̇ (⊤ ×̃ α₂)
  (ConstantRNF TopBT,SymRNF (RNFMaxs Bot α₂)) → case prodRNFMaxsTop α₂ of
    Top → ConstantRNF TopBT
    AddTop α₂' → SymRNF $ RNFMaxs Bot α₂'
  -- (⊥ ⊔̇ α₁) ×̃ ⊤ ≜ (⊤ × ⊥) ⊔ (⊤ × α₁) = ⊥ ⊔̇ (⊤ ×̃ α₁)
  (SymRNF (RNFMaxs Bot α₁),ConstantRNF TopBT) → case prodRNFMaxsTop α₁ of
    Top → ConstantRNF TopBT
    AddTop α₁' → SymRNF $ RNFMaxs Bot α₁'
  -- c₁ ×̃ (c₂ ⊔̇ α₂) ≜ (c₁ × c₂) ⊔̇ (c₁ ×̃ α₂)
  (ConstantRNF (AddBT c₁),SymRNF (RNFMaxs c₂ α₂)) → SymRNF $ RNFMaxs (AddBot c₁ × c₂) $ prodRNFMaxsConstant c₁ α₂
  -- (c₁ ⊔̇ α₁) ×̃ c₂ ≜ (c₁ × c₂) ⊔̇ (c₂ ×̃ α₁)
  (SymRNF (RNFMaxs c₁ α₁),ConstantRNF (AddBT c₂)) → SymRNF $ RNFMaxs (c₁ × AddBot c₂) $ prodRNFMaxsConstant c₂ α₁
  -- (⊥ ⊔̇ α₁) ×̃ (⊥ ⊔̇ α₂) ≜ ⊥ ⊔̇ (α₁ ×̃ α₂)
  (SymRNF (RNFMaxs Bot α₁),SymRNF (RNFMaxs Bot α₂)) → SymRNF $ RNFMaxs Bot $ prodRNFMaxs α₁ α₂
  -- (⊥ ⊔̇ α₁) ×̃ (c₂ ⊔̇ α₂) ≜ ⊥ ⊔̇ [(c₂ ×̃ α₁) ∪ (α₁ ×̃ α₂)]
  (SymRNF (RNFMaxs Bot α₁),SymRNF (RNFMaxs (AddBot c₂) α₂)) → SymRNF $ RNFMaxs Bot $ concat
    [ prodRNFMaxsConstant c₂ α₁
    , prodRNFMaxs α₁ α₂
    ]
  -- (c₁ ⊔̇ α₁) ×̃ (⊥ ⊔̇ α₂) ≜ ⊥ ⊔̇ [(c₁ ×̃ α₂) ∪ (α₁ ×̃ α₂)]
  (SymRNF (RNFMaxs (AddBot c₁) α₁),SymRNF (RNFMaxs Bot α₂)) → SymRNF $ RNFMaxs Bot $ concat
    [ prodRNFMaxsConstant c₁ α₂
    , prodRNFMaxs α₁ α₂
    ]
  -- (c₁ ⊔̇ α₁) ×̃ (c₂ ⊔̇ α₂) ≜ (c₁ × c₂) ⊔̇ [(c₁ ×̃ α₂) ∪ (c₂ ×̃ α₁) ∪ (α₁ ×̃ α₂)]
  (SymRNF (RNFMaxs (AddBot c₁) α₁),SymRNF (RNFMaxs (AddBot c₂) α₂)) → SymRNF $ RNFMaxs (AddBot $ c₁ × c₂) $ concat
    [ prodRNFMaxsConstant c₁ α₂
    , prodRNFMaxsConstant c₂ α₁
    , prodRNFMaxs α₁ α₂
    ]

-----------
-- POWER --
-----------

-- LEFT OFF HERE

-- ┌─────┐
-- │α ^̃ c│
-- └─────┘
powerRNFMaxs ∷ 𝑃 RNFMins → 𝑃 RNFMins
powerRNFMaxs α =
  -- 1/̃ α ≜ { 1/̃(c ⊓̇ β) | c ⊓̇ β ∈ α }
  --      = { (1/c) ⊓̇ (1/̃β) | c ⊓̇ β ∈ α }
  pow $ do
    RNFMins c β ← iter α
    return $ RNFMins (AddTop 1.0 / c) $ invRNFMins β

-- ┌────┐
-- │1/̃ β│
-- └────┘
invRNFMins ∷ 𝑃 RNFSums → 𝑃 RNFSums
invRNFMins β = 
  -- 1/̃ β ≜ { 1/̃ (c +̇ γ) | c +̇ γ ∈ β }
  -- where
  --   1/̃ (c +̇ γ) ≜ (1/c′) ×̇ 1/̃δ        when  c = 0  and  γ = {c′ × δ}
  --              ≜ 1/̇ (c +̇ γ)          otherwise
  pow $ do
    RNFSums c γ ← iter β
    case (c,list γ) of
      (Bot,(RNFProds δ :* c') :& Nil) → return $ RNFSums Bot $ RNFProds (invRNFProds δ) ↦ (AddTop 1.0 / c')
      _ → return $ RNFSums Bot $ RNFProds ((InvRA $ RNFSums c γ) ↦ 1.0) ↦ AddTop 1.0

-- ┌────┐
-- │1/̃ γ│
-- └────┘
invRNFProds ∷ RNFAtom ⇰ 𝔻 → RNFAtom ⇰ 𝔻 
invRNFProds δ = 
  -- 1/̃ δ ≜ { 1/̃(ε ^̇ c) | ε ^̇ c ∈ δ }
  --      ≜ (1/ε) ^̇ c | ε ^̇ c ∈ δ }
  sum $ do
    ε :* c ← iter δ
    return $ invRNFAtom ε ↦ c

-- ┌────┐
-- │1/̃ ε│
-- └────┘
invRNFAtom ∷ RNFAtom → RNFAtom
invRNFAtom (InvRA γ̇) = _ γ̇

-- ┌────┐
-- │1/̃ e│
-- └────┘
invRNF ∷ RNF → RNF
invRNF e = case e of
  -- 1/̃ ⊥ ≜ ⊥
  ConstantRNF BotBT → ConstantRNF BotBT
  -- 1/̃ ⊤ ≜ ⊤
  ConstantRNF TopBT → ConstantRNF TopBT
  -- 1/̃ c ≜ 1/c
  ConstantRNF (AddBT c) → ConstantRNF $ AddBT $ 1.0 / c
  -- 1/̃(c ⊔̇ α) ≜ (1/c) ⊔̇ (1/̃ α)
  SymRNF (RNFMaxs c α) → SymRNF $ RNFMaxs (AddBot 1.0 / c) $ invRNFMaxs α
