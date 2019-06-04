module Duet.RNF2Fixed where

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
-- δ̇ ×̈ c ∈ γ
data RNFSums = RNFSums
  { rnfSumsConstant ∷ AddBot 𝔻
  , rnfSumsSymbolic ∷ RNFProds ⇰ AddTop 𝔻 -- (at least one inside)
  }
  deriving (Eq,Ord,Show)

-- δ̇ ∈ RNFProds ⩴ δ̂ ×̇ δ̌
-- δ̂ ∈ RNFSums ⇰ ℚ
-- δ̌ ∈ RNFAtom ⇰ ℚ
data RNFProds = RNFProds
  { rnfProdsSymbolicIrred ∷ RNFSums ⇰ ℚ -- (at least one inside one of these)
  , rnfProdsSymbolicAtoms ∷ RNFAtom ⇰ ℚ -- (at least one inside one of these)
  }
  deriving (Eq,Ord,Show)

-- ε ∈ RNFAtom
data RNFAtom =
    VarRA 𝕏
  | LogRA RNFSums
  | EfnRA RNFProds
  deriving (Eq,Ord,Show)

-------------
-- HELPERS --
-------------

oneAtom ∷ RNFAtom → RNFProds
oneAtom ε = RNFProds dø $ ε ↦ one

oneProd ∷ RNFProds → RNFSums
oneProd δ = RNFSums Bot $ δ ↦ AddTop 1.0

oneSum ∷ RNFSums → RNFMins
oneSum γ = RNFMins Top $ single γ

oneMin ∷ RNFMins → RNFMaxs
oneMin β = RNFMaxs Bot $ single β

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
varRNF = 
  SymRNF 
  ∘ oneMin
  ∘ oneSum
  ∘ oneProd
  ∘ oneAtom
  ∘ VarRA

---------
-- MAX --
---------

-- ┌─────┐
-- │c ⊔̃ α̇│
-- └─────┘
maxRNFMaxsConstant ∷ 𝔻 → RNFMaxs → RNFMaxs
maxRNFMaxsConstant c (RNFMaxs d α) = 
  -- c ⊔̃ (d ⊔̇ α) ≜ (c ⊔ d) ⊔̇ α
  RNFMaxs (AddBot c ⊔ d) α

-- ┌─────┐
-- │α̇ ⊔̃ α̇│
-- └─────┘
maxRNFMaxs ∷ RNFMaxs → RNFMaxs → RNFMaxs
maxRNFMaxs (RNFMaxs d₁ α₁) (RNFMaxs d₂ α₂) = 
  -- (d₁ ⊔̇ α₁) ⊔̃ (d₂ ⊔̇ α₂) ≜ (d₁ ⊔ d₂) ⊔̇ (α₁ ∪ α₂)
  RNFMaxs (d₁ ⊔ d₂) $ α₁ ∪ α₂

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
  -- c ⊔̃ α̇
  (ConstantRNF (AddBT c),SymRNF α̇) → SymRNF $ maxRNFMaxsConstant c α̇
  -- α̇ ⊔̃ c
  (SymRNF α̇,ConstantRNF (AddBT c)) → SymRNF $ maxRNFMaxsConstant c α̇
  -- α̇₁ ⊔̃ α̇₂
  (SymRNF α̇₁, SymRNF α̇₂) → SymRNF $ maxRNFMaxs α̇₁ α̇₂

---------
-- MIN --
---------

-- ┌─────┐
-- │c ⊓̃ α̇│
-- └─────┘
minRNFMaxsConstant ∷ 𝔻 → RNFMaxs → RNFMaxs
minRNFMaxsConstant c (RNFMaxs d α) = 
  -- c ⊓̃ (d ⊔̇ α) ≜ (c ⊓ d) ⊔̇ (c ⊓̃ α)
  RNFMaxs (AddBot c ⊓ d) $ minRNFMaxsConstantSym c α

-- ┌─────┐
-- │c ⊓̃ α│
-- └─────┘
minRNFMaxsConstantSym ∷ 𝔻 → 𝑃 RNFMins → 𝑃 RNFMins
minRNFMaxsConstantSym c α =
  -- c ⊓̃ α = c ⊓ ⨆{β̇ | β̇ ∈ α}
  --       ≜ ⨆{ c ⊓ β̇ | β̇ ∈ α }
  pow $ do
    β̇ ← iter α
    return $ minRNFMinsConstant c β̇
    
-- ┌─────┐
-- │c ⊓̃ β̇│
-- └─────┘
minRNFMinsConstant ∷ 𝔻 → RNFMins → RNFMins
minRNFMinsConstant c (RNFMins d β) = 
  -- c ⊓̃ (d ⊓̇ β) ≜ (c ⊓ d) ⊓̇ β 
  RNFMins (AddTop c ⊓ d) β

-- ┌─────┐
-- │α̇ ⊓̃ α̇│
-- └─────┘
minRNFMaxs ∷ RNFMaxs → RNFMaxs → RNFMaxs
minRNFMaxs (RNFMaxs d₁ α₁) (RNFMaxs d₂ α₂) = 
  -- (d₁ ⊔̇ α₁) ⊓̃ (d₂ ⊔̇ α₂) ≜ (d₁ ⊓ d₂) ⊔̇ ⋃{d₁ ⊓̃ α₂ , d₂ ⊓̃ α₁ , α₁ ⊓̃ α₂ }
  RNFMaxs (d₁ ⊓ d₂) $ joins
    [ flip (elimAddBot pø) d₁ $ \ d₁' → minRNFMaxsConstantSym d₁' α₂
    , flip (elimAddBot pø) d₂ $ \ d₂' → minRNFMaxsConstantSym d₂' α₁
    , minRNFMaxsSym α₁ α₂
    ]

-- ┌─────┐
-- │α ⊓̃ α│
-- └─────┘
minRNFMaxsSym ∷ 𝑃 RNFMins → 𝑃 RNFMins → 𝑃 RNFMins
minRNFMaxsSym α₁ α₂ = 
  -- α₁ ⊓̃ α₂ = ⨆{β̇ | β̇ ∈ α₁} ⊓ ⨆{β̇ | β̇ ∈ α₂}
  --         ≜ ⨆{ β̇₁ ⊓ β̇₂ | β̇₁ ∈ α₁ , β̇₂ ∈ α₂ }
  pow $ do
    β̇₁ ← iter α₁
    β̇₂ ← iter α₂
    return $ minRNFMins β̇₁ β̇₂

-- ┌─────┐
-- │β̇ ⊓̃ β̇│
-- └─────┘
minRNFMins ∷ RNFMins → RNFMins → RNFMins
minRNFMins (RNFMins d₁ β₁) (RNFMins d₂ β₂) =
  -- (d₁ ⊓̇ β₁) ⊓̃ (d₂ ⊓̇ β₂) ≜ (d₁ ⊓ d₂) ⊓̇ (β₁ ∪ β₂)
  RNFMins (d₁ ⊓ d₂) $ β₁ ∪ β₂


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
  -- c ⊓̃ α̇
  (ConstantRNF (AddBT c),SymRNF α̇) → SymRNF $ minRNFMaxsConstant c α̇
  -- α̇ ⊓̃ c
  (SymRNF α̇,ConstantRNF (AddBT c)) → SymRNF $ minRNFMaxsConstant c α̇
  -- (c₁ ⊔̇ α₁) ⊓̃ (c₂ ⊔̇ α₂) ≜ (c₁ ⊓ c₂) ⊔̇ [(c₁ ⊓̃ α₂) ∪ (c₂ ⊓̃ α₁) ∪ (α₁ ⊓̃ α₂)]
  (SymRNF α̇₁,SymRNF α̇₂) → SymRNF $ minRNFMaxs α̇₁ α̇₂

----------
-- PLUS --
----------

-- ┌─────┐
-- │c +̃ α̇│
-- └─────┘
sumRNFMaxsConstant ∷ 𝔻 → RNFMaxs → RNFMaxs
sumRNFMaxsConstant c (RNFMaxs d α) = 
  -- c +̃ (d ⊔̇ α) ≜ (c + d) ⊔̇ (c +̃ α)
  RNFMaxs (AddBot c + d) $ sumRNFMaxsConstantSym c α

-- ┌─────┐
-- │c +̃ α│
-- └─────┘
sumRNFMaxsConstantSym ∷ 𝔻 → 𝑃 RNFMins → 𝑃 RNFMins
sumRNFMaxsConstantSym c α = 
  -- c +̃ α = c + ⨆{β̇ | β̇ ∈ α}
  --       = ⨆{ c +̃ β̇ | β̇ ∈ α }
  pow $ do
    β̇ ← iter α
    return $ sumRNFMinsConstant c β̇

-- ┌─────┐
-- │c +̃ β̇│
-- └─────┘
sumRNFMinsConstant ∷ 𝔻 → RNFMins → RNFMins
sumRNFMinsConstant c (RNFMins d β) = 
  -- c +̃ (d ⊓̇ β) ≜ (c + d) ⊓̇ (c ⊓̃ β)
  RNFMins (AddTop c + d) $ sumRNFMinsConstantSym c β

-- ┌─────┐
-- │c +̃ β│
-- └─────┘
sumRNFMinsConstantSym ∷ 𝔻 → 𝑃 RNFSums → 𝑃 RNFSums
sumRNFMinsConstantSym c β = 
  -- c +̃ β ≜ c + ⨅{γ̇ | γ̇ ∈ β}
  --       ≜ ⨅{c ⊓̃ γ̇ | γ̇ ∈ β}
  pow $ do
    γ̇ ← iter β
    return $ sumRNFSumsConstant c γ̇
    
-- ┌─────┐
-- │c +̃ γ̇│
-- └─────┘
sumRNFSumsConstant ∷ 𝔻 → RNFSums → RNFSums
sumRNFSumsConstant c (RNFSums d γ) =
  -- c +̃ (d +̇ γ) ≜ (c + d) +̇ γ
  RNFSums (AddBot c + d) γ

-- ┌─────┐
-- │α̇ +̃ α̇│
-- └─────┘
sumRNFMaxs ∷ RNFMaxs → RNFMaxs → RNFMaxs
sumRNFMaxs (RNFMaxs d₁ α₁) (RNFMaxs d₂ α₂) =
  -- (d₁ ⊔̇ α₁) +̃ (d₂ ⊔̇ α₂) ≜ (d₁ + d₂) ⊔̇ ⋃{ d₁ +̃ α₂ , d₂ +̃ α₁ , α₁ +̃ α₂ }
  RNFMaxs (d₁ + d₂) $ joins
    [ flip (elimAddBot pø) d₁ $ \ d₁' → sumRNFMaxsConstantSym d₁' α₂
    , flip (elimAddBot pø) d₂ $ \ d₂' → sumRNFMaxsConstantSym d₂' α₁
    , sumRNFMaxsSym α₁ α₂
    ]

-- ┌─────┐
-- │α +̃ α│
-- └─────┘
sumRNFMaxsSym ∷ 𝑃 RNFMins → 𝑃 RNFMins → 𝑃 RNFMins
sumRNFMaxsSym α₁ α₂ = 
  -- α₁ +̃ α₂ = ⨆{β̇ | β̇ ∈ α₁} + ⨆{β̇ | β̇ ∈ α₂}
  --         ≜ ⨆{ β̇₁ +̃ β₂ | β̇₁ ∈ α₁ , β̇₂ ∈ α₂ }
  pow $ do
    β̇₁ ← iter α₁
    β̇₂ ← iter α₂
    return $ sumRNFMins β̇₁ β̇₂

-- ┌─────┐
-- │β̇ +̃ β̇│
-- └─────┘
sumRNFMins ∷ RNFMins → RNFMins → RNFMins
sumRNFMins (RNFMins d₁ β₁) (RNFMins d₂ β₂) =
  -- (d₁ ⊓̇ β₁) +̃ (d₂ ⊓̇ β₂) = (d₁ + d₂) ⊓̇ ⋃{ d₁ +̃ β₂ , d₂ +̃ β₁ , β₁ +̃ β₂ }
  RNFMins (d₁ + d₂) $ joins
     [ flip (elimAddTop pø) d₁ $ \ d₁' → sumRNFMinsConstantSym d₁' β₂
     , flip (elimAddTop pø) d₂ $ \ d₂' → sumRNFMinsConstantSym d₂' β₁
     , sumRNFMinsSym β₁ β₂
     ]

-- ┌─────┐
-- │β +̃ β│
-- └─────┘
sumRNFMinsSym ∷ 𝑃 RNFSums → 𝑃 RNFSums → 𝑃 RNFSums
sumRNFMinsSym β₁ β₂ =
  -- β₁ +̃ β₂ = ⨅{γ̇ | γ̇ ∈ β₁} + ⨅{γ̇ | γ̇ ∈ β₂}
  --         ≜ ⨅{γ̇₁ +̃ γ̇₂ | γ̇₁ ∈ β₁ , γ̇₂ ∈ β₂}
  pow $ do
    γ̇₁ ← iter β₁
    γ̇₂ ← iter β₂
    return $ sumRNFSums γ̇₁ γ̇₂
    
-- ┌─────┐
-- │γ̇ +̃ γ̇│
-- └─────┘
sumRNFSums ∷ RNFSums → RNFSums → RNFSums
sumRNFSums (RNFSums d₁ γ₁) (RNFSums d₂ γ₂) = 
  -- (d₁ +̇ γ₁) +̃ (d₂ +̇ γ₂) ≜ (d₁ + d₂) +̇ (γ₁ ⊎ γ₂) 
  RNFSums (d₁ + d₂) $ γ₁ ⊎ γ₂

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
  -- c +̃ α̇
  (ConstantRNF (AddBT c),SymRNF α̇) → SymRNF $ sumRNFMaxsConstant c α̇
  -- α̇ +̃ c
  (SymRNF α̇,ConstantRNF (AddBT c)) → SymRNF $ sumRNFMaxsConstant c α̇
  -- α̇₁ +̃ α̇₂
  (SymRNF α̇₁,SymRNF α̇₂) → SymRNF $ sumRNFMaxs α̇₁ α̇₂

-----------
-- TIMES --
-----------

-- ┌─────┐
-- │⊤ ×̃ α̇│
-- └─────┘
prodRNFMaxsTop ∷ RNFMaxs → AddTop RNFMaxs
prodRNFMaxsTop (RNFMaxs dB α) = case dB of
  -- ⊤ ×̃ (⊥ ⊔̇ α) ≜ ⊥ ⊔̇ (⊤ ×̃ α)
  Bot → do
    α' ← prodRNFMaxsTopSym α
    return $ RNFMaxs Bot α'
  -- ⊤ ×̃ (d ⊔̇ α) ≜ ⊤
  AddBot _ → Top

-- ┌─────┐
-- │⊤ ×̃ α│
-- └─────┘
prodRNFMaxsTopSym ∷ 𝑃 RNFMins → AddTop (𝑃 RNFMins)
prodRNFMaxsTopSym α = 
  -- ⊤ ×̃ α = ⊤ × ⨆{β̇ | β̇ ∈ α}
  --       ≜ { ⊤ ×̃ β̇ | β̇ ∈ α }
  map pow $ mapM id $ do
    β̇ ← iter α
    return $ prodRNFMinsTop β̇
    
    
prodRNFMinsTop ∷ RNFMins → AddTop RNFMins
prodRNFMinsTop (RNFMins _ β) = do
  -- ⊤ ×̃ (d ⊓̇ β) = (⊤ × d) ⊓̇ (⊤ ×̃ β)
  --             ≜ ⊤ ⊓̇ (⊤ ×̃ β)
  β' ← prodRNFMinsTopSym β
  return $ RNFMins Top β'

-- ┌─────┐
-- │⊤ ×̃ β│
-- └─────┘
prodRNFMinsTopSym ∷ 𝑃 RNFSums → AddTop (𝑃 RNFSums)
prodRNFMinsTopSym β = 
  -- ⊤ ×̃ β = ⊤ × ⨅{ γ̇ | γ̇ ∈ β }
  --       ≜ ⨅{ ⊤ × γ̇ | γ̇ ∈ β }
  map pow $ mapM id $ do
     γ̇ ← iter β
     return $ prodRNFSumsTop γ̇

-- ┌─────┐
-- │⊤ ×̃ γ̇│
-- └─────┘
prodRNFSumsTop ∷ RNFSums → AddTop RNFSums
prodRNFSumsTop (RNFSums dB γ) = case dB of
  -- ⊤ ×̃ (⊥ +̇ γ) = (⊤ × ⊥) +̇ (⊤ ×̃ γ)
  --             ≜ ⊥ +̇ (⊤ ×̃ γ)
  Bot → AddTop $ RNFSums Bot $ prodRNFSumsTopSym γ
  -- ⊤ ×̃ (d +̇ γ) = (⊤ × d) +̇ (⊤ ×̃ γ)
  --             = ⊤
  AddBot _ → Top

-- ┌─────┐
-- │⊤ ×̃ γ│
-- └─────┘
prodRNFSumsTopSym ∷ RNFProds ⇰ AddTop 𝔻 → RNFProds ⇰ AddTop 𝔻
prodRNFSumsTopSym γ = 
  -- ⊤ ×̃ γ = ⊤ × ∑{ δ̇ ×̈ d | δ̇ ×̈ d ∈ γ }
  --       ≜ ∑{ δ̇ ×̈ ⊤ | δ̇ ×̈ d ∈ γ }
  sum $ do
    δ̇ :* _d ← iter γ
    return $ δ̇ ↦ Top

-- ┌─────┐
-- │c ×̃ α̇│
-- └─────┘
prodRNFMaxsConstant ∷ 𝔻 → RNFMaxs → RNFMaxs
prodRNFMaxsConstant c (RNFMaxs d α) =
  -- c ×̃ (d ⊔̇ α) ≜ (c × d) ⊔̇ (c ×̃ α)
  RNFMaxs (AddBot c × d) $ prodRNFMaxsConstantSym c α

-- ┌─────┐
-- │c ×̃ α│
-- └─────┘
prodRNFMaxsConstantSym ∷ 𝔻 → 𝑃 RNFMins → 𝑃 RNFMins
prodRNFMaxsConstantSym c α = 
  -- c ×̃ α = c × ⨆{ β̇ | β̇ ∈ α }
  --       ≜ ⨆{ c × β̇ | β̇ ∈ α }
  pow $ do
    RNFMins c' β ← iter α
    return $ RNFMins (AddTop c × c') $ prodRNFMinsConstantSym c β

prodRNFMinsConstant ∷ 𝔻 → RNFMins → RNFMins
prodRNFMinsConstant c (RNFMins d β) =
  -- c ×̃ (d ⊓̇ β) ≜ (c × d) ⊓̇ (c ×̃ β)
  RNFMins (AddTop c × d) $ prodRNFMinsConstantSym c β

-- ┌─────┐
-- │c ×̃ β│
-- └─────┘
prodRNFMinsConstantSym ∷ 𝔻 → 𝑃 RNFSums → 𝑃 RNFSums
prodRNFMinsConstantSym c β = 
  -- c ×̃ β = c × ∑{ γ̇ | γ̇ ∈ β}
  --       ≜ ∑{ c × γ̇ | γ̇ ∈ β}
  pow $ do
    γ̇ ← iter β
    return $ prodRNFSumsConstant c γ̇

-- ┌─────┐
-- │c ×̃ γ̇│
-- └─────┘
prodRNFSumsConstant ∷ 𝔻 → RNFSums → RNFSums
prodRNFSumsConstant c (RNFSums d γ) = 
  -- c ×̃ (d +̇ γ) ≜ (c × d) +̇ (c ×̃ γ)
  RNFSums (AddBot c × d) $ prodRNFSumsConstantSym c γ

-- ┌─────┐
-- │c ×̃ γ│
-- └─────┘
prodRNFSumsConstantSym ∷ 𝔻 → RNFProds ⇰ AddTop 𝔻 → RNFProds ⇰ AddTop 𝔻
prodRNFSumsConstantSym c γ = 
  -- c ×̃ γ ≜ c × ∏{ δ̇ ×̈ d | δ̇ ×̈ d ∈ γ }
  --       = ∏{ δ̇ ×̈ (c × d) | δ̇ ×̈ d ∈ γ }
  sum $ do
    δ̇ :* d ← iter γ
    return $ δ̇ ↦ (AddTop c × d)

-- ┌─────┐
-- │α̇ ×̃ α̇│
-- └─────┘
prodRNFMaxs ∷ RNFMaxs → RNFMaxs → AddTop RNFMaxs
prodRNFMaxs (RNFMaxs d₁ α₁) (RNFMaxs d₂ α₂) = do
  -- (d₁ ⊔̇ α₁) ×̃ (d₂ ⊔̇ α₂) ≜ (d₁ × d₂) ⊔̇ ⋃{ d₁ ×̃ α₂ , d₂ ×̃ α₁ , α₁ ×̃ α₂ }
  α ← prodRNFMaxsSym α₁ α₂
  return $ 
    RNFMaxs (d₁ × d₂) $ joins
      [ flip (elimAddBot pø) d₁ $ \ d₁' → prodRNFMaxsConstantSym d₁' α₂
      , flip (elimAddBot pø) d₂ $ \ d₂' → prodRNFMaxsConstantSym d₂' α₁
      , α
      ]

-- ┌─────┐
-- │α ×̃ α│
-- └─────┘
prodRNFMaxsSym ∷ 𝑃 RNFMins → 𝑃 RNFMins → AddTop (𝑃 RNFMins)
prodRNFMaxsSym α₁ α₂ = 
  -- α₁ ×̃ α₂ = ⨆{ β̇ | β̇ ∈ α₁} × ⨆{ β̇ | β̇ ∈ α₂}
  --         ≜ ⨆{ β̇₁ ×̃ β̇₂ | β̇₁ ∈ α₁ , β̇₂ ∈ α₂ }
  let α = pow $ do
            β̇₁ ← iter α₁
            β̇₂ ← iter α₂
            elimAddTop null return $ prodRNFMins β̇₁ β̇₂
  in case α ≡ pø of
    True → Top
    False → AddTop α


-- ┌─────┐
-- │β̇ ×̃ β̇│
-- └─────┘
prodRNFMins ∷ RNFMins → RNFMins → AddTop RNFMins
prodRNFMins (RNFMins d₁ β₁) (RNFMins d₂ β₂) =
  -- (d₁ ⊓̇ β₁) ×̃ (d₂ ⊓̇ β₂) ≜ (d₁ × d₂) ⊓̇ ⋃{ d₁ ×̃ β₂ , d₂ ×̃ β₁ , β₁ ×̃ β₂ }
  let β = joins
        [ flip (elimAddTop pø) d₁ $ \ d₁' → prodRNFMinsConstantSym d₁' β₂
        , flip (elimAddTop pø) d₂ $ \ d₂' → prodRNFMinsConstantSym d₂' β₁
        , elimAddTop pø id $ prodRNFMinsSym β₁ β₂
        ]
  in case β ≡ pø of
    True → Top
    False → AddTop $ RNFMins (d₁ × d₂) β

-- ┌─────┐
-- │β ×̃ β│
-- └─────┘
prodRNFMinsSym ∷ 𝑃 RNFSums → 𝑃 RNFSums → AddTop (𝑃 RNFSums)
prodRNFMinsSym β₁ β₂ =
  -- β₁ ×̃ β₂ = ⨅{ γ̇ | γ̇ ∈ β₁ } × ⨅{ γ̇ | γ̇ ∈ β₁ }
  --         ≜ ⨅{ γ̇₁ ×̃ γ̇₂ | γ̇₁ ∈ β₁ , γ̇₂ ∈ β₂ }
  let β = pow $ do
        γ̇₁ ← iter β₁
        γ̇₂ ← iter β₂
        elimAddTop null return $ prodRNFSums γ̇₁ γ̇₂
  in case β ≡ pø of
    True → Top
    False → AddTop β

-- FIXED --

-- ┌─────┐
-- │γ̇ ×̃ γ̇│
-- └─────┘
prodRNFSums ∷ RNFSums → RNFSums → AddTop RNFSums
prodRNFSums (RNFSums d₁ γ₁) (RNFSums d₂ γ₂) = do
  -- (d₁ +̇ γ₁) ×̃ (d₁ +̇ γ₂) ≜ (d₁ × d₂) +̇ ⋃{ d₁ ×̃ γ₂ , d₂ ×̃ γ₁ , γ₁ ×̃ γ₂ }
  RNFSums d₃ γ₃ ← prodRNFSumsSym γ₁ γ₂
  return $ RNFSums (d₁ × d₂ + d₃) $ sum
    [ flip (elimAddBot dø) d₁ $ \ d₁' → prodRNFSumsConstantSym d₁' γ₂
    , flip (elimAddBot dø) d₂ $ \ d₂' → prodRNFSumsConstantSym d₂' γ₁
    , γ₃
    ]

-- ┌─────┐
-- │γ ×̃ γ│
-- └─────┘
prodRNFSumsSym ∷ RNFProds ⇰ AddTop 𝔻 → RNFProds ⇰ AddTop 𝔻 → AddTop RNFSums
prodRNFSumsSym γ₁ γ₂ =
  -- γ₁ ×̃ γ₂ = ∑{ δ̇ ×̈ d | δ̇ ×̈ d ∈ γ₁ } × ∑{ δ̇ ×̈ d | δ̇ ×̈ d ∈ γ₂ }
  --         = ∑{ (δ̇₁ ×̃ δ̇₂) ×̈ (d₁ × d₂) | δ̇₁ ×̈ d₁ ∈ γ₁ , δ̇₂ ×̈ d₂ ∈ γ₂ }
  --         = ∑{ (d₁ × d₂) × γ̇ | γ̇ ∈ (δ̇₁ ×̃ δ̇₂) , δ̇₁ ×̈ d₁ ∈ γ₁ , δ̇₂ ×̈ d₂ ∈ γ₂ }
  --         = ∑{ 
  --
  mfoldWith (map tohs $ iter γ₁ ⧆ iter γ₂) (RNFSums Bot dø) $ \ ((δ̇₁,d₁),(δ̇₂,d₂)) γ̇ᵢ → do
    d₁₂ ← d₁ × d₂
    γ̇ ← prodRNFProds δ̇₁ δ̇₂
    return $ sumRNFSums γ̇ᵢ $ prodRNFSumsConstant d₁₂ γ̇

-- ┌─────┐
-- │δ̇ ×̃ δ̇│
-- └─────┘
prodRNFProds ∷ RNFProds → RNFProds → AddTop RNFSums
prodRNFProds (RNFProds δ̂₁ δ̌₁) (RNFProds δ̂₂ δ̌₂) =
  -- (δ̂₁ ×̇ δ̌₁) ×̃ (δ̂₂ ×̇ δ̌₂) ≜ (δ̂₁ ⊎ δ̂₂) ×̇ (δ̌₂ ⊎ δ̌₂)
  reinterpSumsFP $ oneProd $ RNFProds (δ̂₁ ⊎ δ̂₂) (δ̌₁ ⊎ δ̌₂)

reinterpSumsFP ∷ RNFSums → AddTop RNFSums
reinterpSumsFP γ̇ = fp (AddTop γ̇) reinterpSums

reinterpSums ∷ AddTop RNFSums → AddTop RNFSums
reinterpSums γ̇M = do
  RNFSums c γ₀ ← γ̇M
  RNFSums c' γ' ← mfoldWith γ₀ (RNFSums Bot dø) $ \ (RNFProds δ̂₀ δ̌₀ :* d) γ̇ᵢ → do
    elimAddTop prodRNFSumsTop (kreturn ∘ prodRNFSumsConstant) d $ 
      sumRNFSums γ̇ᵢ $
        foldWith δ̂₀ (oneProd $ RNFProds dø δ̌₀) $ \ (γ̇ :* d') γ̇ⱼ →
          prodRNFSumsNorec γ̇ⱼ $ powerRNFSumsNorec d' γ̇
  return $ RNFSums (c + c') γ'

-- NOREC --

-- ┌─────┐
-- │γ̇ ×̃ γ̇│
-- └─────┘
prodRNFSumsNorec ∷ RNFSums → RNFSums → RNFSums
prodRNFSumsNorec (RNFSums d₁ γ₁) (RNFSums d₂ γ₂) =
  -- (d₁ +̇ γ₁) ×̃ (d₁ +̇ γ₂) ≜ (d₁ × d₂) +̇ ⋃{ d₁ ×̃ γ₂ , d₂ ×̃ γ₁ , γ₁ ×̃ γ₂ }
  RNFSums (d₁ × d₂) $ sum
    [ flip (elimAddBot dø) d₁ $ \ d₁' → prodRNFSumsConstantSym d₁' γ₂
    , flip (elimAddBot dø) d₂ $ \ d₂' → prodRNFSumsConstantSym d₂' γ₁
    , prodRNFSumsSymNorec γ₁ γ₂
    ]

-- ┌─────┐
-- │γ ×̃ γ│
-- └─────┘
prodRNFSumsSymNorec ∷ RNFProds ⇰ AddTop 𝔻 → RNFProds ⇰ AddTop 𝔻 → RNFProds ⇰ AddTop 𝔻
prodRNFSumsSymNorec γ₁ γ₂ =
  -- γ₁ ×̃ γ₂ = ∑{ δ̇ ×̈ d | δ̇ ×̈ d ∈ γ₁ } × ∑{ δ̇ ×̈ d | δ̇ ×̈ d ∈ γ₂ }
  --         ≜ ∑{ (δ̇₁ ×̃ δ̇₂) ×̈ (d₁ × d₂) | δ̇₁ ×̈ d₁ ∈ γ₁ , δ̇₂ ×̈ d₂ ∈ γ₂ }
  sum $ do
    δ̇₁ :* d₁  ← iter γ₁
    δ̇₂ :* d₂  ← iter γ₂
    return $ prodRNFProdsNorec δ̇₁ δ̇₂ ↦ (d₁ × d₂)

-- ┌─────┐
-- │δ̇ ×̃ δ̇│
-- └─────┘
prodRNFProdsNorec ∷ RNFProds → RNFProds → RNFProds
prodRNFProdsNorec (RNFProds δ̂₁ δ̌₁) (RNFProds δ̂₂ δ̌₂) =
  -- (δ̂₁ ×̇ δ̌₁) ×̃ (δ̂₂ ×̇ δ̌₂) ≜ (δ̂₁ ⊎ δ̂₂) ×̇ (δ̌₂ ⊎ δ̌₂)
  RNFProds (δ̂₁ ⊎ δ̂₂) (δ̌₁ ⊎ δ̌₂)

-- ┌─────┐
-- │γ̇ ^̃ c│
-- └─────┘
powerRNFSumsNorec ∷ ℚ → RNFSums → RNFSums
powerRNFSumsNorec c γ̇ = case γ̇ of
    RNFSums Bot (stream → (uncons𝑆 → Some ((δ̇ :* d) :* (uncons𝑆 → None)))) → 
      RNFSums Bot $ powerRNFProdsNorec c δ̇ ↦ (d ^ AddTop (dbl c))
    _ 
      | c < zero → invRNFSumsNorec $ posPowerRNFSumsNorec (ratAbs c) γ̇
      | otherwise → posPowerRNFSumsNorec (ratAbs c) γ̇

powerRNFProdsNorec ∷ ℚ → RNFProds → RNFProds
powerRNFProdsNorec c (RNFProds δ̂ δ̌) =
  let δ̂' = sum $ do
        γ̇ :* d ← iter δ̂
        return $ γ̇ ↦ (c × d)
      δ̌' = sum $ do
        ε :* d ← iter δ̌
        return $ ε ↦ (c × d)
  in RNFProds δ̂' δ̌'

-- ┌────┐
-- │1/̃ γ̇│
-- └────┘
invRNFSumsNorec ∷ RNFSums → RNFSums
invRNFSumsNorec γ̇ = oneProd $ RNFProds (γ̇ ↦ neg one) dø

-- ┌─────┐
-- │γ̇ ^̃ c│
-- └─────┘
posPowerRNFSumsNorec ∷ 𝕋 → RNFSums → RNFSums
posPowerRNFSumsNorec c γ̇ 
  | c > one = prodRNFSumsNorec γ̇ $ posPowerRNFSumsNorec (c - one) γ̇
  | otherwise = oneProd $ RNFProds (γ̇ ↦ rat c) dø

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
  -- ⊤ ×̃ α̇
  (ConstantRNF TopBT,SymRNF α̇) → elimAddTop (ConstantRNF TopBT) SymRNF $ prodRNFMaxsTop α̇
  -- α̇ ×̃ ⊤
  (SymRNF α̇,ConstantRNF TopBT) → elimAddTop (ConstantRNF TopBT) SymRNF $ prodRNFMaxsTop α̇
  -- c ×̃ α̇
  (ConstantRNF (AddBT c),SymRNF α̇) → SymRNF $ prodRNFMaxsConstant c α̇
  -- α̇ ×̃ c
  (SymRNF α̇,ConstantRNF (AddBT c)) → SymRNF $ prodRNFMaxsConstant c α̇
  -- α̇₁ ×̃ α̇₂
  (SymRNF α̇₁,SymRNF α̇₂) → case prodRNFMaxs α̇₁ α̇₂ of
    Top → ConstantRNF TopBT
    AddTop α̇ → SymRNF α̇

-----------
-- POWER --
-----------

-- ┌─────┐
-- │α̇ ^̃ c│
-- └─────┘
powerRNFMaxs ∷ ℚ → RNFMaxs → RNFMaxs
powerRNFMaxs c (RNFMaxs d α) =
  -- (d ⊔̇ α) ^̃ c ≜ (d ^ c) ⊔̇ (α ^̃ c)
  RNFMaxs (d ^ AddBot (dbl c)) $ powerRNFMaxsSym c α

-- ┌─────┐
-- │α ^̃ c│
-- └─────┘
powerRNFMaxsSym ∷ ℚ → 𝑃 RNFMins → 𝑃 RNFMins
powerRNFMaxsSym c α =
  -- α ^̃ c = ⨆{ β̇ | β̇ ∈ α } ^ c
  --       ≜ ⨆{ β̇ ^̃ c | β̇ ∈ α}
  pow $ do
    β̇ ← iter α
    return $ powerRNFMins c β̇

-- ┌─────┐
-- │β̇ ^̃ c│
-- └─────┘
powerRNFMins ∷ ℚ → RNFMins → RNFMins
powerRNFMins c (RNFMins d β) =
  -- (d ⊓̇ β) ^̃ c = (d ^ c) ⊓̇ (β ^̃ c)
  RNFMins (d ^ AddTop (dbl c)) $ powerRNFMinsSym c β

-- ┌─────┐
-- │β ^̃ c│
-- └─────┘
powerRNFMinsSym ∷ ℚ → 𝑃 RNFSums → 𝑃 RNFSums
powerRNFMinsSym c β = 
  -- β ^̃ c = ⨅{ γ̇ | γ̇ ∈ β } ^ c
  --       ≜ ⨅{ γ̇ ^̃ c | γ̇ ∈ β }
  pow $ do
    γ̇ ← iter β
    return $ powerRNFSums c γ̇

-- FIXED --

-- ┌─────┐
-- │γ̇ ^̃ c│
-- └─────┘
powerRNFSums ∷ ℚ → RNFSums → AddTop RNFSums
powerRNFSums c γ̇ = case γ̇ of
    RNFSums Bot (stream → (uncons𝑆 → Some ((δ̇ :* d) :* (uncons𝑆 → None)))) → do
      undefined
      -- RNFSums Bot $ powerRNFProds c δ̇ ↦ (d ^ AddTop (dbl c))
    _ → _ $ reinterpSumsFP $ oneProd $ RNFProds (γ̇ ↦ c) dø

powerRNFProds ∷ ℚ → RNFProds → AddTop RNFSums
powerRNFProds c (RNFProds δ̂ δ̌) =
  reinterpSumsFP $
    let δ̂' = sum $ do
          γ̇ :* d ← iter δ̂
          return $ γ̇ ↦ (c × d)
        δ̌' = sum $ do
          ε :* d ← iter δ̌
          return $ ε ↦ (c × d)
    in oneProd $ RNFProds δ̂' δ̌'

-- -- ┌────┐
-- -- │1/̃ γ̇│
-- -- └────┘
-- invRNFSums ∷ RNFSums → RNFSums
-- invRNFSums γ̇ = oneProd $ RNFProds (γ̇ ↦ neg one) dø
-- 
-- -- ┌─────┐
-- -- │γ̇ ^̃ c│
-- -- └─────┘
-- posPowerRNFSums ∷ 𝕋 → RNFSums → RNFSums
-- posPowerRNFSums c γ̇ 
--   | c > one = undefined -- prodRNFSums γ̇ $ posPowerRNFSums (c - one) γ̇
--   | otherwise = undefined -- oneProd $ RNFProds (γ̇ ↦ rat c) dø

-- ┌─────┐
-- │e ^̃ c│
-- └─────┘
powerRNF ∷ ℚ → RNF → RNF
powerRNF c e = case e of
  -- ⊥ ^̃ c ≜ ⊥
  ConstantRNF BotBT → ConstantRNF BotBT
  -- ⊤ ^̃ c ≜ ⊤
  ConstantRNF TopBT → ConstantRNF TopBT
  -- c′ ^̃ c ≜ c′ ^ c
  ConstantRNF (AddBT c') → ConstantRNF $ AddBT $ c' ^ dbl c
  -- α̇ ^̃ c
  SymRNF α̇ → SymRNF $ powerRNFMaxs c α̇

-- -----------------
-- -- EXPONENTIAL --
-- -----------------
-- 
-- -- ┌────┐
-- -- │𝑒^̃ α│
-- -- └────┘
-- efnRNFMaxs ∷ 𝑃 RNFMins → 𝑃 RNFMins
-- efnRNFMaxs α =
--   -- 𝑒^̃ α ≜ { 𝑒^̃ (c ⊓̇ β) | c ⊓̇ β ∈ α }
--   --      = { (𝑒 ^ c) ⊓̇ (𝑒^̃ β)) | c ⊓̇ β ∈ α }
--   pow $ do
--     RNFMins c β ← iter α
--     return $ RNFMins (exp c) $ efnRNFMins β
-- 
-- -- ┌────┐
-- -- │𝑒^̃ β│
-- -- └────┘
-- efnRNFMins ∷ 𝑃 RNFSums → 𝑃 RNFSums
-- efnRNFMins β = 
--   -- 𝑒^̃ β ≜ { 𝑒^̃(c +̇ γ) | c +̇ γ ∈ β }
--   --      = { 0 +̇ {(𝑒^c) ×̇ (𝑒^̃ γ) | c +̇ γ ∈ β }}
--   pow $ do
--     RNFSums c γ ← iter β
--     return $ RNFSums Bot $ RNFProds (efnRNFSums γ) ↦ AddTop (elimAddBot 1.0 exp c)
-- 
-- -- ┌────┐
-- -- │𝑒^̃ γ│
-- -- └────┘
-- efnRNFSums ∷ RNFProds ⇰ AddTop 𝔻 → RNFAtom ⇰ ℚ
-- efnRNFSums γ =
--   -- 𝑒^̃ γ ≜ Π{ 𝑒^̃ (c ×̇ δ) | c ×̇ δ ∈ γ }
--   sum $ do
--     RNFProds δ :* c ← iter γ
--     return $ EfnRA c (RNFProds δ) ↦ one
-- 
-- -- ┌────┐
-- -- │𝑒^̃ e│
-- -- └────┘
-- efnRNF ∷ RNF → RNF
-- efnRNF e = 
--   case e of
--   -- 𝑒^̃ ⊥ ≜ ⊥
--   ConstantRNF BotBT → ConstantRNF BotBT
--   -- 𝑒^̃ ⊤ ≜ ⊤
--   ConstantRNF TopBT → ConstantRNF TopBT
--   -- 𝑒^̃ c ≜ 𝑒 ^ c
--   ConstantRNF (AddBT c) → ConstantRNF $ AddBT $ exp c
--   -- (c ⊔̇ α) ^̃ q ≜ (c ^ q) ⊔̇ (α ^̃ q)
--   SymRNF (RNFMaxs c α) → SymRNF $ RNFMaxs (exp c) $ efnRNFMaxs α
-- 
-- ---------
-- -- LOG --
-- ---------
-- 
-- -- ┌────┐
-- -- │㏒̃ α│
-- -- └────┘
-- logRNFMaxs ∷ 𝑃 RNFMins → 𝑃 RNFMins
-- logRNFMaxs α =
--   -- ㏒̃ α ≜ { ㏒̃ (c ⊓̇ β) | c ⊓̇ β ∈ α }
--   --      = { (㏒̃^ c) ⊓̇ (㏒̃ β)) | c ⊓̇ β ∈ α }
--   pow $ do
--     RNFMins c β ← iter α
--     return $ RNFMins (exp c) $ logRNFMins β
-- 
-- -- ┌────┐
-- -- │㏒̃ β│
-- -- └────┘
-- logRNFMins ∷ 𝑃 RNFSums → 𝑃 RNFSums
-- logRNFMins β = 
--   -- ㏒̃ β ≜ { ㏒̃ (c +̇ γ) | c +̇ γ ∈ β }
--   --      = { ㏒̇ (c +̇ γ) | c +̇ γ ∈ β }
--   pow $ do
--     RNFSums c γ ← iter β
--     return $ RNFSums Bot $ RNFProds (LogRA (RNFSums c γ) ↦ one) ↦ AddTop 1.0
-- 
-- -- -- ┌────┐
-- -- -- │㏒ γ│
-- -- -- └────┘
-- -- logRNFSums ∷ RNFProds ⇰ AddTop 𝔻 → RNFAtom ⇰ ℚ
-- -- logRNFSums γ =
-- --   -- ㏒ γ ≜ Π{ ㏒ (c ×̇ δ) | c ×̇ δ ∈ γ }
-- --   sum $ do
-- --     RNFProds δ :* c ← iter γ
-- --     undefined
-- --     -- return $ LogRA c (RNFProds δ) ↦ one
-- 
-- -- ┌────┐
-- -- │㏒ e│
-- -- └────┘
-- logRNF ∷ RNF → RNF
-- logRNF e = 
--   case e of
--   -- ㏒ ⊥ ≜ ⊥
--   ConstantRNF BotBT → ConstantRNF BotBT
--   -- ㏒ ⊤ ≜ ⊤
--   ConstantRNF TopBT → ConstantRNF TopBT
--   -- ㏒ c ≜ ㏒^ c
--   ConstantRNF (AddBT c) → ConstantRNF $ AddBT $ exp c
--   -- (c ⊔̇ α) ^̃ q ≜ (c ^ q) ⊔̇ (α ^̃ q)
--   SymRNF (RNFMaxs c α) → SymRNF $ RNFMaxs (exp c) $ logRNFMaxs α

