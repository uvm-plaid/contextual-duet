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
  { rnfProdsSymbolic ∷ RNFAtom ⇰ ℚ -- (at least one inside)
  }
  deriving (Eq,Ord,Show)

-- ε ∈ RNFAtom
data RNFAtom =
    VarRA 𝕏
  | InvRA RNFSums
  | RootRA ℕ RNFSums
  | LogRA RNFSums
  | EfnRA (AddTop 𝔻) RNFProds
  deriving (Eq,Ord,Show)

-------------
-- HELPERS --
-------------

oneAtom ∷ RNFAtom → RNFProds
oneAtom ε = RNFProds $ ε ↦ one

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

--------------------
-- RATIONAL POWER --
--------------------

-- ┌─────┐
-- │α ^̃ q│
-- └─────┘
powerRNFMaxs ∷ ℚ → 𝑃 RNFMins → 𝑃 RNFMins
powerRNFMaxs q α =
  -- α ^̃ q ≜ { (c ⊓̇ β) ^̃ q | c ⊓̇ β ∈ α }
  --       = { (c ^ q) ⊓̇ (β ^̃ q)) | c ⊓̇ β ∈ α }
  pow $ do
    RNFMins c β ← iter α
    return $ RNFMins (c ^ AddTop (dbl q)) $ powerRNFMins q β

-- ┌─────┐
-- │β ^̃ q│
-- └─────┘
powerRNFMins ∷ ℚ → 𝑃 RNFSums → 𝑃 RNFSums
powerRNFMins q β = 
  -- a ^̃ q ≜ { (c +̇ γ) ^̃ q | c +̇ γ ∈ β }
  pow $ do
    γ̇ ← iter β
    return $ powerRNFSums q γ̇

-- ┌─────┐
-- │γ̇ ^̃ c│
-- └─────┘
powerRNFSums ∷ ℚ → RNFSums → RNFSums
powerRNFSums q (RNFSums c γ) = case (c,tohs $ list γ) of
  -- (0 +̇ {c ×̇ δ}) ^̃ q ≜ 0 +̇ {(c ×̇ δ) ^̃ q}
  (Bot,[(RNFProds δ,c')]) → RNFSums Bot $ RNFProds (powerRNFProds q δ) ↦ (c' ^ AddTop (dbl q))
  _ → loop q (RNFSums c γ)
  where
    loop ∷ ℚ → RNFSums → RNFSums
    loop q' (RNFSums c₁ γ₁)
      -- (c +̇ γ) ^̃ 0 ≜ 0 +̇ {}
      | q' ≡ zero = RNFSums Bot dø
      -- (c +̇ γ) ^̃ (-q) ≜ 1/̇ ((c +̇ γ) ^̃ q)
      | q' < zero = 
        let γ̇ = loop (neg q') $ RNFSums c₁ γ₁
        in RNFSums Bot $ RNFProds (InvRA γ̇ ↦ one) ↦ AddTop 1.0
      -- (c +̇ γ) ^̃ (1+q) ≜ (c +̇ γ) ×̃ (c +̇ γ) ^̃ q
      | q' ≥ one  = 
          let RNFSums c₂ γ₂ = loop (q' - one) $ RNFSums c₁ γ₁
          in RNFSums (c₁ × c₂) $ sum
            [ flip (elimAddBot dø) c₂ $ \ c₂' → prodRNFSumsConstant c₂' γ₁
            , flip (elimAddBot dø) c₁ $ \ c₁' → prodRNFSumsConstant c₁' γ₂
            , prodRNFSums γ₁ γ₂
            ]
      -- 0 < q < one
      -- (c +̇ γ) ^̃ (1/n) ≜ n√̇ (c +̇ γ)
      | otherwise =
        RNFSums Bot $ RNFProds (RootRA (abs (ratNum (one / q))) (RNFSums c γ) ↦ one) ↦ AddTop 1.0

-- ┌─────┐
-- │δ ^̃ c│
-- └─────┘
powerRNFProds ∷ ℚ → RNFAtom ⇰ ℚ → RNFAtom ⇰ ℚ 
powerRNFProds q δ = 
  -- δ ^̃ q ≜ { (ε ^̇ c) ^̃ q | ε ^̇ c ∈ δ }
  --       ≜ { ε ^̇ (c × q) | ε ^̇ c ∈ δ }
  sum $ do
    ε :* c ← iter δ
    return $ ε ↦ (c × q)

-- ┌─────┐
-- │e ^̃ q│
-- └─────┘
powerRNF ∷ ℚ → RNF → RNF
powerRNF q e = case e of
  -- ⊥ ^̃ q ≜ ⊥
  ConstantRNF BotBT → ConstantRNF BotBT
  -- ⊤ ^̃ q ≜ ⊤
  ConstantRNF TopBT → ConstantRNF TopBT
  -- c ^̃ q ≜ c ^ q
  ConstantRNF (AddBT c) → ConstantRNF $ AddBT $ c ^ dbl q
  -- (c ⊔̇ α) ^̃ q ≜ (c ^ q) ⊔̇ (α ^̃ q)
  SymRNF (RNFMaxs c α) → SymRNF $ RNFMaxs (c ^ AddBot (dbl q)) $ powerRNFMaxs q α

-----------------
-- EXPONENTIAL --
-----------------

-- ┌────┐
-- │𝑒^̃ α│
-- └────┘
efnRNFMaxs ∷ 𝑃 RNFMins → 𝑃 RNFMins
efnRNFMaxs α =
  -- 𝑒^̃ α ≜ { 𝑒^̃ (c ⊓̇ β) | c ⊓̇ β ∈ α }
  --      = { (𝑒 ^ c) ⊓̇ (𝑒^̃ β)) | c ⊓̇ β ∈ α }
  pow $ do
    RNFMins c β ← iter α
    return $ RNFMins (exp c) $ efnRNFMins β

-- ┌────┐
-- │𝑒^̃ β│
-- └────┘
efnRNFMins ∷ 𝑃 RNFSums → 𝑃 RNFSums
efnRNFMins β = 
  -- 𝑒^̃ β ≜ { 𝑒^̃(c +̇ γ) | c +̇ γ ∈ β }
  --      = { 0 +̇ {(𝑒^c) ×̇ (𝑒^̃ γ) | c +̇ γ ∈ β }}
  pow $ do
    RNFSums c γ ← iter β
    return $ RNFSums Bot $ RNFProds (efnRNFSums γ) ↦ AddTop (elimAddBot 1.0 exp c)

-- ┌────┐
-- │𝑒^̃ γ│
-- └────┘
efnRNFSums ∷ RNFProds ⇰ AddTop 𝔻 → RNFAtom ⇰ ℚ
efnRNFSums γ =
  -- 𝑒^̃ γ ≜ Π{ 𝑒^̃ (c ×̇ δ) | c ×̇ δ ∈ γ }
  sum $ do
    RNFProds δ :* c ← iter γ
    return $ EfnRA c (RNFProds δ) ↦ one

-- ┌────┐
-- │𝑒^̃ e│
-- └────┘
efnRNF ∷ RNF → RNF
efnRNF e = 
  case e of
  -- 𝑒^̃ ⊥ ≜ ⊥
  ConstantRNF BotBT → ConstantRNF BotBT
  -- 𝑒^̃ ⊤ ≜ ⊤
  ConstantRNF TopBT → ConstantRNF TopBT
  -- 𝑒^̃ c ≜ 𝑒 ^ c
  ConstantRNF (AddBT c) → ConstantRNF $ AddBT $ exp c
  -- (c ⊔̇ α) ^̃ q ≜ (c ^ q) ⊔̇ (α ^̃ q)
  SymRNF (RNFMaxs c α) → SymRNF $ RNFMaxs (exp c) $ efnRNFMaxs α

---------
-- LOG --
---------

-- ┌────┐
-- │㏒̃ α│
-- └────┘
logRNFMaxs ∷ 𝑃 RNFMins → 𝑃 RNFMins
logRNFMaxs α =
  -- ㏒̃ α ≜ { ㏒̃ (c ⊓̇ β) | c ⊓̇ β ∈ α }
  --      = { (㏒̃^ c) ⊓̇ (㏒̃ β)) | c ⊓̇ β ∈ α }
  pow $ do
    RNFMins c β ← iter α
    return $ RNFMins (exp c) $ logRNFMins β

-- ┌────┐
-- │㏒̃ β│
-- └────┘
logRNFMins ∷ 𝑃 RNFSums → 𝑃 RNFSums
logRNFMins β = 
  -- ㏒̃ β ≜ { ㏒̃ (c +̇ γ) | c +̇ γ ∈ β }
  --      = { ㏒̇ (c +̇ γ) | c +̇ γ ∈ β }
  pow $ do
    RNFSums c γ ← iter β
    return $ RNFSums Bot $ RNFProds (LogRA (RNFSums c γ) ↦ one) ↦ AddTop 1.0

-- -- ┌────┐
-- -- │㏒ γ│
-- -- └────┘
-- logRNFSums ∷ RNFProds ⇰ AddTop 𝔻 → RNFAtom ⇰ ℚ
-- logRNFSums γ =
--   -- ㏒ γ ≜ Π{ ㏒ (c ×̇ δ) | c ×̇ δ ∈ γ }
--   sum $ do
--     RNFProds δ :* c ← iter γ
--     undefined
--     -- return $ LogRA c (RNFProds δ) ↦ one

-- ┌────┐
-- │㏒ e│
-- └────┘
logRNF ∷ RNF → RNF
logRNF e = 
  case e of
  -- ㏒ ⊥ ≜ ⊥
  ConstantRNF BotBT → ConstantRNF BotBT
  -- ㏒ ⊤ ≜ ⊤
  ConstantRNF TopBT → ConstantRNF TopBT
  -- ㏒ c ≜ ㏒^ c
  ConstantRNF (AddBT c) → ConstantRNF $ AddBT $ exp c
  -- (c ⊔̇ α) ^̃ q ≜ (c ^ q) ⊔̇ (α ^̃ q)
  SymRNF (RNFMaxs c α) → SymRNF $ RNFMaxs (exp c) $ logRNFMaxs α
