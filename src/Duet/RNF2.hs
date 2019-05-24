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
  | EfnRA (AddTop 𝔻) RNFProds
  deriving (Eq,Ord,Show)

makePrettySum ''RNF
makePrettySum ''RNFMaxs
makePrettySum ''RNFMins
makePrettySum ''RNFSums
makePrettySum ''RNFProds
makePrettySum ''RNFAtom

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

pifEmpty ∷ b → (𝑃 a → b) → 𝑃 a → b
pifEmpty y f xs
  | isEmpty xs = y
  | otherwise = f xs

difEmpty ∷ a → (k ⇰ v → a) → k ⇰ v → a
difEmpty x f kvs
  | isEmpty kvs = x
  | otherwise = f kvs

-------------
-- LITERAL --
-------------

dblRNF ∷ 𝔻 → RNF
dblRNF d
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

-- CONSTANT --

-- ┌─────┐
-- │c ⊔̃ α̇│
-- └─────┘
maxRNFMaxsConstant ∷ 𝔻 → RNFMaxs → RNFMaxs
maxRNFMaxsConstant c (RNFMaxs d α) =
  -- c ⊔̃ (d ⊔̇ α) ≜ (c ⊔ d) ⊔̇ α
  RNFMaxs (AddBot c ⊔ d) α

-- BINARY --

-- ┌─────┐
-- │α̇ ⊔̃ α̇│
-- └─────┘
maxRNFMaxs ∷ RNFMaxs → RNFMaxs → RNFMaxs
maxRNFMaxs (RNFMaxs d₁ α₁) (RNFMaxs d₂ α₂) =
  -- (d₁ ⊔̇ α₁) ⊔̃ (d₂ ⊔̇ α₂) ≜ (d₁ ⊔ d₂) ⊔̇ (α₁ ∪ α₂)
  RNFMaxs (d₁ ⊔ d₂) $ α₁ ∪ α₂

-- RNF --

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

-- CONSTANT --

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

-- BINARY --

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

-- RNF --

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

-- CONSTANT --

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

-- BINARY --

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

-- RNF --

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

-- TOP --

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
  pow ^$ mapM id $ do
    β̇ ← iter α
    return $ prodRNFMinsTop β̇

-- ┌─────┐
-- │⊤ ×̃ β̇│
-- └─────┘
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
  pifEmpty Top AddTop $ pow $ do
   γ̇ ← iter β
   elimAddTop null return $ prodRNFSumsTop γ̇

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

-- CONSTANT --

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
  -- c ×̃ γ = c × ∏{ δ̇ ×̈ d | δ̇ ×̈ d ∈ γ }
  --       ≜ ∏{ δ̇ ×̈ (c × d) | δ̇ ×̈ d ∈ γ }
  sum $ do
    δ̇ :* d ← iter γ
    return $ δ̇ ↦ (AddTop c × d)

-- BINARY --

-- ┌─────┐
-- │α̇ ×̃ α̇│
-- └─────┘
prodRNFMaxs ∷ RNFMaxs → RNFMaxs → AddTop RNFMaxs
prodRNFMaxs (RNFMaxs d₁ α₁) (RNFMaxs d₂ α₂) =
  -- (d₁ ⊔̇ α₁) ×̃ (d₂ ⊔̇ α₂) ≜ (d₁ × d₂) ⊔̇ ⋃{ d₁ ×̃ α₂ , d₂ ×̃ α₁ , α₁ ×̃ α₂ }
  RNFMaxs (d₁ × d₂) ∘ joins ^$ mapM id
    [ return $ flip (elimAddBot pø) d₁ $ \ d₁' → prodRNFMaxsConstantSym d₁' α₂
    , return $ flip (elimAddBot pø) d₂ $ \ d₂' → prodRNFMaxsConstantSym d₂' α₁
    , prodRNFMaxsSym α₁ α₂
    ]

-- ┌─────┐
-- │α ×̃ α│
-- └─────┘
prodRNFMaxsSym ∷ 𝑃 RNFMins → 𝑃 RNFMins → AddTop (𝑃 RNFMins)
prodRNFMaxsSym α₁ α₂ =
  -- α₁ ×̃ α₂ = ⨆{ β̇ | β̇ ∈ α₁} × ⨆{ β̇ | β̇ ∈ α₂}
  --         ≜ ⨆{ β̇₁ ×̃ β̇₂ | β̇₁ ∈ α₁ , β̇₂ ∈ α₂ }
  pow ^$ mapM id $ do
    β̇₁ ← iter α₁
    β̇₂ ← iter α₂
    return $ prodRNFMins β̇₁ β̇₂


-- ┌─────┐
-- │β̇ ×̃ β̇│
-- └─────┘
prodRNFMins ∷ RNFMins → RNFMins → AddTop RNFMins
prodRNFMins (RNFMins d₁ β₁) (RNFMins d₂ β₂) =
  -- (d₁ ⊓̇ β₁) ×̃ (d₂ ⊓̇ β₂) ≜ (d₁ × d₂) ⊓̇ ⋃{ d₁ ×̃ β₂ , d₂ ×̃ β₁ , β₁ ×̃ β₂ }
  RNFMins (d₁ × d₂) ^$ pifEmpty Top AddTop $ joins
    [ flip (elimAddTop pø) d₁ $ \ d₁' → prodRNFMinsConstantSym d₁' β₂
    , flip (elimAddTop pø) d₂ $ \ d₂' → prodRNFMinsConstantSym d₂' β₁
    , elimAddTop pø id $ prodRNFMinsSym β₁ β₂
    ]

-- ┌─────┐
-- │β ×̃ β│
-- └─────┘
prodRNFMinsSym ∷ 𝑃 RNFSums → 𝑃 RNFSums → AddTop (𝑃 RNFSums)
prodRNFMinsSym β₁ β₂ =
  -- β₁ ×̃ β₂ = ⨅{ γ̇ | γ̇ ∈ β₁ } × ⨅{ γ̇ | γ̇ ∈ β₁ }
  --         ≜ ⨅{ γ̇₁ ×̃ γ̇₂ | γ̇₁ ∈ β₁ , γ̇₂ ∈ β₂ }
  pifEmpty Top AddTop $ pow $ do
    γ̇₁ ← iter β₁
    γ̇₂ ← iter β₂
    elimAddTop null return $ prodRNFSums γ̇₁ γ̇₂

-- ┌─────┐
-- │γ̇ ×̃ γ̇│
-- └─────┘
prodRNFSums ∷ RNFSums → RNFSums → AddTop RNFSums
prodRNFSums (RNFSums d₁ γ₁) (RNFSums d₂ γ₂) = do
  -- (d₁ +̇ γ₁) ×̃ (d₁ +̇ γ₂) = (d₁ × d₂) + (d₁ × γ₂) + (d₂ × γ₁) + (γ₁ × γ₂)
  --                       = (d₁ × d₂) + (d₁ × γ₂) + (d₂ × γ₁) + (d₃ + γ₃) where (d +̇ γ₃) = γ₁ × γ₂
  --                       ≜ (d₁ × d₂ + d₃) + (d₁ × γ₂) + (d₂ × γ₁) + γ₃   where (d +̇ γ₃) = γ₁ × γ₂
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
  --         = ∑{ γ̇ × (d₁ × d₂) | γ̇ ∈ (δ̇₁ ×̃ δ̇₂) , δ̇₁ ×̈ d₁ ∈ γ₁ , δ̇₂ ×̈ d₂ ∈ γ₂ }
  --
  mfoldWith (map tohs $ iter γ₁ ⧆ iter γ₂) (RNFSums Bot dø) $ \ ((δ̇₁,d₁),(δ̇₂,d₂)) γ̇ᵢ → do
    d₁₂ ← d₁ × d₂
    γ̇ ← prodRNFProds δ̇₁ δ̇₂
    return $ sumRNFSums γ̇ᵢ $ prodRNFSumsConstant d₁₂ γ̇

-- ┌─────┐
-- │δ̇ ×̃ δ̇│
-- └─────┘
prodRNFProds ∷ RNFProds → RNFProds → AddTop RNFSums
prodRNFProds (RNFProds δ̂₁ δ̌₁) (RNFProds δ̂₂ δ̌₂) = do
  -- (δ̂₁ ×̇ δ̌₁) ×̃ (δ̂₂ ×̇ δ̌₂) ≜ (δ̂₁ ×̃ δ̂₂) ×̇ (δ̌₂ ⊎ δ̌₂)
  γ̇ ← prodRNFIrreds δ̂₁ δ̂₂
  return $ RNFSums Bot $ prodRNFSumsAtoms (δ̌₁ ⊎ δ̌₂) γ̇

-- ┌─────┐
-- │δ̂ ×̃ δ̂│
-- └─────┘
prodRNFIrreds ∷ RNFSums ⇰ ℚ → RNFSums ⇰ ℚ → AddTop RNFSums
prodRNFIrreds δ̂₁ δ̂₂ =
  -- δ̂₁ ×̃ δ̂₂ = ∏{γ̇ ^̇ d | γ̇ ^̇ d ∈ δ̂₁} × ∏{γ̇ ^̇ d | γ̇ ^̇ d ∈ δ̂₂}
  --         ≜ ∏{γ̇ ^̃ d | γ̇ ^̇ d ∈ (δ̂₁ ⊎ δ̂₂)}
  let k₁ = keys δ̂₁
      k₂ = keys δ̂₂
      γ̇₀ = oneProd $ RNFProds (without k₂ δ̂₁ ⊎ without k₁ δ̂₂) dø
      δ̂s = interWith (+) δ̂₁ δ̂₂
  in
  mfoldWith δ̂s γ̇₀ $ \ (γ̇ :* d) γ̇ᵢ → do
    γ̇' ← powerRNFSums d γ̇
    prodRNFSums γ̇ᵢ γ̇'

-- ┌─────┐
-- │δ̌ ×̃ γ̇│
-- └─────┘
prodRNFSumsAtoms ∷ RNFAtom ⇰ ℚ → RNFSums → RNFProds ⇰ AddTop 𝔻
prodRNFSumsAtoms δ̌ (RNFSums d γ) =
  -- δ̌ ×̃ (d +̇ γ) ≜ δ̌ ×̃ d + δ̌ ×̃ γ
  sum
    [ flip (elimAddBot dø) d $ \ d' → RNFProds dø δ̌ ↦ AddTop d'
    , prodRNFSumsAtomsSym δ̌ γ
    ]

prodRNFSumsAtomsSym ∷ RNFAtom ⇰ ℚ → RNFProds ⇰ AddTop 𝔻 → RNFProds ⇰ AddTop 𝔻
prodRNFSumsAtomsSym δ̌ γ =
  -- δ̌ ×̃ γ = δ̌ × ∑{ δ̇ ×̈ d | δ̇ ×̈ d ∈ γ }
  --       ≜ ∑{ (δ̌ ×̃ δ̇) ×̇ d | δ̇ ×̈ d ∈ γ }
  sum $ do
    δ̇ :* d ← iter γ
    return $ prodRNFProdsAtoms δ̌ δ̇ ↦ d

prodRNFProdsAtoms ∷ RNFAtom ⇰ ℚ → RNFProds → RNFProds
prodRNFProdsAtoms δ̌ (RNFProds δ̂' δ̌') = RNFProds δ̂' $ δ̌' ⊎ δ̌

-- RNF --

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
  (SymRNF α̇₁,SymRNF α̇₂) → elimAddTop (ConstantRNF TopBT) SymRNF $ prodRNFMaxs α̇₁ α̇₂

-----------
-- POWER --
-----------

-- ┌─────┐
-- │α̇ ^̃ c│
-- └─────┘
powerRNFMaxs ∷ ℚ → RNFMaxs → AddTop RNFMaxs
powerRNFMaxs c (RNFMaxs d α) = do
  -- (d ⊔̇ α) ^̃ c ≜ (d ^ c) ⊔̇ (α ^̃ c)
  RNFMaxs d'' α' ← powerRNFMaxsSym c α
  let d' = (d ^ AddBot (dbl c))
  return $ RNFMaxs (d' ⊔ d'') α'

-- ┌─────┐
-- │α ^̃ c│
-- └─────┘
powerRNFMaxsSym ∷ ℚ → 𝑃 RNFMins → AddTop RNFMaxs
powerRNFMaxsSym c α =
  -- α ^̃ c = ⨆{ β̇ | β̇ ∈ α } ^ c
  --       ≜ ⨆{ β̇ ^̃ c | β̇ ∈ α}
  mfoldWith (iter α) (RNFMaxs Bot pø) $ \ β̇ (RNFMaxs dᵢ αᵢ) →
    case powerRNFMins c β̇ of
      Inl d' → do
        d'' ← d'
        return $ RNFMaxs (dᵢ ⊔ AddBot d'') αᵢ
      Inr β̇' →
        return $ RNFMaxs dᵢ $ single β̇' ∪ αᵢ

-- ┌─────┐
-- │β̇ ^̃ c│
-- └─────┘
powerRNFMins ∷ ℚ → RNFMins → AddTop 𝔻 ∨ RNFMins
powerRNFMins c (RNFMins d β) =
  -- (d ⊓̇ β) ^̃ c = (d ^ c) ⊓̇ (β ^̃ c)
  case powerRNFMinsSym c β of
    Top → Inl $ d ^ AddTop (dbl c)
    AddTop β' → Inr $ RNFMins (d ^ AddTop (dbl c)) β'

-- ┌─────┐
-- │β ^̃ c│
-- └─────┘
powerRNFMinsSym ∷ ℚ → 𝑃 RNFSums → AddTop (𝑃 RNFSums)
powerRNFMinsSym c β =
  -- β ^̃ c = ⨅{ γ̇ | γ̇ ∈ β } ^ c
  --       ≜ ⨅{ γ̇ ^̃ c | γ̇ ∈ β }
  pifEmpty Top AddTop $ pow $ do
    γ̇ ← iter β
    elimAddTop null return $ powerRNFSums c γ̇

-- ┌─────┐
-- │γ̇ ^̃ c│
-- └─────┘
powerRNFSums ∷ ℚ → RNFSums → AddTop RNFSums
powerRNFSums c γ̇ = case γ̇ of
  RNFSums Bot (stream → (uncons𝑆 → Some ((δ̇ :* d) :* (uncons𝑆 → None)))) → do
    γ̇' ← powerRNFProds c δ̇
    elimAddTop prodRNFSumsTop (kreturn ∘ prodRNFSumsConstant) d γ̇'
  _ → powerRNFSumsIrred c γ̇

-- ┌─────┐
-- │γ̇ ^̃ c│
-- └─────┘
powerRNFSumsIrred ∷ ℚ → RNFSums → AddTop RNFSums
powerRNFSumsIrred c γ̇
  | c ≡ zero = return $ RNFSums (AddBot 1.0) dø
  | c ≥ one = prodRNFSums γ̇ *$ powerRNFSumsIrred (c - one) γ̇
  | c < zero = invRNFSums *$ powerRNFSumsIrred (one / c) γ̇
  | otherwise = return $ oneProd $ RNFProds (γ̇ ↦ c) dø

-- ┌────┐
-- │1/̃ γ̇│
-- └────┘
invRNFSums ∷ RNFSums → AddTop RNFSums
invRNFSums γ̇ = case γ̇ of
  RNFSums Bot (stream → (uncons𝑆 → Some ((δ̇ :* d) :* (uncons𝑆 → None)))) → do
    γ̇' ← powerRNFProds (neg one) δ̇
    elimAddTop prodRNFSumsTop (kreturn ∘ prodRNFSumsConstant) d γ̇'
  _ → return $ oneProd $ RNFProds (γ̇ ↦ neg one) dø

-- ┌─────┐
-- │δ̇ ^̃ c│
-- └─────┘
powerRNFProds ∷ ℚ → RNFProds → AddTop RNFSums
powerRNFProds c (RNFProds δ̂ δ̌) =
  let δ̌' = powerRNFAtoms c δ̌
  in
  mfoldWith (iter δ̂) (oneProd $ RNFProds dø δ̌') $ \ (γ̇ :* d) γ̇ᵢ → do
    γ̇' ← powerRNFSumsIrred (c × d) γ̇
    prodRNFSums γ̇ᵢ γ̇'

powerRNFAtoms ∷ ℚ → RNFAtom ⇰ ℚ → RNFAtom ⇰ ℚ
powerRNFAtoms c δ̌ = sum $ do
  ε :* d ← iter δ̌
  return $ ε ↦ (c × d)

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
  SymRNF α̇ → elimAddTop (ConstantRNF TopBT) SymRNF $ powerRNFMaxs c α̇

-----------------
-- EXPONENTIAL --
-----------------

-- ┌────┐
-- │𝑒^̃ α̇│
-- └────┘
efnRNFMaxs ∷ RNFMaxs → RNFMaxs
efnRNFMaxs (RNFMaxs c α) =
  -- 𝑒^̃ (c ⊔̇ α) ≜ (𝑒^̃ c) ⊔̇ (𝑒^̃ α)
  RNFMaxs (exp c) $ efnRNFMaxsSym α

-- ┌────┐
-- │𝑒^̃ α│
-- └────┘
efnRNFMaxsSym ∷ 𝑃 RNFMins → 𝑃 RNFMins
efnRNFMaxsSym α =
  -- 𝑒^̃ α ≜ ⨆{ 𝑒^̃ (c ⊓̇ β) | c ⊓̇ β ∈ α }
  --      = ⨆{ (𝑒 ^ c) ⊓̇ (𝑒^̃ β)) | c ⊓̇ β ∈ α }
  pow $ do
    β̇ ← iter α
    return $ efnRNFMins β̇

-- ┌────┐
-- │𝑒^̃ β̇│
-- └────┘
efnRNFMins ∷ RNFMins → RNFMins
efnRNFMins (RNFMins c β) =
  -- 𝑒^̃ (c ⊓̇ α) ≜ (𝑒^̃ c) ⊓̇ (𝑒^̃ α)
  RNFMins (exp c) $ efnRNFMinsSym β

-- ┌────┐
-- │𝑒^̃ β│
-- └────┘
efnRNFMinsSym ∷ 𝑃 RNFSums → 𝑃 RNFSums
efnRNFMinsSym β =
  -- 𝑒^̃ β ≜ ⨅{ 𝑒^̃(c +̇ γ) | c +̇ γ ∈ β }
  --      = ⨅{ 0 +̇ {(𝑒^c) ×̇ (𝑒^̃ γ) | c +̇ γ ∈ β }}
  pow $ do
    γ̇ ← iter β
    return $ efnRNFSums γ̇

-- ┌────┐
-- │𝑒^̃ γ̇│
-- └────┘
efnRNFSums ∷ RNFSums → RNFSums
efnRNFSums (RNFSums c γ) = 
  -- 𝑒^̃ (c +̇ γ) ≜ (e^̃ c) ×̇ ∅ ×̇ (e^̃ γ)
  RNFSums Bot $ RNFProds dø (efnRNFSumsSym γ) ↦ AddTop (elimAddBot 1.0 exp c)

-- ┌────┐
-- │𝑒^̃ γ│
-- └────┘
efnRNFSumsSym ∷ RNFProds ⇰ AddTop 𝔻 → RNFAtom ⇰ ℚ
efnRNFSumsSym γ =
  -- 𝑒^̃ γ ≜ Π{ 𝑒^̃ (c ×̇ δ̂ ×̇ δ̌) | c ×̇ δ̂ ×̇ δ̌ ∈ γ }
  sum $ do
    RNFProds δ̂ δ̌ :* c ← iter γ
    return $ EfnRA c (RNFProds δ̂ δ̌) ↦ one

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
  SymRNF α̇ → SymRNF $ efnRNFMaxs α̇

---------
-- LOG --
---------

-- ┌────┐
-- │㏒ α̇│
-- └────┘
logRNFMaxs ∷ RNFMaxs → AddTop RNFMaxs
logRNFMaxs (RNFMaxs c α) = do
  -- ㏒ (c ⊔̇ α) ≜ (㏒ c) ⊔̇ (㏒ α)
  α' ← logRNFMaxsSym α
  return $ RNFMaxs (log c) α'

-- ┌────┐
-- │㏒ α│
-- └────┘
logRNFMaxsSym ∷ 𝑃 RNFMins → AddTop (𝑃 RNFMins)
logRNFMaxsSym α =
  -- ㏒ α ≜ ⨆{ ㏒ (c ⊓̇ β) | c ⊓̇ β ∈ α }
  --      = ⨆{ (㏒^ c) ⊓̇ (㏒ β)) | c ⊓̇ β ∈ α }
  pow ^$ mapM id $ do
    β̇ ← iter α
    return $ logRNFMins β̇

-- ┌────┐
-- │㏒ β̇│
-- └────┘
logRNFMins ∷ RNFMins → AddTop RNFMins
logRNFMins (RNFMins c β) = do
  -- ㏒ (c ⊓̇ α) ≜ (㏒ c) ⊓̇ (㏒ α)
  β' ← logRNFMinsSym β
  return $ RNFMins (log c) β'

-- ┌────┐
-- │㏒ β│
-- └────┘
logRNFMinsSym ∷ 𝑃 RNFSums → AddTop (𝑃 RNFSums)
logRNFMinsSym β =
  -- ㏒ β ≜ ⨅{ ㏒(c +̇ γ) | c +̇ γ ∈ β }
  pow ^$ mapM id $ do
    γ̇ ← iter β
    return $ logRNFSums γ̇

-- ┌────┐
-- │㏒ γ̇│
-- └────┘
logRNFSums ∷ RNFSums → AddTop RNFSums
logRNFSums γ̇ = case γ̇ of 
  RNFSums Bot (stream → (uncons𝑆 → Some ((δ̇ :* d) :* (uncons𝑆 → None)))) → do
    d' ← d
    return $ RNFSums (AddBot d') $ logRNFProds δ̇
  _ → return $ RNFSums Bot $ RNFProds dø (LogRA γ̇ ↦ one) ↦ one

-- ┌────┐
-- │㏒ δ̇│
-- └────┘
logRNFProds ∷ RNFProds → RNFProds ⇰ AddTop 𝔻
logRNFProds (RNFProds δ̂ δ̌) = 
  sum
  [ sum $ do 
      γ̇ :* c ← list δ̂
      return $ RNFProds dø (LogRA γ̇ ↦ c) ↦ one
  , sum $ do 
      α :* c ← list δ̌
      let c' :* δ̇ = logRNFAtom α
      return $ δ̇ ↦ c' -- (c × c')
  ]

logRNFAtom ∷ RNFAtom → (AddTop 𝔻 ∧ RNFProds)
logRNFAtom = \case
  EfnRA c δ̇ → c :* δ̇
  α → one :* oneAtom α

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
  SymRNF α̇ → elimAddTop (ConstantRNF TopBT) SymRNF $ logRNFMaxs α̇

trRNF ∷ RNF → RNF
trRNF = undefined

instance HasPrism RNF ℕ where
  hasPrism = Prism (dblRNF ∘ dbl) $ \case
    ConstantRNF BotBT → Some 0
    ConstantRNF (AddBT (natO → Some n)) → Some n
    _ → None

instance HasPrism RNF 𝔻 where
  hasPrism = Prism dblRNF $ \case
    ConstantRNF BotBT → Some 0.0
    ConstantRNF (AddBT d) → Some d
    _ → None

instance Bot RNF where bot = ConstantRNF BotBT
instance Top RNF where top = ConstantRNF TopBT
instance Join RNF where (⊔) = maxRNF
instance Meet RNF where (⊓) = minRNF

instance Zero RNF where zero = ConstantRNF BotBT
instance One RNF where one = ConstantRNF (AddBT one)
instance Plus RNF where (+) = sumRNF
instance Times RNF where (×) = prodRNF

instance Additive RNF
instance Multiplicative RNF
instance JoinLattice RNF
instance MeetLattice RNF
instance Lattice RNF

instance Exponential RNF where (^) = undefined
instance ExponentialFn RNF where exp = undefined
instance Root RNF where root = undefined
instance Log RNF where log = undefined

instance POrd RNF where
  η₁ ⊑ η₂ = (η₁ ⊔ η₂) ≡ η₂

-- instance Pretty RNF where pretty = undefined

type RExp = Annotated FullContext RExpPre
data RExpPre =
    VarRE 𝕏
  | ConstRE (AddBT 𝔻)
  | MaxRE RExp RExp
  | MinRE RExp RExp
  | PlusRE RExp RExp
  | TimesRE RExp RExp
  | PowRE ℚ RExp
  | EfnRE RExp
  | LogRE RExp
  deriving (Eq,Ord,Show)
makePrettySum ''RExpPre

varRE ∷ 𝕏 → RExp
varRE = Annotated null ∘ VarRE

constRE ∷ AddBT 𝔻 → RExp
constRE = Annotated null ∘ ConstRE

maxRE ∷ RExp → RExp → RExp
maxRE = Annotated null ∘∘ MaxRE

minRE ∷ RExp → RExp → RExp
minRE = Annotated null ∘∘ MinRE

plusRE ∷ RExp → RExp → RExp
plusRE = Annotated null ∘∘ PlusRE

timesRE ∷ RExp → RExp → RExp
timesRE = Annotated null ∘∘ TimesRE

powRE ∷ ℚ → RExp → RExp
powRE = Annotated null ∘∘ PowRE

efnRE ∷ RExp → RExp
efnRE = Annotated null ∘ EfnRE

logRE ∷ RExp → RExp
logRE = Annotated null ∘ LogRE

-- add exp
-- add log
-- add ind

normalizeRNF ∷ RExp → RNF
normalizeRNF = normalizeRNFPre ∘ extract

normalizeRNFPre ∷ RExpPre → RNF
normalizeRNFPre = \case
  VarRE x → varRNF x
  ConstRE c → ConstantRNF c
  MaxRE η₁ η₂ → normalizeRNF η₁ ⊔ normalizeRNF η₂
  MinRE η₁ η₂ → normalizeRNF η₁ ⊓ normalizeRNF η₂
  PlusRE η₁ η₂ → normalizeRNF η₁ + normalizeRNF η₂
  TimesRE η₁ η₂ → normalizeRNF η₁ × normalizeRNF η₂
  PowRE c η → powerRNF c $ normalizeRNF η
  EfnRE η → efnRNF $ normalizeRNF η
  LogRE η → logRNF $ normalizeRNF η

e1 ∷ RNF
e1 = normalizeRNF $ varRE (var "x") `timesRE` varRE (var "x")

e2 ∷ RNF
e2 = normalizeRNF $ powRE (rat 1 / rat 2) $ (varRE (var "x") `timesRE` varRE (var "x")) `plusRE` varRE (var "y")

-- ((a^½ + b^½) ^ ½) × ((a^½ + b^½) ^ ½)
-- ==
-- (a^½ + b^½)
e3 ∷ RNF
e3 = normalizeRNF $
  powRE (rat 1 / rat 2)
    ((powRE (rat 1 / rat 2) (varRE (var "a")))
     `plusRE`
     (powRE (rat 1 / rat 2) (varRE (var "b"))))
  `timesRE`
  powRE (rat 1 / rat 2)
    ((powRE (rat 1 / rat 2) (varRE (var "a")))
     `plusRE`
     (powRE (rat 1 / rat 2) (varRE (var "b"))))

e3' ∷ RNF
e3' = normalizeRNF $
    (powRE (rat 1 / rat 2) (varRE (var "a")))
    `plusRE`
    (powRE (rat 1 / rat 2) (varRE (var "b")))

-- Substitution --

e1subst ∷ RNF
e1subst = substRNF (var "x") (dblRNF 3.0) e1

e1subst' ∷ RNF
e1subst' = substRNF (var "x") (substRNF (var "x") e1 e1) e1

substRNF ∷ 𝕏 → RNF → RNF → RNF
substRNF _ _ (ConstantRNF a) = ConstantRNF a
substRNF x r' (SymRNF maxs) = substRNFMaxs x r' maxs

substRNFMaxs ∷ 𝕏 → RNF → RNFMaxs → RNF
substRNFMaxs x r' (RNFMaxs d pmins) = fold (addBot2RNF d) maxRNF $ do
  (RNFMins c psums) ← list pmins
  return $ fold (addTop2RNF c) minRNF $ do
    sums ← list psums
    return $ substRNFSums x r' sums

substRNFSums ∷ 𝕏 → RNF → RNFSums → RNF
substRNFSums x r' (RNFSums d γ) = do
  fold (addBot2RNF d) sumRNF $ do
    (prods :* sca) ← list γ
    return $ prodRNF (addTop2RNF sca) $ substRNFProds x r' prods

substRNFProds ∷ 𝕏 → RNF → RNFProds → RNF
substRNFProds x r' (RNFProds δ̂ δ̌) =
  let δ̂' = fold (dblRNF 1.0) prodRNF $ map (\(sums :* q) → powerRNF q $ substRNFSums x r' sums) $ list δ̂ in
  let δ̌' = fold (dblRNF 1.0) prodRNF $ map (\(atom :* q) → powerRNF q $ substRAtom x r' atom) $ list δ̌
  in prodRNF δ̂' δ̌'

substRAtom ∷ 𝕏 → RNF → RNFAtom → RNF
substRAtom x r' = \case
  VarRA y → case x ≡ y of
    True → r'
    False → varRNF y
  -- LogRA xs² → logRNF $ substRNFSums x r' xs²
  -- EfnRA xs¹ → expFnRNF $ substRNFProds x r' xs¹

addBT2RNF ∷ AddBT 𝔻 → RNF
addBT2RNF BotBT = bot
addBT2RNF TopBT = top
addBT2RNF (AddBT d) = dblRNF d

addBot2RNF ∷ AddBot 𝔻 → RNF
addBot2RNF Bot = bot
addBot2RNF (AddBot d) = dblRNF d

addTop2RNF ∷ AddTop 𝔻 → RNF
addTop2RNF Top = top
addTop2RNF (AddTop d) = dblRNF d
