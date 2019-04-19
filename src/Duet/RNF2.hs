module Duet.RNF2 where

import Duet.UVMHS

-- before

-- data RNF =
--     NNRealRNF 𝔻
--   | TopRNF
--   | BotRNF
--   | SymRNF (𝑃 {- max -} (𝑃 {- min -} RSP))
--   deriving (Eq,Ord,Show)
-- newtype RSP = RSP { unRSP ∷ (𝔹 {- top? -} ∧ (RAtom ⇰ {- prod -} 𝔻)) ⇰ {- sum -} 𝔻 }
--   deriving (Eq,Ord,Show)
-- data RAtom =
--     VarRA 𝕏
--   | InvRA RSP
--   | EFnRA RSP
--   | LogRA RSP
--   deriving (Eq,Ord,Show)
-- 
-- makePrisms ''RNF
-- 
-- instance HasPrism RNF ℕ where hasPrism = natRNFL
-- instance HasPrism RNF 𝔻 where hasPrism = nNRealRNFL

-- David in January

data RNF = 
    NNRealRNF (AddTop 𝔻)
  | SymRNF RNFMaxes
  deriving (Eq,Ord,Show)

data RNFMaxes = RNFMaxes
  { rnfMaxConstant ∷ 𝔻 -- could be zero (can't be top)
  , rnfMaxSymbolic ∷ 𝑃 RNFMins -- (at least one inside)
  }
  deriving (Eq,Ord,Show)

data RNFMins = RNFMins
  { rnfMinConstant ∷ AddTop 𝔻 -- could be top (can't be zero)
  , rnfMinSymbolic ∷ 𝑃 RNFSums -- (at least one inside)
  }
  deriving (Eq,Ord,Show)

data RNFSums = RNFSums
  { rnfSumConstant ∷ 𝔻 -- can be zero
  , rnfSumSymbolic ∷ RNFProds ⇰ 𝔻 -- (at least one inside)
  }
  deriving (Eq,Ord,Show)

data RNFProds = RNFProds
  { rnfProdHasTop ∷ 𝔹
  , rnfProdSymbolic ∷ RNFAtom ⇰ 𝔻 -- (at least one inside)
  }
  deriving (Eq,Ord,Show)

data RNFAtom =
    VarRA 𝕏
  | InvRA RNFSums -- (at least two in sum)
  | RootRA RNFSums -- (at least two in sum)
  | LogRA RNFSums -- (at least two in sum)
  | EfnRA RNFSums -- (at least two in sum)
  deriving (Eq,Ord,Show)

maxRNF ∷ RNF → RNF → RNF
maxRNF r₁ r₂ = case (r₁,r₂) of
  (NNRealRNF Top,_) → NNRealRNF Top
  (_,NNRealRNF Top) → NNRealRNF Top
  (NNRealRNF c₁,NNRealRNF c₂) → NNRealRNF (c₁ ⊔ c₂)
  (NNRealRNF (AddTop c₁),SymRNF (RNFMaxes c₂ ys⁴)) → SymRNF $ RNFMaxes (c₁ ⊔ c₂) ys⁴
  (SymRNF (RNFMaxes c₁ xs⁴),NNRealRNF (AddTop c₂)) → SymRNF $ RNFMaxes (c₁ ⊔ c₂) xs⁴
  (SymRNF (RNFMaxes c₁ xs⁴), SymRNF (RNFMaxes c₂ ys⁴)) → SymRNF $ RNFMaxes (c₁ ⊔ c₂) (xs⁴ ∪ ys⁴)

minRNFMaxs ∷ 𝑃 RNFMins → 𝑃 RNFMins → 𝑃 RNFMins
minRNFMaxs xs⁴ ys⁴ = pow $ do
  RNFMins d₁ xs³ ← iter xs⁴
  RNFMins d₂ ys³ ← iter ys⁴
  return $ RNFMins (d₁ ⊓ d₂) (xs³ ∪ ys³)

minRNFMaxsConstant ∷ 𝔻 → 𝑃 RNFMins → AddBot (𝑃 RNFMins) -- Bot = ∅ and AddBot ≠ ∅
minRNFMaxsConstant c xs⁴ =
  let xs⁴' = pow $ do
        RNFMins d₁ xs³ ← iter xs⁴
        case c ≡ 0.0 of
          True → mzero
          False → return $ RNFMins (AddTop c ⊓ d₁) xs³
  in case xs⁴' ≡ pø of
    True → Bot
    False → AddBot xs⁴'

minRNF ∷ RNF → RNF → RNF
minRNF r₁ r₂ = case (r₁,r₂) of
  (NNRealRNF (AddTop c₁),_) | c₁ ≡ 0.0 → NNRealRNF $ AddTop 0.0
  (_,NNRealRNF (AddTop c₂)) | c₂ ≡ 0.0 → NNRealRNF $ AddTop 0.0
  (NNRealRNF c₁,NNRealRNF c₂) → NNRealRNF (c₁ ⊓ c₂)
  (NNRealRNF Top,SymRNF (RNFMaxes c₂ ys⁴)) → SymRNF $ RNFMaxes c₂ ys⁴
  (NNRealRNF (AddTop c₁),SymRNF (RNFMaxes c₂ ys⁴)) → SymRNF $ RNFMaxes (c₁ ⊓ c₂) ys⁴
  (SymRNF (RNFMaxes c₁ xs⁴),NNRealRNF Top) → SymRNF $ RNFMaxes c₁ xs⁴
  (SymRNF (RNFMaxes c₁ xs⁴),NNRealRNF (AddTop c₂)) → SymRNF $ RNFMaxes (c₁ ⊓ c₂) xs⁴
  (SymRNF (RNFMaxes c₁ xs⁴), SymRNF (RNFMaxes c₂ ys⁴)) →  SymRNF $ RNFMaxes (c₁ ⊓ c₂) $ concat
    [ elimAddBot pø id $ minRNFMaxsConstant c₁ ys⁴
    , elimAddBot pø id $ minRNFMaxsConstant c₂ xs⁴
    , minRNFMaxs xs⁴ ys⁴ 
    ]

sumRNFConstantMins ∷ 𝔻 → 𝑃 RNFSums → 𝑃 RNFSums
sumRNFConstantMins c xs³ = pow $ do
  RNFSums d xs² ← iter xs³
  return $ RNFSums (c + d) xs²

sumRNFConstantMaxs ∷ 𝔻 → 𝑃 RNFMins → 𝑃 RNFMins
sumRNFConstantMaxs c xs⁴ = pow $ do
  RNFMins d xs³ ← iter xs⁴
  return $ RNFMins (AddTop c + d) $ sumRNFConstantMins c xs³

sumRNF ∷ RNF → RNF → RNF
sumRNF r₁ r₂ = case (r₁,r₂) of
  (NNRealRNF c₁,NNRealRNF c₂) → NNRealRNF (c₁ + c₂)
  -- c₁ + (c₂ ⊔ ys) = (c₁ + c₂) ⊔ (c₁ + ys)
  (NNRealRNF Top,SymRNF (RNFMaxes c₂ ys⁴)) → NNRealRNF Top
  (NNRealRNF (AddTop c₁),SymRNF (RNFMaxes c₂ ys⁴)) → SymRNF $ RNFMaxes (c₁ + c₂) $ sumRNFConstantMaxs c₁ ys⁴
  (SymRNF (RNFMaxes c₁ xs⁴),NNRealRNF Top) → NNRealRNF Top
  (SymRNF (RNFMaxes c₁ xs⁴),NNRealRNF (AddTop c₂)) → SymRNF $ RNFMaxes (c₁ + c₂) $ sumRNFConstantMaxs c₂ xs⁴
  (SymRNF (RNFMaxes c₁ xs⁴),SymRNF (RNFMaxes c₂ ys⁴)) → SymRNF $ RNFMaxes (c₁ + c₂) $ 
    undefined
    -- [ sumRNFConstantMaxs c₁ xs⁴
    -- , sumRNFConstantMaxs c₂ ys⁴
    -- , sumRNFMaxs xs⁴ ys⁴
    -- ]
    -- -- (c₁ ⊔ xs⁴) + (c₂ ⊔ ys⁴)
    -- -- (c₁ + c₂) ⊔ (c₁ + xs⁴) ⊔ (c₂ + ys⁴) ⊔ (xs⁴ + ys⁴)
    -- --
    -- -- d₁ ⊓ xs
    -- RNFMins d₁ xs³ ← iter xs⁴
    -- -- d₂ ⊓ ys
    -- RNFMins d₂ ys³ ← iter ys⁴
    -- -- (d₁ ⊓ xs) + (d₂ ⊓ ys) = (d₁ + d₂) ⊓ (d₁ + ys) ⊓ (xs + d₂) ⊓ (xs + ys)
    -- return $ RNFMins (d₁ + d₂) $ pow $ concat
    --   [ iter $ sumRNFConstantMins (_ d₁) ys³
    --   , iter $ sumRNFConstantMins d₂ xs³
    --   , do RNFSums b₁ xs² ← iter xs³
    --        RNFSums b₂ ys² ← iter xs³
    --        return $ RNFSums (b₁ + b₂) (xs² + ys²)
    --   ]

-- prodRNF ∷ RNF → RNF → RNF
-- prodRNF r₁ r₂ = case (r₁,r₂) of
--   (TopRNF,TopRNF) → TopRNF
--   (NNRealRNF _,TopRNF) → TopRNF
--   (TopRNF,NNRealRNF _) → TopRNF
--   -- ⊤ × (c₂ ⊔ ys⁴)
--   -- (⊤ × c₂) ⊔ (⊤ × ys⁴)
--   (TopRNF,(RNFMaxes c₂ ys⁴)) = RNFMaxes ( 
--     | c₂ ≡ 0.0 → RNFMaxesprodRNFTopMaxs  

