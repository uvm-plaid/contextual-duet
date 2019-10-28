{-# LANGUAGE PartialTypeSignatures #-}
module Duet.Syntax where

import Duet.UVMHS

import Duet.RNF2

data Norm = L1 | L2 | LInf
  deriving (Eq,Ord,Show)

data ProgramVar = TLVar 𝕏 | TMVar 𝕏
  deriving (Eq,Ord,Show)

data Clip = NormClip Norm | UClip
  deriving (Eq,Ord,Show)

newtype Sens r = Sens { unSens ∷ r }
  deriving
  (Eq,Ord,Show
  ,Zero,Plus,Additive
  ,One,Times,Multiplicative
  ,Null,Append,Monoid
  ,Unit,Cross,Prodoid
  ,POrd
  ,Bot,Join,JoinLattice
  ,Top,Meet,MeetLattice
  ,Lattice)

instance Functor Sens where map f = Sens ∘ f ∘ unSens

instance (HasPrism r s) ⇒ HasPrism (Sens r) s where
  hasPrism = Prism
    { construct = Sens ∘ construct hasPrism
    , view = view hasPrism ∘ unSens
    }

data PRIV =
    EPS
  | ED
  | RENYI
  | ZC
  | TC
  deriving (Eq,Ord,Show)

data PRIV_W (p ∷ PRIV) where
  EPS_W ∷ PRIV_W 'EPS
  ED_W ∷ PRIV_W 'ED
  RENYI_W ∷ PRIV_W 'RENYI
  ZC_W ∷ PRIV_W 'ZC
  TC_W ∷ PRIV_W 'TC

eqPRIV ∷ PRIV_W p₁ → PRIV_W p₂ → 𝑂 (p₁ ≟ p₂)
eqPRIV p₁ p₂ = case (p₁,p₂) of
  (EPS_W,EPS_W) → Some Refl
  (ED_W,ED_W) → Some Refl
  (RENYI_W,RENYI_W) → Some Refl
  (ZC_W,ZC_W) → Some Refl
  (TC_W,TC_W) → Some Refl
  (_,_) → None

stripPRIV ∷ PRIV_W p → PRIV
stripPRIV = \case
  EPS_W → EPS
  ED_W → ED
  RENYI_W → RENYI
  ZC_W → ZC
  TC_W → TC

class PRIV_C (p ∷ PRIV) where
  priv ∷ PRIV_W p

instance PRIV_C 'EPS where priv = EPS_W
instance PRIV_C 'ED where priv = ED_W
instance PRIV_C 'RENYI where priv = RENYI_W
instance PRIV_C 'ZC where priv = ZC_W
instance PRIV_C 'TC where priv = TC_W

data Pr (p ∷ PRIV) r where
  EpsPriv ∷ r → Pr 'EPS r
  EDPriv ∷ r → r → Pr 'ED r
  RenyiPriv ∷ r → r → Pr 'RENYI r
  ZCPriv ∷ r → Pr 'ZC r
  TCPriv ∷ r → r → Pr 'TC r
deriving instance (Eq r) ⇒ Eq (Pr p r)
deriving instance (Ord r) ⇒ Ord (Pr p r)
deriving instance (Show r) ⇒ Show (Pr p r)

instance (Append r,Meet r) ⇒ Append (Pr p r) where
  EpsPriv ε₁ ⧺ EpsPriv ε₂ = EpsPriv $ ε₁ ⧺ ε₂
  EDPriv ε₁ δ₁ ⧺ EDPriv ε₂ δ₂ = EDPriv (ε₁ ⧺ ε₂) (δ₁ ⧺ δ₂)
  RenyiPriv α₁ ε₁ ⧺ RenyiPriv α₂ ε₂ = RenyiPriv (α₁ ⊓ α₂) (ε₁ ⧺ ε₂)
  ZCPriv ρ₁ ⧺ ZCPriv ρ₂ = ZCPriv $ ρ₁ ⧺ ρ₂
  TCPriv ρ₁ ω₁ ⧺ TCPriv ρ₂ ω₂ = TCPriv (ρ₁ ⧺ ρ₂) (ω₁ ⊓ ω₂)
instance (Join r,Meet r) ⇒ Join (Pr p r) where
  EpsPriv ε₁ ⊔ EpsPriv ε₂ = EpsPriv $ ε₁ ⊔ ε₂
  EDPriv ε₁ δ₁ ⊔ EDPriv ε₂ δ₂ = EDPriv (ε₁ ⊔ ε₂) (δ₁ ⊔ δ₂)
  RenyiPriv α₁ ε₁ ⊔ RenyiPriv α₂ ε₂ = RenyiPriv (α₁ ⊓ α₂) (ε₁ ⊔ ε₂)
  ZCPriv ρ₁ ⊔ ZCPriv ρ₂ = ZCPriv $ ρ₁ ⊔ ρ₂
  TCPriv ρ₁ ω₁ ⊔ TCPriv ρ₂ ω₂ = TCPriv (ρ₁ ⊔ ρ₂) (ω₁ ⊓ ω₂)
instance (Join r,Meet r) ⇒ Meet (Pr p r) where
  EpsPriv ε₁ ⊓ EpsPriv ε₂ = EpsPriv $ ε₁ ⊓ ε₂
  EDPriv ε₁ δ₁ ⊓ EDPriv ε₂ δ₂ = EDPriv (ε₁ ⊓ ε₂) (δ₁ ⊓ δ₂)
  RenyiPriv α₁ ε₁ ⊓ RenyiPriv α₂ ε₂ = RenyiPriv (α₁ ⊔ α₂) (ε₁ ⊓ ε₂)
  ZCPriv ρ₁ ⊓ ZCPriv ρ₂ = ZCPriv $ ρ₁ ⊓ ρ₂
  TCPriv ρ₁ ω₁ ⊓ TCPriv ρ₂ ω₂ = TCPriv (ρ₁ ⊓ ρ₂) (ω₁ ⊔ ω₂)
instance (Plus r) ⇒ Plus (Pr p r) where
  EpsPriv ε₁ + EpsPriv ε₂ = EpsPriv $ ε₁ + ε₂
  EDPriv ε₁ δ₁ + EDPriv ε₂ δ₂ = EDPriv (ε₁ + ε₂) (δ₁ + δ₂)
  RenyiPriv α₁ ε₁ + RenyiPriv α₂ ε₂ = RenyiPriv (α₁ + α₂) (ε₁ + ε₂)
  ZCPriv ρ₁ + ZCPriv ρ₂ = ZCPriv $ ρ₁ + ρ₂
  TCPriv ρ₁ ω₁ + TCPriv ρ₂ ω₂ = TCPriv (ρ₁ + ρ₂) (ω₁ + ω₂)

iteratePr ∷ (Times r) ⇒ r → Pr p r → Pr p r
iteratePr x = \case
  EpsPriv ε → EpsPriv $ x × ε
  EDPriv ε δ → EDPriv (x × ε) (x × δ)
  RenyiPriv α ε → RenyiPriv α $ x × ε
  ZCPriv ρ → ZCPriv $ x × ρ
  TCPriv ρ ω → TCPriv (x × ρ) ω

makePr ∷ ∀ p r. (PRIV_C p,Top r) ⇒ r → Pr p r
makePr r = case priv @ p of
  EPS_W → EpsPriv r
  ED_W → EDPriv r r
  RENYI_W → RenyiPriv top r
  ZC_W → ZCPriv r
  TC_W → TCPriv r top

indicatorPr ∷ (Join r) ⇒ Pr p r → r
indicatorPr = \case
  EpsPriv ε → ε
  EDPriv ε δ → ε ⊔ δ
  RenyiPriv _α ε → ε
  ZCPriv ρ → ρ
  TCPriv ρ _ω → ρ

-- JOE TODO: put a link here to the paper
-- TODO: fix this formula when we have minus and divide
-- convertRENYIEDPr ∷ (One r,Plus r,Minus r,Divide r,Log r) ⇒ r → Pr 'RENYI r → Pr 'ED r
-- convertRENYIEDPr δ (RenyiPriv α ε) = EDPriv (ε + log (one / δ) / (α - one)) δ
convertRENYIEDPr ∷ (One r,Plus r,Log r) ⇒ r → Pr 'RENYI r → Pr 'ED r
convertRENYIEDPr δ (RenyiPriv α ε) = EDPriv ε δ

-- JOE TODO: put a link here to the paper
convertZCEDPr ∷ (One r,Plus r,Times r,Divide r,Root r,Log r) ⇒ r → Pr 'ZC r → Pr 'ED r
convertZCEDPr δ (ZCPriv ρ) = EDPriv (ρ + (one + one) × root (ρ × log (one / δ))) δ

-- JOE TODO: put a link here to the paper
convertEPSZCPr ∷ (One r,Plus r,Times r,Divide r,Root r,Log r) ⇒ Pr 'EPS r → Pr 'ZC r
convertEPSZCPr (EpsPriv ε) = ZCPriv ((one / (one + one)) × ε × ε)

-- JOE TODO: put a link here to the paper
-- we would like to have a constraint solver for this, because the conversion
-- only makes sense when ⟨δ,ρ,ω⟩ are in a particular relationship
-- convertTCEDPr ∷ (One r,Plus r,Minus r,Divide r,Log r) ⇒ r → Pr 'TC r → Pr 'ED r
-- convertTCEDPr δ (TCPriv ρ ω) = EDPRIV _ _

instance Functor (Pr p) where
  map f (EpsPriv ε) = EpsPriv $ f ε
  map f (EDPriv ε δ) = EDPriv (f ε) (f δ)
  map f (RenyiPriv α ε) = RenyiPriv (f α) (f ε)
  map f (ZCPriv ρ) = ZCPriv $ f ρ
  map f (TCPriv ρ ω) = TCPriv (f ρ) (f ω)

data PEnv r where
  PEnv ∷ ∀ (p ∷ PRIV) r. (PRIV_C p) ⇒ ProgramVar ⇰ Pr p r → PEnv r

instance (Eq r) ⇒ Eq (PEnv r) where
  (==) ∷ PEnv r → PEnv r → 𝔹
  PEnv (xps₁ ∷ ProgramVar ⇰ Pr p₁ r) == PEnv (xps₂ ∷ ProgramVar ⇰ Pr p₂ r) = case eqPRIV (priv @ p₁) (priv @ p₂) of
    Some Refl → xps₁ ≡ xps₂
    None → False
instance (Ord r) ⇒ Ord (PEnv r) where
  compare ∷ PEnv r → PEnv r → Ordering
  compare (PEnv (xps₁ ∷ ProgramVar ⇰ Pr p₁ r)) (PEnv (xps₂ ∷ ProgramVar ⇰ Pr p₂ r)) = case eqPRIV (priv @ p₁) (priv @ p₂) of
    Some Refl → compare xps₁ xps₂
    None → compare (stripPRIV (priv @ p₁)) (stripPRIV (priv @ p₂))
deriving instance (Show r) ⇒ Show (PEnv r)

data RowsT r = RexpRT r | StarRT deriving (Eq,Ord,Show)

instance Functor RowsT where
  map ∷ (a → b) → RowsT a → RowsT b
  map f = \case
    RexpRT r → RexpRT $ f r
    StarRT → StarRT

data MExp r =
    EmptyME
  | VarME 𝕏
  | ConsME (Type r) (MExp r)
  | AppendME (MExp r) (MExp r)
  | RexpME r (Type r)
  deriving (Eq,Ord,Show)

instance Functor MExp where
  map ∷ (a → b) → MExp a → MExp b
  map f = \case
    EmptyME → EmptyME
    VarME x → VarME x
    ConsME τ m → ConsME (map f τ) (map f m)
    AppendME n m → AppendME (map f n) (map f m)
    RexpME r τ → RexpME (f r) (map f τ)

data Kind =
    ℕK
  | ℝK
  | TypeK
  | CxtK
  | SchemaK
  deriving (Eq,Ord,Show)

-- DAVID STILL HATES THIS
instance POrd Kind where
  x ⊑ y | x ≡ y = True
  ℕK ⊑ ℝK = True
  _ ⊑ _ = False

data KindE =
    ℕKE
  | ℝKE
  | TypeKE
  | ErrorKE
  deriving (Eq,Ord,Show)

instance Join KindE where
  ℕKE ⊔ ℝKE = ℝKE
  ℝKE ⊔ ℕKE = ℝKE
  x  ⊔ y
    | x ≡ y = x
    | otherwise = ErrorKE

toKindE ∷ Kind → KindE
toKindE ℕK = ℕKE
toKindE ℝK = ℝKE
toKindE TypeK = TypeKE

frKindE ∷ KindE → 𝑂 Kind
frKindE ℕKE = Some ℕK
frKindE ℝKE = Some ℝK
frKindE TypeKE = Some TypeK
frKindE ErrorKE = None

-- concrete syntax:
-- (x : τ₁) ⊸[ x⋅0 ] (y : τ₂) ⊸⋆ [ x⋅p₁ y⋅p₂ ] τ₃
type TypeSource r = Annotated FullContext (Type r)
data Type r =
    VarT 𝕏
  | ℕˢT r
  | ℝˢT r
  | ℕT
  | ℝT
  | 𝕀T r
  | 𝔹T
  | 𝕊T
  | SetT (Type r)
  | 𝕄T Norm Clip (RowsT r) (MExp r)
  | 𝔻T (Type r)
  | Type r :⊕: Type r
  | Type r :⊗: Type r
  | (Type r ∧ (ProgramVar ⇰ Sens r)) :&: ((ProgramVar ⇰ Sens r) ∧ Type r)
  | (Type r ∧ (ProgramVar ⇰ Sens r)) :⊞: ((ProgramVar ⇰ Sens r) ∧ Type r)
  | (Type r ∧ (ProgramVar ⇰ Sens r)) :⊠: ((ProgramVar ⇰ Sens r) ∧ Type r)
  | (𝕏 ∧ Type r) :⊸: ((ProgramVar ⇰ Sens r) ∧ Type r)
  | (𝕏 ∧ Type r ∧ Sens r) :⊸⋆: (PEnv r ∧ Type r)
  | ForallT 𝕏 Kind (Type r)
  | CxtT (𝑃 ProgramVar)
  | UnitT
  | BoxedT (𝕏 ⇰ Sens r) (Type r)
  deriving (Eq,Ord,Show)

instance Functor Type where
  map ∷ (a → b) → Type a → Type b
  map f = \case
    ℕˢT r → ℕˢT $ f r
    ℝˢT r → ℝˢT $ f r
    ℕT → ℕT
    ℝT → ℝT
    𝕀T r → 𝕀T $ f r
    𝔹T → 𝔹T
    𝕊T → 𝕊T
    SetT τ → SetT (map f τ)
    𝕄T ℓ c r₁ r₂ → 𝕄T ℓ c (map f r₁) (map f r₂)
    𝔻T τ → 𝔻T $ map f τ
    τ₁ :⊕: τ₂ → map f τ₁ :⊕: map f τ₂
    τ₁ :⊗: τ₂ → map f τ₁ :⊗: map f τ₂
    (τ₁ :* σ₁) :&: (σ₂ :* τ₂) → (map f τ₁ :* mapp f σ₁) :&: (mapp f σ₂ :* map f τ₂)
    (τ₁ :* σ₁) :⊞: (σ₂ :* τ₂) → (map f τ₁ :* mapp f σ₁) :⊞: (mapp f σ₂ :* map f τ₂)
    (τ₁ :* σ₁) :⊠: (σ₂ :* τ₂) → (map f τ₁ :* mapp f σ₁) :⊠: (mapp f σ₂ :* map f τ₂)
    -- sλ
    (x :* τ₁) :⊸: (σ :* τ₂) → (x :* map f τ₁) :⊸: (mapp f σ :*  map f τ₂)
    -- pλ
    (x :* τ₁ :* s) :⊸⋆: (PEnv pσ :* τ₂) → (x :* map f τ₁ :* map f s) :⊸⋆: (PEnv (map (map f) pσ) :* map f τ₂)
    ForallT α κ τ → ForallT α κ $ map f τ
    CxtT xs → CxtT xs
    UnitT → UnitT
    BoxedT σ τ → BoxedT (map (map f) σ) (map f τ)
    VarT x → VarT x

type TLExp r = Annotated FullContext (TLExpPre r)
data TLExpPre r =
    VarTE 𝕏
  -- Type Stuff
  | ℕˢTE r
  | ℝˢTE r
  | ℕTE
  | ℝTE
  | 𝕀TE r
  | 𝔹TE
  | 𝕊TE
  | SetTE (TLExp r)
  | 𝕄TE Norm Clip (RowsT r) (MExp r)
  | 𝔻TE (TLExp r)
  | TLExp r :⊕♭: TLExp r
  | TLExp r :⊗♭: TLExp r
  | (TLExp r ∧ (ProgramVar ⇰ Sens r)) :&♭: ((ProgramVar ⇰ Sens r) ∧ TLExp r)
  | (TLExp r ∧ (ProgramVar ⇰ Sens r)) :⊞♭: ((ProgramVar ⇰ Sens r) ∧ TLExp r)
  | (TLExp r ∧ (ProgramVar ⇰ Sens r)) :⊠♭: ((ProgramVar ⇰ Sens r) ∧ TLExp r)
  | (𝕏 ∧ TLExp r) :⊸♭: ((ProgramVar ⇰ Sens r) ∧ TLExp r)
  | (𝕏 ∧ TLExp r ∧ Sens r) :⊸⋆♭: (PEnv r ∧ TLExp r)
  | ForallTE 𝕏 Kind (TLExp r)
  | CxtTE (𝑃 ProgramVar)
  | UnitTE
  | BoxedTE (𝕏 ⇰ Sens r) (TLExp r)
  -- RExp Stuff
  | NatTE ℕ
  | NNRealTE 𝔻
  | MaxTE (TLExp r) (TLExp r)
  | MinTE (TLExp r) (TLExp r)
  | PlusTE (TLExp r) (TLExp r)
  | TimesTE (TLExp r) (TLExp r)
  | DivTE (TLExp r) (TLExp r)
  | RootTE (TLExp r)
  | LogTE (TLExp r)
  | TopTE
  -- Schema stuff
  | EmptyTE
  | ConsTE (TLExp r) (TLExp r)
  | AppendTE (TLExp r) (TLExp r)
  | RexpTE (TLExp r) (TLExp r)
  -- Privacy Stuff
  -- QUESTION, TODO
  | PairTE (TLExp r) (TLExp r)
  deriving (Eq,Ord,Show)
makePrettySum ''TLExpPre

instance Functor TLExpPre where
  map ∷ (a → b) → TLExpPre a → TLExpPre b
  map f = \case
    ℕˢTE r → ℕˢTE $ f r
    ℝˢTE r → ℝˢTE $ f r
    ℕTE → ℕTE
    ℝTE → ℝTE
    𝕀TE r → 𝕀TE $ f r
    𝔹TE → 𝔹TE
    𝕊TE → 𝕊TE
    SetTE τ → do
      let tag = annotatedTag τ
      SetTE $ Annotated tag (map f (extract τ))
    𝕄TE ℓ c r₁ r₂ → 𝕄TE ℓ c (map f r₁) (map f r₂)
    𝔻TE τ → do
      let tag = annotatedTag τ
      𝔻TE $ Annotated tag (map f (extract τ))
    τ₁ :⊕♭: τ₂ → do
      let tag₁ = annotatedTag τ₁
      let tag₂ = annotatedTag τ₂
      (Annotated tag₁ (map f (extract τ₁))) :⊕♭: (Annotated tag₂ (map f (extract τ₂)))
    τ₁ :⊗♭: τ₂ → do
      let tag₁ = annotatedTag τ₁
      let tag₂ = annotatedTag τ₂
      (Annotated tag₁ (map f (extract τ₁))) :⊗♭: (Annotated tag₂ (map f (extract τ₂)))
    (τ₁ :* σ₁) :&♭: (σ₂ :* τ₂) → do
      let tag₁ = annotatedTag τ₁
      let tag₂ = annotatedTag τ₂
      ((Annotated tag₁ (map f (extract τ₁))) :* mapp f σ₁) :&♭: (mapp f σ₂ :* (Annotated tag₂ (map f (extract τ₂))))
    (τ₁ :* σ₁) :⊞♭: (σ₂ :* τ₂) → do
      let tag₁ = annotatedTag τ₁
      let tag₂ = annotatedTag τ₂
      ((Annotated tag₁ (map f (extract τ₁))) :* mapp f σ₁) :⊞♭: (mapp f σ₂ :* (Annotated tag₂ (map f (extract τ₂))))
    (τ₁ :* σ₁) :⊠♭: (σ₂ :* τ₂) → do
      let tag₁ = annotatedTag τ₁
      let tag₂ = annotatedTag τ₂
      ((Annotated tag₁ (map f (extract τ₁))) :* mapp f σ₁) :⊠♭: (mapp f σ₂ :* (Annotated tag₂ (map f (extract τ₂))))
    (x :* τ₁) :⊸♭: (σ :* τ₂) → do
      let tag₁ = annotatedTag τ₁
      let tag₂ = annotatedTag τ₂
      (x :* (Annotated tag₁ (map f (extract τ₁)))) :⊸♭: (mapp f σ :* (Annotated tag₂ (map f (extract τ₂))))
    (x :* τ₁ :* s) :⊸⋆♭: (PEnv pσ :* τ₂) → do
      let tag₁ = annotatedTag τ₁
      let tag₂ = annotatedTag τ₂
      (x :* (Annotated tag₁ (map f (extract τ₁))) :* map f s) :⊸⋆♭: (PEnv (map (map f) pσ) :* (Annotated tag₂ (map f (extract τ₂))))
    ForallTE α κ τ → do
      let tag = annotatedTag τ
      ForallTE α κ $ (Annotated tag (map f (extract τ)))
    CxtTE xs → CxtTE xs
    UnitTE → UnitTE
    VarTE x → VarTE x
    NatTE n → NatTE n
    NNRealTE d → NNRealTE d
    MaxTE τ₁ τ₂ → do
      let tag₁ = annotatedTag τ₁
      let tag₂ = annotatedTag τ₂
      MaxTE (Annotated tag₁ (map f (extract τ₁))) (Annotated tag₂ (map f (extract τ₂)))
    MinTE τ₁ τ₂ → do
      let tag₁ = annotatedTag τ₁
      let tag₂ = annotatedTag τ₂
      MinTE (Annotated tag₁ (map f (extract τ₁))) (Annotated tag₂ (map f (extract τ₂)))
    PlusTE τ₁ τ₂ → do
      let tag₁ = annotatedTag τ₁
      let tag₂ = annotatedTag τ₂
      PlusTE (Annotated tag₁ (map f (extract τ₁))) (Annotated tag₂ (map f (extract τ₂)))
    TimesTE τ₁ τ₂ → do
      let tag₁ = annotatedTag τ₁
      let tag₂ = annotatedTag τ₂
      TimesTE (Annotated tag₁ (map f (extract τ₁))) (Annotated tag₂ (map f (extract τ₂)))
    DivTE τ₁ τ₂ → do
      let tag₁ = annotatedTag τ₁
      let tag₂ = annotatedTag τ₂
      DivTE (Annotated tag₁ (map f (extract τ₁))) (Annotated tag₂ (map f (extract τ₂)))
    RootTE τ →  do
      let tag = annotatedTag τ
      RootTE (Annotated tag (map f (extract τ)))
    LogTE τ →  do
      let tag = annotatedTag τ
      LogTE (Annotated tag (map f (extract τ)))
    TopTE → TopTE
    EmptyTE → EmptyTE
    ConsTE τ₁ τ₂ → do
      let tag₁ = annotatedTag τ₁
      let tag₂ = annotatedTag τ₂
      ConsTE (Annotated tag₁ (map f (extract τ₁))) (Annotated tag₂ (map f (extract τ₂)))
    AppendTE τ₁ τ₂ → do
      let tag₁ = annotatedTag τ₁
      let tag₂ = annotatedTag τ₂
      AppendTE (Annotated tag₁ (map f (extract τ₁))) (Annotated tag₂ (map f (extract τ₂)))
    RexpTE τ₁ τ₂ → do
      let tag₁ = annotatedTag τ₁
      let tag₂ = annotatedTag τ₂
      RexpTE (Annotated tag₁ (map f (extract τ₁))) (Annotated tag₂ (map f (extract τ₂)))

freshenTL ∷ (𝕏 ⇰ 𝕏) → (𝕏 ⇰ 𝕏) → TLExp RNF → ℕ → (TLExp RNF ∧ ℕ)
freshenTL ρ β τ''' n =
  let nplusone = n + one in
  let tag = annotatedTag τ''' in
  let (z :* nFinal) = case (extract τ''') of
        ℕˢTE r → (ℕˢTE (substAlphaRNF (list ρ) r)) :* n
        ℝˢTE r → (ℝˢTE (substAlphaRNF (list ρ) r)) :* n
        ℕTE → (ℕTE :* n)
        ℝTE → (ℝTE :* n)
        𝕀TE r → (𝕀TE (substAlphaRNF (list ρ) r)) :* n
        𝔹TE → (𝔹TE :* n)
        𝕊TE → (𝕊TE :* n)
        SetTE τ → do
          let (τ' :* n') = freshenTL ρ β τ n
          (SetTE τ') :* n'
        𝕄TE l c rows cols →
          let rows' = case rows of
                        StarRT → StarRT
                        RexpRT r → RexpRT (substAlphaRNF (list ρ) r)
          in let (cols' :* n') = (freshenMExp ρ β cols n)
          in (𝕄TE l c rows' cols') :* n'
        𝔻TE τ → do
          let (τ' :* n') = freshenTL ρ β τ n
          (𝔻TE τ') :* n'
        τ₁ :⊕♭: τ₂ →
          let (τ₁' :* n') = freshenTL ρ β τ₁ n in
          let (τ₂' :* n'') = freshenTL ρ β τ₂ n' in
          (τ₁' :⊕♭: τ₂') :* n''
        τ₁ :⊗♭: τ₂ →
          let (τ₁' :* n') = freshenTL ρ β τ₁ n in
          let (τ₂' :* n'') = freshenTL ρ β τ₂ n' in
          (τ₁' :⊗♭: τ₂') :* n''
        (τ₁ :* σ₁) :&♭: (σ₂ :* τ₂) →
          let (τ₁' :* n') = freshenTL ρ β τ₁ n in
          let σ₁' = (mapp (\r → substAlphaRNF (list ρ) r) σ₁) in
          let σ₁'' = assoc $ map (\(TMVar x :* s) → TMVar (freshenVar β x) :* s) $ list σ₁' in
          let (τ₂' :* n'') = freshenTL ρ β τ₂ n' in
          let σ₂' = (mapp (\r → substAlphaRNF (list ρ) r) σ₂) in
          let σ₂'' = assoc $ map (\(TMVar x :* s) → TMVar (freshenVar β x) :* s) $ list σ₂' in
          ((τ₁' :* σ₁'') :&♭: (σ₂'' :* τ₂')) :* n''
        (τ₁ :* σ₁) :⊞♭: (σ₂ :* τ₂) →
          let (τ₁' :* n') = freshenTL ρ β τ₁ n in
          let σ₁' = (mapp (\r → substAlphaRNF (list ρ) r) σ₁) in
          let σ₁'' = assoc $ map (\(TMVar x :* s) → TMVar (freshenVar β x) :* s) $ list σ₁' in
          let (τ₂' :* n'') = freshenTL ρ β τ₂ n' in
          let σ₂' = (mapp (\r → substAlphaRNF (list ρ) r) σ₂) in
          let σ₂'' = assoc $ map (\(TMVar x :* s) → TMVar (freshenVar β x) :* s) $ list σ₂' in
          ((τ₁' :* σ₁'') :⊞♭: (σ₂'' :* τ₂')) :* n''
        (τ₁ :* σ₁) :⊠♭: (σ₂ :* τ₂) →
          let (τ₁' :* n') = freshenTL ρ β τ₁ n in
          let σ₁' = (mapp (\r → substAlphaRNF (list ρ) r) σ₁) in
          let σ₁'' = assoc $ map (\(TMVar x :* s) → TMVar (freshenVar β x) :* s) $ list σ₁' in
          let (τ₂' :* n'') = freshenTL ρ β τ₂ n' in
          let σ₂' = (mapp (\r → substAlphaRNF (list ρ) r) σ₂) in
          let σ₂'' = assoc $ map (\(TMVar x :* s) → TMVar (freshenVar β x) :* s) $ list σ₂' in
          ((τ₁' :* σ₁'') :⊠♭: (σ₂'' :* τ₂')) :* n''
        (x₁ :* τ₁) :⊸♭: (sσ₁ :* τ₂) →
          let x₁ⁿ = 𝕏 {𝕩name=(𝕩name x₁), 𝕩Gen=Some n} in
          let (τ₁' :* n') = freshenTL ρ ((x₁↦ x₁ⁿ) ⩌ β) τ₁ nplusone in
          let (τ₂' :* n'') = freshenTL ρ ((x₁↦ x₁ⁿ) ⩌ β) τ₂ n' in
          let sσ₁' = (mapp (\r → substAlphaRNF (list ρ) r) sσ₁) in
          let sσ₁'' ∷ (ProgramVar ⇰ _) = assoc $ map (\(x :* s) → freshenRef ρ ((x₁↦ x₁ⁿ) ⩌ β) x :* s) $ list sσ₁' in
          ((x₁ⁿ :* τ₁') :⊸♭: (sσ₁'' :* τ₂') :* n'')
        (x₁ :* τ₁ :* s) :⊸⋆♭: (PEnv pσ₁ :* τ₂) →
          let x₁ⁿ = 𝕏 {𝕩name=(𝕩name x₁), 𝕩Gen=Some n} in
          let (τ₁' :* n') = freshenTL ρ ((x₁↦ x₁ⁿ) ⩌ β) τ₁ nplusone in
          let (τ₂' :* n'') = freshenTL ρ ((x₁↦ x₁ⁿ) ⩌ β) τ₂ n' in
          let s' = map (substAlphaRNF (list ρ)) s in
          let pσ₁' = (mapp (\r → substAlphaRNF (list ρ) r) pσ₁) in
          let pσ₁'' = assoc $ map (\(x :* p) → freshenRef ρ ((x₁↦ x₁ⁿ) ⩌ β) x :* p) $ list pσ₁' in
          ((x₁ⁿ :* τ₁' :* s') :⊸⋆♭: (PEnv pσ₁'' :* τ₂') :* n'')
        ForallTE x κ τ →
          let xⁿ = 𝕏 {𝕩name=(𝕩name x), 𝕩Gen=Some n} in
          let (τ' :* n') = freshenTL ((x↦ xⁿ) ⩌ ρ) β τ nplusone in
          (ForallTE xⁿ κ τ' ) :* n'
        CxtTE xs → do
          let xs' = pow $ map (\x → freshenRef ρ β x) $ list xs
          (CxtTE xs' :* n)
        UnitTE → UnitTE :* n
        VarTE x → (VarTE $ getTLVar $ freshenRef ρ β (TLVar x)) :* n
        NatTE η → NatTE η :* n
        NNRealTE d → NNRealTE d :* n
        MaxTE τ₁ τ₂ →
          let (τ₁' :* n') = freshenTL ρ β τ₁ n in
          let (τ₂' :* n'') = freshenTL ρ β τ₂ n' in
          (MaxTE τ₁' τ₂') :* n''
        MinTE τ₁ τ₂ →
          let (τ₁' :* n') = freshenTL ρ β τ₁ n in
          let (τ₂' :* n'') = freshenTL ρ β τ₂ n' in
          (MinTE τ₁' τ₂') :* n''
        PlusTE τ₁ τ₂ →
          let (τ₁' :* n') = freshenTL ρ β τ₁ n in
          let (τ₂' :* n'') = freshenTL ρ β τ₂ n' in
          (PlusTE τ₁' τ₂') :* n''
        TimesTE τ₁ τ₂ →
          let (τ₁' :* n') = freshenTL ρ β τ₁ n in
          let (τ₂' :* n'') = freshenTL ρ β τ₂ n' in
          (TimesTE τ₁' τ₂') :* n''
        DivTE τ₁ τ₂ →
          let (τ₁' :* n') = freshenTL ρ β τ₁ n in
          let (τ₂' :* n'') = freshenTL ρ β τ₂ n' in
          (DivTE τ₁' τ₂') :* n''
        RootTE τ →
          let (τ' :* n') = freshenTL ρ β τ n in
          (RootTE τ') :* n'
        LogTE τ →
          let (τ' :* n') = freshenTL ρ β τ n in
          (LogTE τ') :* n'
        TopTE → TopTE :* n
        EmptyTE → EmptyTE :* n
        ConsTE τ₁ τ₂ →
          let (τ₁' :* n') = freshenTL ρ β τ₁ n in
          let (τ₂' :* n'') = freshenTL ρ β τ₂ n' in
          (ConsTE τ₁' τ₂') :* n''
        AppendTE τ₁ τ₂ →
          let (τ₁' :* n') = freshenTL ρ β τ₁ n in
          let (τ₂' :* n'') = freshenTL ρ β τ₂ n' in
          (AppendTE τ₁' τ₂') :* n''
        RexpTE τ₁ τ₂ →
          let (τ₁' :* n') = freshenTL ρ β τ₁ n in
          let (τ₂' :* n'') = freshenTL ρ β τ₂ n' in
          (RexpTE τ₁' τ₂') :* n''
  in
  (Annotated tag z) :* nFinal

freshenType ∷ (𝕏 ⇰ 𝕏) → (𝕏 ⇰ 𝕏) → Type RNF → ℕ → (Type RNF ∧ ℕ)
freshenType ρ β τ''' n = let nplusone = n + one in
  case τ''' of
    VarT x → (VarT $ getTLVar $ freshenRef ρ β (TLVar x)) :* n
    ℕˢT r → (ℕˢT (substAlphaRNF (list ρ) r)) :* n
    ℝˢT r → (ℝˢT (substAlphaRNF (list ρ) r)) :* n
    ℕT → (ℕT :* n)
    ℝT → (ℝT :* n)
    𝕀T r → (𝕀T (substAlphaRNF (list ρ) r)) :* n
    𝔹T → (𝔹T :* n)
    𝕊T → (𝕊T :* n)
    SetT τ → let (τ' :* n') = freshenType ρ β τ n
      in (SetT τ') :* n'
    𝕄T l c rows cols →
      let rows' = case rows of
                    StarRT → StarRT
                    RexpRT r → RexpRT (substAlphaRNF (list ρ) r)
      in let (cols' :* n') = (freshenMExp ρ β cols n)
      in (𝕄T l c rows' cols') :* n'
    𝔻T τ → let (τ' :* n') = freshenType ρ β τ n
      in (𝔻T τ') :* n'
    τ₁ :⊕: τ₂ →
      let (τ₁' :* n') = freshenType ρ β τ₁ n in
      let (τ₂' :* n'') = freshenType ρ β τ₂ n' in
      (τ₁' :⊕: τ₂') :* n''
    τ₁ :⊗: τ₂ →
      let (τ₁' :* n') = freshenType ρ β τ₁ n in
      let (τ₂' :* n'') = freshenType ρ β τ₂ n' in
      (τ₁' :⊗: τ₂') :* n''
    (τ₁ :* σ₁) :&: (σ₂ :* τ₂) →
      let (τ₁' :* n') = freshenType ρ β τ₁ n in
      let σ₁' = (mapp (\r → substAlphaRNF (list ρ) r) σ₁) in
      let σ₁'' = assoc $ map (\(TMVar x :* s) → TMVar (freshenVar β x) :* s) $ list σ₁' in
      let (τ₂' :* n'') = freshenType ρ β τ₂ n' in
      let σ₂' = (mapp (\r → substAlphaRNF (list ρ) r) σ₂) in
      let σ₂'' = assoc $ map (\(TMVar x :* s) → TMVar (freshenVar β x) :* s) $ list σ₂' in
      ((τ₁' :* σ₁'') :&: (σ₂'' :* τ₂')) :* n''
    (τ₁ :* σ₁) :⊞: (σ₂ :* τ₂) →
      let (τ₁' :* n') = freshenType ρ β τ₁ n in
      let σ₁' = (mapp (\r → substAlphaRNF (list ρ) r) σ₁) in
      let σ₁'' = assoc $ map (\(TMVar x :* s) → TMVar (freshenVar β x) :* s) $ list σ₁' in
      let (τ₂' :* n'') = freshenType ρ β τ₂ n' in
      let σ₂' = (mapp (\r → substAlphaRNF (list ρ) r) σ₂) in
      let σ₂'' = assoc $ map (\(TMVar x :* s) → TMVar (freshenVar β x) :* s) $ list σ₂' in
      ((τ₁' :* σ₁'') :⊞: (σ₂'' :* τ₂')) :* n''
    (τ₁ :* σ₁) :⊠: (σ₂ :* τ₂) →
      let (τ₁' :* n') = freshenType ρ β τ₁ n in
      let σ₁' = (mapp (\r → substAlphaRNF (list ρ) r) σ₁) in
      let σ₁'' = assoc $ map (\(TMVar x :* s) → TMVar (freshenVar β x) :* s) $ list σ₁' in
      let (τ₂' :* n'') = freshenType ρ β τ₂ n' in
      let σ₂' = (mapp (\r → substAlphaRNF (list ρ) r) σ₂) in
      let σ₂'' = assoc $ map (\(TMVar x :* s) → TMVar (freshenVar β x) :* s) $ list σ₂' in
      ((τ₁' :* σ₁'') :⊠: (σ₂'' :* τ₂')) :* n''
    (x₁ :* τ₁) :⊸: (sσ₁ :* τ₂) →
      let x₁ⁿ = 𝕏 {𝕩name=(𝕩name x₁), 𝕩Gen=Some n} in
      let (τ₁' :* n') = freshenType ρ ((x₁↦ x₁ⁿ) ⩌ β) τ₁ nplusone in
      let (τ₂' :* n'') = freshenType ρ ((x₁↦ x₁ⁿ) ⩌ β) τ₂ n' in
      let sσ₁' = (mapp (\r → substAlphaRNF (list ρ) r) sσ₁) in
      let sσ₁'' ∷ (ProgramVar ⇰ _) = assoc $ map (\(x :* s) → freshenRef ρ ((x₁↦ x₁ⁿ) ⩌ β) x :* s) $ list sσ₁' in
      ((x₁ⁿ :* τ₁') :⊸: (sσ₁'' :* τ₂') :* n'')
    (x₁ :* τ₁ :* s) :⊸⋆: (PEnv (pσ₁ ∷ ProgramVar ⇰ Pr p RNF) :* τ₂) →
      let x₁ⁿ = 𝕏 {𝕩name=(𝕩name x₁), 𝕩Gen=Some n} in
      let (τ₁' :* n') = freshenType ρ ((x₁↦ x₁ⁿ) ⩌ β) τ₁ nplusone in
      let s' = map (substAlphaRNF (list ρ)) s in
      let (τ₂' :* n'') = freshenType ρ ((x₁↦ x₁ⁿ) ⩌ β) τ₂ n' in
      let pσ₁' = (mapp (\r → substAlphaRNF (list ρ) r) pσ₁) in
      let pσ₁'' = assoc $ map (\(x :* p) → freshenRef ρ ((x₁↦ x₁ⁿ) ⩌ β) x :* p) $ list pσ₁' in
      ((x₁ⁿ :* τ₁' :* s') :⊸⋆: (PEnv pσ₁'' :* τ₂') :* n'')
    ForallT x κ τ →
      let xⁿ = 𝕏 {𝕩name=(𝕩name x), 𝕩Gen=Some n} in
      let (τ' :* n') = freshenType ((x↦ xⁿ) ⩌ ρ) β τ nplusone in
      (ForallT xⁿ κ τ' ) :* n'
    CxtT xs → do
      let xs' = pow $ map (\x → freshenRef ρ β x) $ list xs
      (CxtT xs' :* n)
    BoxedT sσ₁ τ₁ → undefined
    UnitT → UnitT :* n

substAlphaRExp ∷ 𝐿 (𝕏 ∧ 𝕏) → RExp → RExp
substAlphaRExp Nil r = r
substAlphaRExp ((x₁:*x₂):&ρ) r = substAlphaRExp ρ $ substRExp x₁ (varRE x₂) r

substAlphaRNF ∷ 𝐿 (𝕏 ∧ 𝕏) → RNF → RNF
substAlphaRNF Nil r = r
substAlphaRNF ((x₁:*x₂):&ρ) r = substAlphaRNF ρ $ substRNF x₁ (varRNF x₂) r

freshenVar ∷ (𝕏 ⇰ 𝕏) → 𝕏 → 𝕏
freshenVar β x = case β ⋕? x of
  None → x
  Some x' → x'

freshenRef ∷ (𝕏 ⇰ 𝕏) → (𝕏 ⇰ 𝕏) → ProgramVar → ProgramVar
freshenRef ρ β tv = case tv of
  TLVar tlx → case ρ ⋕? tlx of
    None → TLVar tlx
    Some x' → TLVar x'
  TMVar plx → case β ⋕? plx of
    None → TMVar plx
    Some x' → TMVar x'

getTLVar ∷ ProgramVar → 𝕏
getTLVar (TLVar x) = x
getTLVar _ = error "expected TLVar"

getVar ∷ ProgramVar → 𝕏
getVar (TLVar x) = x
getVar (TMVar x) = x

freshenMExp ∷ (𝕏 ⇰ 𝕏) → (𝕏 ⇰ 𝕏) → MExp RNF → ℕ → (MExp RNF ∧ ℕ)
freshenMExp ρ β meInit n = case meInit of
  EmptyME → EmptyME :* n
  VarME x → (VarME $ freshenVar ρ x) :* n
  ConsME τ me →
    let (τ' :* n') =  (freshenType ρ β τ n) in
    let (me' :* n'') = (freshenMExp ρ β me n')
    in (ConsME τ' me') :* n''
  AppendME me₁ me₂ →
    let (me₁' :* n') = (freshenMExp ρ β me₁ n) in
    let (me₂' :* n'') = (freshenMExp ρ β me₂ n')
    in (AppendME me₁' me₂') :* n''
  RexpME r τ →
    let (τ' :* n') =  (freshenType ρ β τ n) in
    (RexpME (substAlphaRNF (list ρ) r) τ') :* n'

alphaEquiv ∷ (𝕏 ⇰ 𝕏) → (𝕏 ⇰ 𝕏) → Type RNF → Type RNF → 𝔹
alphaEquiv ρ β τ₁' τ₂' =
  case (τ₁',τ₂') of
    (VarT x₁,VarT x₂) → case ρ ⋕? x₁ of
      Some x₁' → x₁' ≡ x₂
      None → x₁ ≡ x₂
    (ℕˢT r₁,ℕˢT r₂) → (substAlphaRNF (list ρ) r₁) ≡ r₂
    (ℝˢT r₁,ℝˢT r₂) → (substAlphaRNF (list ρ) r₁) ≡ r₂
    (ℕT,ℕT) → True
    (ℝT,ℝT) → True
    (𝕀T r₁,𝕀T r₂) → (substAlphaRNF (list ρ) r₁) ≡ r₂
    (𝔹T,𝔹T) → True
    (𝕊T,𝕊T) → True
    (SetT τ₁,SetT τ₂) → alphaEquiv ρ β τ₁ τ₂
    (𝕄T l₁ c₁ rows₁ cols₁,𝕄T l₂ c₂ rows₂ cols₂) → case (l₁≡l₂,c₁≡c₂) of
      (True,True) → (alphaEquivRows ρ rows₁ rows₂) ⩓ (alphaEquivMExp ρ β cols₁ cols₂)
      _ → False
    (𝔻T τ₁,𝔻T τ₂) → alphaEquiv ρ β τ₁ τ₂
    (τ₁₁ :⊕: τ₁₂,τ₂₁ :⊕: τ₂₂) → (alphaEquiv ρ β τ₁₁ τ₂₁) ⩓ (alphaEquiv ρ β τ₁₂ τ₂₂)
    (τ₁₁ :⊗: τ₁₂,τ₂₁ :⊗: τ₂₂) → (alphaEquiv ρ β τ₁₁ τ₂₁) ⩓ (alphaEquiv ρ β τ₁₂ τ₂₂)
    ((τ₁₁ :* σ₁₁) :&: (σ₁₂ :* τ₁₂),(τ₂₁ :* σ₂₁) :&: (σ₂₂ :* τ₂₂)) → do
      let c₁ = (alphaEquiv ρ β τ₁₁ τ₂₁) ⩓ (alphaEquiv ρ β τ₁₂ τ₂₂)
      let σ₁₁' = (mapp (\r → substAlphaRNF (list ρ) r) σ₁₁)
      let σ₁₁'' = assoc $ map (\(TMVar x :* s) → TMVar (freshenVar β x) :* s) $ list σ₁₁'
      let σ₁₂' = (mapp (\r → substAlphaRNF (list ρ) r) σ₁₂)
      let σ₁₂'' = assoc $ map (\(TMVar x :* s) → TMVar (freshenVar β x) :* s) $ list σ₁₂'
      let c₂ = (σ₁₁'' ≡ σ₂₁)
      let c₃ = (σ₁₂'' ≡ σ₂₂)
      c₁ ⩓ c₂ ⩓ c₃
    ((τ₁₁ :* σ₁₁) :⊞: (σ₁₂ :* τ₁₂),(τ₂₁ :* σ₂₁) :⊞: (σ₂₂ :* τ₂₂)) → do
      let c₁ = (alphaEquiv ρ β τ₁₁ τ₂₁) ⩓ (alphaEquiv ρ β τ₁₂ τ₂₂)
      let σ₁₁' = (mapp (\r → substAlphaRNF (list ρ) r) σ₁₁)
      let σ₁₁'' = assoc $ map (\(TMVar x :* s) → TMVar (freshenVar β x) :* s) $ list σ₁₁'
      let σ₁₂' = (mapp (\r → substAlphaRNF (list ρ) r) σ₁₂)
      let σ₁₂'' = assoc $ map (\(TMVar x :* s) → TMVar (freshenVar β x) :* s) $ list σ₁₂'
      let c₂ = (σ₁₁'' ≡ σ₂₁)
      let c₃ = (σ₁₂'' ≡ σ₂₂)
      c₁ ⩓ c₂ ⩓ c₃
    ((τ₁₁ :* σ₁₁) :⊠: (σ₁₂ :* τ₁₂),(τ₂₁ :* σ₂₁) :⊠: (σ₂₂ :* τ₂₂)) → do
      let c₁ = (alphaEquiv ρ β τ₁₁ τ₂₁) ⩓ (alphaEquiv ρ β τ₁₂ τ₂₂)
      let σ₁₁' = (mapp (\r → substAlphaRNF (list ρ) r) σ₁₁)
      let σ₁₁'' = assoc $ map (\(TMVar x :* s) → TMVar (freshenVar β x) :* s) $ list σ₁₁'
      let σ₁₂' = (mapp (\r → substAlphaRNF (list ρ) r) σ₁₂)
      let σ₁₂'' = assoc $ map (\(TMVar x :* s) → TMVar (freshenVar β x) :* s) $ list σ₁₂'
      let c₂ = (σ₁₁'' ≡ σ₂₁)
      let c₃ = (σ₁₂'' ≡ σ₂₂)
      c₁ ⩓ c₂ ⩓ c₃
    ((x₁ :* τ₁₁) :⊸: (sσ₁ :* τ₁₂),(x₂ :* τ₂₁) :⊸: (sσ₂ :* τ₂₂)) → do
      let sσ₁' = (mapp (\r → substAlphaRNF (list ρ) r) sσ₁)
      let sσ₁'' ∷ (ProgramVar ⇰ _) = assoc $ map (\(x :* s) → freshenRef ρ ((x₁↦ x₂) ⩌ β) x :* s) $ list sσ₁'
      let c₁ = (alphaEquiv ρ ((x₁ ↦ x₂) ⩌ β) τ₁₁ τ₂₁)
      let c₂ = (alphaEquiv ρ ((x₁ ↦ x₂) ⩌ β) τ₁₂ τ₂₂)
      let c₃ = (sσ₁'' ≡ sσ₂)
      c₁ ⩓ c₂ ⩓ c₃
    ((x₁ :* τ₁₁ :* s₁) :⊸⋆: (PEnv (pσ₁ ∷ ProgramVar ⇰ Pr p RNF) :* τ₁₂),(x₂ :* τ₂₁ :* s₂) :⊸⋆: (PEnv (pσ₂ ∷ ProgramVar ⇰ Pr p' RNF) :* τ₂₂)) →
      case eqPRIV (priv @ p) (priv @ p') of
        None → False
        Some Refl →
          let pσ₁' = (mapp (\r → substAlphaRNF (list ρ) r) pσ₁) in
          let pσ₁'' ∷ (ProgramVar ⇰ _) = assoc $ map (\(x :* p) → freshenRef ρ ((x₁↦ x₂) ⩌ β) x :* p) $ list pσ₁' in
          let s₁' = map (substAlphaRNF (list ρ)) s₁ in
          let c₁ = (alphaEquiv ρ ((x₁ ↦ x₂) ⩌ β) τ₁₁ τ₂₁) in
          let c₂ = (alphaEquiv ρ ((x₁ ↦ x₂) ⩌ β) τ₁₂ τ₂₂) in
          let c₃ = (pσ₁'' ≡ pσ₂) in
          let c₄ = (s₁' ≡ s₂) in
          c₁ ⩓ c₂ ⩓ c₃ ⩓ c₄
    (ForallT x₁ κ₁ τ₁,ForallT x₂ κ₂ τ₂) → case (κ₁ ≡ κ₂) of
      True → alphaEquiv ((x₁↦x₂) ⩌ ρ) β τ₁ τ₂
      False → False
    (CxtT xs₁,CxtT xs₂) → xs₁ ≡ xs₂
    (UnitT, UnitT) → True
    (BoxedT sσ₁ τ₁,BoxedT sσ₂ τ₂) → undefined
    _ → False

alphaEquivMExp ∷ (𝕏 ⇰ 𝕏) → (𝕏 ⇰ 𝕏) → MExp RNF → MExp RNF → 𝔹
alphaEquivMExp ρ β me₁' me₂' = case (me₁',me₂') of
  (EmptyME,EmptyME) → True
  (VarME x₁,VarME x₂) → x₁ ≡ x₂
  (ConsME τ₁ me₁,ConsME τ₂ me₂) → (alphaEquiv ρ β τ₁ τ₂) ⩓ (alphaEquivMExp ρ β me₁ me₂)
  (AppendME me₁₁ me₁₂,AppendME me₂₁ me₂₂) → (alphaEquivMExp ρ β me₁₁ me₂₁) ⩓ (alphaEquivMExp ρ β me₁₂ me₂₂)
  (RexpME r₁ τ₁,RexpME r₂ τ₂) → ((substAlphaRNF (list ρ) r₁) ≡ r₂) ⩓ (alphaEquiv ρ β τ₁ τ₂)
  _ → False

alphaEquivRows ∷ (𝕏 ⇰ 𝕏) → RowsT RNF → RowsT RNF → 𝔹
alphaEquivRows ρ rows₁ rows₂ = case (rows₁,rows₂) of
  (StarRT, StarRT) → True
  (RexpRT r₁, RexpRT r₂) → (substAlphaRNF (list ρ) r₁) ≡ r₂
  _ → False

tyJoinMExp ∷ (𝕏 ⇰ 𝕏) → (𝕏 ⇰ 𝕏) → MExp RNF → MExp RNF → 𝑂 (MExp RNF)
tyJoinMExp ρ β me₁' me₂' = case (me₁',me₂') of
  (EmptyME,EmptyME) → return EmptyME
  (VarME x₁,VarME x₂) | x₁ ≡ x₂ → return $ VarME x₁
  (ConsME τ₁ me₁,ConsME τ₂ me₂) → do
    τa ← tyJoin ρ β τ₁ τ₂
    mea ← tyJoinMExp ρ β me₁ me₂
    return $ ConsME τa mea
  (AppendME me₁₁ me₁₂,AppendME me₂₁ me₂₂) → do
    mea ← tyJoinMExp ρ β me₁₁ me₂₁
    meb ← tyJoinMExp ρ β me₁₂ me₂₂
    return $ AppendME mea meb
  (RexpME r₁ τ₁,RexpME r₂ τ₂) | r₁ ≡ r₂ → do
    τa ← tyJoin ρ β τ₁ τ₂
    return $ RexpME r₁ τa
  _ → None

tyJoinRows ∷ (𝕏 ⇰ 𝕏) → RowsT RNF → RowsT RNF → 𝑂 (RowsT RNF)
tyJoinRows ρ rows₁ rows₂ = case (rows₁,rows₂) of
  (StarRT, StarRT) → return StarRT
  (RexpRT r₁, RexpRT r₂) | (substAlphaRNF (list ρ) r₁) ≡ r₂ → return $ RexpRT r₂
  _ → None

tyJoin ∷ (𝕏 ⇰ 𝕏) → (𝕏 ⇰ 𝕏) → Type RNF → Type RNF → 𝑂(Type RNF)
tyJoin ρ β τ₁' τ₂' =
  case (τ₁',τ₂') of
    (VarT x₁,VarT x₂)→ case ρ ⋕? x₁ of
      Some x₁' → case x₁' ≡ x₂ of
        False → None
        True → return $ VarT x₂
      None → case x₁ ≡ x₂ of
        False → None
        True → return $ VarT x₂
    (ℕˢT r₁,ℕˢT r₂) | (substAlphaRNF (list ρ) r₁) ≡ r₂ → do
      return $ ℕˢT r₂
    (ℝˢT r₁,ℝˢT r₂) | (substAlphaRNF (list ρ) r₁) ≡ r₂ → return $ ℝˢT r₂
    (ℕT,ℕT) → return $ ℕT
    (ℝT,ℝT) → return $ ℝT
    (𝕀T r₁,𝕀T r₂) | (substAlphaRNF (list ρ) r₁) ≡ r₂ → return $ 𝕀T r₂
    (𝔹T,𝔹T) → return $ 𝔹T
    (𝕊T,𝕊T) → return $ 𝕊T
    (SetT τ₁,SetT τ₂) → do
      τa ← tyJoin ρ β τ₁ τ₂
      return $ SetT τa
    --TODO: rows, cols
    (𝕄T l₁ c₁ rows₁ cols₁,𝕄T l₂ c₂ rows₂ cols₂) | (l₁≡l₂) ⩓ (c₁≡c₂) ⩓ (c₁≡c₂) → do
      rowsa ← tyJoinRows ρ rows₁ rows₂
      colsa ← tyJoinMExp ρ β cols₁ cols₂
      return $ (𝕄T l₁ c₁ rowsa colsa)
    (𝔻T τ₁,𝔻T τ₂) → do
      τa ← tyJoin ρ β τ₁ τ₂
      return $ 𝔻T τa
    (τ₁₁ :⊕: τ₁₂,τ₂₁ :⊕: τ₂₂) → do
      τa ← tyJoin ρ β τ₁₁ τ₂₁
      τb ← tyJoin ρ β τ₁₂ τ₂₂
      return $ τa :⊕: τb
    (τ₁₁ :⊗: τ₁₂,τ₂₁ :⊗: τ₂₂) → do
      τa ← tyJoin ρ β τ₁₁ τ₂₁
      τb ← tyJoin ρ β τ₁₂ τ₂₂
      return $ τa :⊗: τb
    ((τ₁₁ :* σ₁₁) :&: (σ₁₂ :* τ₁₂),(τ₂₁ :* σ₂₁) :&: (σ₂₂ :* τ₂₂)) → do
      τa ← tyJoin ρ β τ₁₁ τ₂₁
      τb ← tyJoin ρ β τ₁₂ τ₂₂
      let σ₁₁' = (mapp (\r → substAlphaRNF (list ρ) r) σ₁₁)
      let σ₁₁'' = assoc $ map (\(TMVar x :* s) → TMVar (freshenVar β x) :* s) $ list σ₁₁'
      let σ₁₂' = (mapp (\r → substAlphaRNF (list ρ) r) σ₁₂)
      let σ₁₂'' = assoc $ map (\(TMVar x :* s) → TMVar (freshenVar β x) :* s) $ list σ₁₂'
      let σa = σ₁₁'' ⊔ σ₂₁
      let σb = σ₁₂'' ⊔ σ₂₂
      return $ (τa :* σa) :&: (σb :* τb)
    ((τ₁₁ :* σ₁₁) :⊞: (σ₁₂ :* τ₁₂),(τ₂₁ :* σ₂₁) :⊞: (σ₂₂ :* τ₂₂)) → do
      τa ← tyJoin ρ β τ₁₁ τ₂₁
      τb ← tyJoin ρ β τ₁₂ τ₂₂
      let σ₁₁' = (mapp (\r → substAlphaRNF (list ρ) r) σ₁₁)
      let σ₁₁'' = assoc $ map (\(TMVar x :* s) → TMVar (freshenVar β x) :* s) $ list σ₁₁'
      let σ₁₂' = (mapp (\r → substAlphaRNF (list ρ) r) σ₁₂)
      let σ₁₂'' = assoc $ map (\(TMVar x :* s) → TMVar (freshenVar β x) :* s) $ list σ₁₂'
      let σa = σ₁₁'' ⊔ σ₂₁
      let σb = σ₁₂'' ⊔ σ₂₂
      return $ (τa :* σa) :⊞: (σb :* τb)
    ((τ₁₁ :* σ₁₁) :⊠: (σ₁₂ :* τ₁₂),(τ₂₁ :* σ₂₁) :⊠: (σ₂₂ :* τ₂₂)) → do
      τa ← tyJoin ρ β τ₁₁ τ₂₁
      τb ← tyJoin ρ β τ₁₂ τ₂₂
      let σ₁₁' = (mapp (\r → substAlphaRNF (list ρ) r) σ₁₁)
      let σ₁₁'' = assoc $ map (\(TMVar x :* s) → TMVar (freshenVar β x) :* s) $ list σ₁₁'
      let σ₁₂' = (mapp (\r → substAlphaRNF (list ρ) r) σ₁₂)
      let σ₁₂'' = assoc $ map (\(TMVar x :* s) → TMVar (freshenVar β x) :* s) $ list σ₁₂'
      let σa = σ₁₁'' ⊔ σ₂₁
      let σb = σ₁₂'' ⊔ σ₂₂
      return $ (τa :* σa) :⊠: (σb :* τb)
    ((x₁ :* τ₁₁) :⊸: (sσ₁ :* τ₁₂),(x₂ :* τ₂₁) :⊸: (sσ₂ :* τ₂₂)) → do
      τa ← tyMeet ρ ((x₁ ↦ x₂) ⩌ β) τ₁₁ τ₂₁
      τb ← tyJoin ρ ((x₁ ↦ x₂) ⩌ β) τ₁₂ τ₂₂
      let sσ₁' = (mapp (\r → substAlphaRNF (list ρ) r) sσ₁)
      let sσ₁'' ∷ (ProgramVar ⇰ _) = assoc $ map (\(x :* s) → freshenRef ρ ((x₁↦ x₂) ⩌ β) x :* s) $ list sσ₁'
      let σa = sσ₁'' ⊔ sσ₂
      return $ (x₁ :* τa) :⊸: (σa :* τb)
    ((x₁ :* τ₁₁ :* s₁) :⊸⋆: (PEnv (pσ₁ ∷ ProgramVar ⇰ Pr p RNF) :* τ₁₂),(x₂ :* τ₂₁ :* s₂) :⊸⋆: (PEnv (pσ₂ ∷ ProgramVar ⇰ Pr p' RNF) :* τ₂₂)) →
      case eqPRIV (priv @ p) (priv @ p') of
        None → None
        Some Refl → do
          τa ← tyMeet ρ ((x₁ ↦ x₂) ⩌ β) τ₁₁ τ₂₁
          τb ← tyJoin ρ ((x₁ ↦ x₂) ⩌ β) τ₁₂ τ₂₂
          let pσ₁' = (mapp (\r → substAlphaRNF (list ρ) r) pσ₁)
          let pσ₁'' ∷ (ProgramVar ⇰ _) = assoc $ map (\(x :* p) → freshenRef ρ ((x₁↦ x₂) ⩌ β) x :* p) $ list pσ₁'
          let s₁' = map (substAlphaRNF (list ρ)) s₁
          let σa = pσ₁'' ⊔ pσ₂
          return $ (x₁ :* τa :* s₁') :⊸⋆: (PEnv (σa ∷ ProgramVar ⇰ Pr p RNF) :* τb)
    (ForallT x₁ κ₁ τ₁,ForallT x₂ κ₂ τ₂) | (κ₁ ≡ κ₂) → do
      τa ← tyJoin ((x₁↦x₂) ⩌ ρ) β τ₁ τ₂
      return $ ForallT x₂ κ₂ τa
    (CxtT xs₁,CxtT xs₂) | xs₁ ≡ xs₂ → return $ CxtT xs₂
    (UnitT, UnitT) → return $ UnitT
    (BoxedT sσ₁ τ₁,BoxedT sσ₂ τ₂) → undefined
    _ → None

tyMeetMExp ∷ (𝕏 ⇰ 𝕏) → (𝕏 ⇰ 𝕏) → MExp RNF → MExp RNF → 𝑂 (MExp RNF)
tyMeetMExp ρ β me₁' me₂' = case (me₁',me₂') of
  (EmptyME,EmptyME) → return EmptyME
  (VarME x₁,VarME x₂) | x₁ ≡ x₂ → return $ VarME x₁
  (ConsME τ₁ me₁,ConsME τ₂ me₂) → do
    τa ← tyMeet ρ β τ₁ τ₂
    mea ← tyMeetMExp ρ β me₁ me₂
    return $ ConsME τa mea
  (AppendME me₁₁ me₁₂,AppendME me₂₁ me₂₂) → do
    mea ← tyMeetMExp ρ β me₁₁ me₂₁
    meb ← tyMeetMExp ρ β me₁₂ me₂₂
    return $ AppendME mea meb
  (RexpME r₁ τ₁,RexpME r₂ τ₂) | r₁ ≡ r₂ → do
    τa ← tyMeet ρ β τ₁ τ₂
    return $ RexpME r₁ τa
  _ → None

tyMeetRows ∷ (𝕏 ⇰ 𝕏) → RowsT RNF → RowsT RNF → 𝑂 (RowsT RNF)
tyMeetRows ρ rows₁ rows₂ = case (rows₁,rows₂) of
  (StarRT, StarRT) → return StarRT
  (RexpRT r₁, RexpRT r₂) | (substAlphaRNF (list ρ) r₁) ≡ r₂ → return $ RexpRT r₂
  _ → None

tyMeet ∷ (𝕏 ⇰ 𝕏) → (𝕏 ⇰ 𝕏) → Type RNF → Type RNF → 𝑂(Type RNF)
tyMeet ρ β τ₁' τ₂' =
  case (τ₁',τ₂') of
    (VarT x₁,VarT x₂)→ case ρ ⋕? x₁ of
      Some x₁' → case x₁' ≡ x₂ of
        False → None
        True → return $ VarT x₂
      None → case x₁ ≡ x₂ of
        False → None
        True → return $ VarT x₂
    (ℕˢT r₁,ℕˢT r₂) | (substAlphaRNF (list ρ) r₁) ≡ r₂ → return $ ℕˢT r₂
    (ℝˢT r₁,ℝˢT r₂) | (substAlphaRNF (list ρ) r₁) ≡ r₂ → return $ ℝˢT r₂
    (ℕT,ℕT) → return $ ℕT
    (ℝT,ℝT) → return $ ℝT
    (𝕀T r₁,𝕀T r₂) | (substAlphaRNF (list ρ) r₁) ≡ r₂ → return $ 𝕀T r₂
    (𝔹T,𝔹T) → return $ 𝔹T
    (𝕊T,𝕊T) → return $ 𝕊T
    (SetT τ₁,SetT τ₂) → do
      τa ← tyMeet ρ β τ₁ τ₂
      return $ SetT τa
    --TODO: rows, cols
    (𝕄T l₁ c₁ rows₁ cols₁,𝕄T l₂ c₂ rows₂ cols₂) | (l₁≡l₂) ⩓ (c₁≡c₂) ⩓ (c₁≡c₂) → do
      rowsa ← tyMeetRows ρ rows₁ rows₂
      colsa ← tyMeetMExp ρ β cols₁ cols₂
      return $ (𝕄T l₁ c₁ rowsa colsa)
    (𝔻T τ₁,𝔻T τ₂) → do
      τa ← tyMeet ρ β τ₁ τ₂
      return $ 𝔻T τa
    (τ₁₁ :⊕: τ₁₂,τ₂₁ :⊕: τ₂₂) → do
      τa ← tyMeet ρ β τ₁₁ τ₂₁
      τb ← tyMeet ρ β τ₁₂ τ₂₂
      return $ τa :⊕: τb
    (τ₁₁ :⊗: τ₁₂,τ₂₁ :⊗: τ₂₂) → do
      τa ← tyMeet ρ β τ₁₁ τ₂₁
      τb ← tyMeet ρ β τ₁₂ τ₂₂
      return $ τa :⊗: τb
    ((τ₁₁ :* σ₁₁) :&: (σ₁₂ :* τ₁₂),(τ₂₁ :* σ₂₁) :&: (σ₂₂ :* τ₂₂)) → do
      τa ← tyMeet ρ β τ₁₁ τ₂₁
      τb ← tyMeet ρ β τ₁₂ τ₂₂
      let σ₁₁' = (mapp (\r → substAlphaRNF (list ρ) r) σ₁₁)
      let σ₁₁'' = assoc $ map (\(TMVar x :* s) → TMVar (freshenVar β x) :* s) $ list σ₁₁'
      let σ₁₂' = (mapp (\r → substAlphaRNF (list ρ) r) σ₁₂)
      let σ₁₂'' = assoc $ map (\(TMVar x :* s) → TMVar (freshenVar β x) :* s) $ list σ₁₂'
      let σa = σ₁₁'' ⊓ σ₂₁
      let σb = σ₁₂'' ⊓ σ₂₂
      return $ (τa :* σa) :&: (σb :* τb)
    ((τ₁₁ :* σ₁₁) :⊞: (σ₁₂ :* τ₁₂),(τ₂₁ :* σ₂₁) :⊞: (σ₂₂ :* τ₂₂)) → do
      τa ← tyMeet ρ β τ₁₁ τ₂₁
      τb ← tyMeet ρ β τ₁₂ τ₂₂
      let σ₁₁' = (mapp (\r → substAlphaRNF (list ρ) r) σ₁₁)
      let σ₁₁'' = assoc $ map (\(TMVar x :* s) → TMVar (freshenVar β x) :* s) $ list σ₁₁'
      let σ₁₂' = (mapp (\r → substAlphaRNF (list ρ) r) σ₁₂)
      let σ₁₂'' = assoc $ map (\(TMVar x :* s) → TMVar (freshenVar β x) :* s) $ list σ₁₂'
      let σa = σ₁₁'' ⊓ σ₂₁
      let σb = σ₁₂'' ⊓ σ₂₂
      return $ (τa :* σa) :⊞: (σb :* τb)
    ((τ₁₁ :* σ₁₁) :⊠: (σ₁₂ :* τ₁₂),(τ₂₁ :* σ₂₁) :⊠: (σ₂₂ :* τ₂₂)) → do
      τa ← tyMeet ρ β τ₁₁ τ₂₁
      τb ← tyMeet ρ β τ₁₂ τ₂₂
      let σ₁₁' = (mapp (\r → substAlphaRNF (list ρ) r) σ₁₁)
      let σ₁₁'' = assoc $ map (\(TMVar x :* s) → TMVar (freshenVar β x) :* s) $ list σ₁₁'
      let σ₁₂' = (mapp (\r → substAlphaRNF (list ρ) r) σ₁₂)
      let σ₁₂'' = assoc $ map (\(TMVar x :* s) → TMVar (freshenVar β x) :* s) $ list σ₁₂'
      let σa = σ₁₁'' ⊓ σ₂₁
      let σb = σ₁₂'' ⊓ σ₂₂
      return $ (τa :* σa) :⊠: (σb :* τb)
    ((x₁ :* τ₁₁) :⊸: (sσ₁ :* τ₁₂),(x₂ :* τ₂₁) :⊸: (sσ₂ :* τ₂₂)) → do
      τa ← tyJoin ρ ((x₁ ↦ x₂) ⩌ β) τ₁₁ τ₂₁
      τb ← tyMeet ρ ((x₁ ↦ x₂) ⩌ β) τ₁₂ τ₂₂
      let sσ₁' = (mapp (\r → substAlphaRNF (list ρ) r) sσ₁)
      let sσ₁'' ∷ (ProgramVar ⇰ _) = assoc $ map (\(x :* s) → freshenRef ρ ((x₁↦ x₂) ⩌ β) x :* s) $ list sσ₁'
      let σa = sσ₁'' ⊓ sσ₂
      return $ (x₁ :* τ₁₁) :⊸: (sσ₁ :* τ₁₂)
    ((x₁ :* τ₁₁ :* s₁) :⊸⋆: (PEnv (pσ₁ ∷ ProgramVar ⇰ Pr p RNF) :* τ₁₂),(x₂ :* τ₂₁ :* s₂) :⊸⋆: (PEnv (pσ₂ ∷ ProgramVar ⇰ Pr p' RNF) :* τ₂₂)) →
      case eqPRIV (priv @ p) (priv @ p') of
        None → None
        Some Refl → do
          τa ← tyJoin ρ ((x₁ ↦ x₂) ⩌ β) τ₁₁ τ₂₁
          τb ← tyMeet ρ ((x₁ ↦ x₂) ⩌ β) τ₁₂ τ₂₂
          let pσ₁' = (mapp (\r → substAlphaRNF (list ρ) r) pσ₁)
          let pσ₁'' ∷ (ProgramVar ⇰ _) = assoc $ map (\(x :* p) → freshenRef ρ ((x₁↦ x₂) ⩌ β) x :* p) $ list pσ₁'
          let s₁' = map (substAlphaRNF (list ρ)) s₁
          let σa = pσ₁'' ⊓ pσ₂
          return $ (x₁ :* τa :* s₁') :⊸⋆: (PEnv (σa ∷ ProgramVar ⇰ Pr p RNF) :* τb)
    (ForallT x₁ κ₁ τ₁,ForallT x₂ κ₂ τ₂) | (κ₁ ≡ κ₂) → do
      τa ← tyMeet ((x₁↦x₂) ⩌ ρ) β τ₁ τ₂
      return $ ForallT x₂ κ₂ τa
    (CxtT xs₁,CxtT xs₂) | xs₁ ≡ xs₂ → return $ CxtT xs₂
    (UnitT, UnitT) → return $ UnitT
    (BoxedT sσ₁ τ₁,BoxedT sσ₂ τ₂) → undefined
    _ → None

-----------------
-- Expressions --
-----------------

data Grad = LR
  deriving (Eq,Ord,Show)
makePrettySum ''Grad

type SExpSource (p ∷ PRIV) r = Annotated FullContext (SExp p r)
-- this is using GADT syntax and extension
data SExp (p ∷ PRIV) r where
  ℕˢSE ∷ ℕ → SExp p r
  ℝˢSE ∷ 𝔻 → SExp p r
  ℕSE ∷ ℕ → SExp p r
  ℝSE ∷ 𝔻 → SExp p r
  𝕌SE ∷ SExp p r
  TrueSE ∷ SExp p r
  FalseSE ∷ SExp p r
  VarSE ∷ 𝕏 → SExp p r
  LetSE ∷ 𝕏  → SExpSource p r → SExpSource p r → SExp p r
  SFunSE ∷ 𝑂 (𝐿 ProgramVar) → 𝕏  → TypeSource r → SExpSource p r → SExp p r
  AppSE ∷ SExpSource p r → 𝑂 (𝐿 ProgramVar) → SExpSource p r → SExp p r
  PFunSE ∷ 𝑂 (𝐿 ProgramVar) → 𝕏 → TypeSource r → Sens r → PExpSource p r → SExp p r
  TAbsSE ∷ 𝕏 → Kind → SExpSource p r → SExp p r
  TAppSE ∷ SExpSource p r → TLExp r → SExp p r
  IfSE ∷ (SExpSource p r) → (SExpSource p r) → (SExpSource p r) → SExp p r
  CaseSE ∷ SExpSource p r → 𝕏 → SExpSource p r → 𝕏 → SExpSource p r → SExp p r
  InlSE ∷  TypeSource r → SExpSource p r → SExp p r
  InrSE ∷  TypeSource r → SExpSource p r → SExp p r
  PairSE ∷ SExpSource p r → 𝑂 (𝐿 ProgramVar) → 𝑂 (𝐿 ProgramVar) → SExpSource p r → SExp p r
  FstSE ∷ SExpSource p r → SExp p r
  SndSE ∷ SExpSource p r → SExp p r
  TupSE ∷ SExpSource p r → 𝑂 (𝐿 ProgramVar) → 𝑂 (𝐿 ProgramVar) → SExpSource p r → SExp p r
  UntupSE ∷ 𝕏 → 𝕏 → SExpSource p r → SExpSource p r → SExp p r
  deriving (Eq,Ord,Show)

instance Functor (SExp p) where
  map f (ℕˢSE n) = (ℕˢSE n)
  map f (ℝˢSE d) = (ℝˢSE d)
  map f (ℕSE n) = (ℕSE n)
  map f (ℝSE d) = (ℝSE d)
  map f 𝕌SE = 𝕌SE
  map f (TrueSE) = (TrueSE)
  map f (FalseSE) = (FalseSE)
  map f (VarSE x) = (VarSE x)
  map f (LetSE x e₁ e₂) = (LetSE x (mapp f e₁) (mapp f e₂))
  map f (SFunSE xsO x τ e) = (SFunSE xsO x (mapp f τ) (mapp f e))
  map f (AppSE e₁ xs e₂) = (AppSE (mapp f e₁) xs (mapp f e₂))
  map f (PFunSE xsO x τ s e) = (PFunSE xsO x (mapp f τ) (map f s) (mapp f e))
  map f (TAbsSE x κ e) = (TAbsSE x κ (mapp f e))
  map f (TAppSE e τ) = (TAppSE (mapp f e) (mapp f τ))
  map f (IfSE e₁ e₂ e₃) = (IfSE (mapp f e₁) (mapp f e₂) (mapp f e₃))
  map f (PairSE e₁ xsO₁ xsO₂ e₂) = (PairSE (mapp f e₁) xsO₁ xsO₂ (mapp f e₂))
  map f (FstSE e) = (FstSE (mapp f e))
  map f (SndSE e) = (SndSE (mapp f e))
  map f (TupSE e₁ xsO₁ xsO₂ e₂) = (TupSE (mapp f e₁) xsO₁ xsO₂ (mapp f e₂))
  map f (UntupSE x₁ x₂ e₁ e₂) = (UntupSE x₁ x₂ (mapp f e₁) (mapp f e₂))
  map f (InlSE τ₂ e) = (InlSE (mapp f τ₂) (mapp f e))
  map f (InrSE τ₁ e) = (InrSE (mapp f τ₁) (mapp f e))
  map f (CaseSE e₁ x e₂ y e₃) = (CaseSE (mapp f e₁) x (mapp f e₂) y (mapp f e₃))

type PExpSource (p ∷ PRIV) r = Annotated FullContext (PExp p r)
data PExp (p ∷ PRIV) r where
  ReturnPE ∷ SExpSource p r → PExp p r
  BindPE ∷ 𝕏 → PExpSource p r → PExpSource p r → PExp p r
  LetPE ∷ 𝕏  → SExpSource p r → PExpSource p r → PExp p r
  IfPE ∷ (SExpSource p r) → (PExpSource p r) → (PExpSource p r) → PExp p r
  CasePE ∷ SExpSource p r → 𝕏 → PExpSource p r → 𝕏 → PExpSource p r → PExp p r
  AppPE ∷ SExpSource p r → 𝑂 (𝐿 ProgramVar) → SExpSource p r → PExp p r
  ConvertZCEDPE ∷ SExpSource 'ED r → PExpSource 'ZC r → PExp 'ED r
  ConvertEPSZCPE ∷ PExpSource 'EPS r → PExp 'ZC r
  ConvertRENYIEDPE ∷ SExpSource 'ED r → PExpSource 'RENYI r → PExp 'ED r

instance Functor (PExp p) where
  map f (ReturnPE e) = (ReturnPE (mapp f e))
  map f (BindPE x e₁ e₂) = (BindPE x (mapp f e₁) (mapp f e₂))
  map f (LetPE x e₁ e₂) = (LetPE x (mapp f e₁) (mapp f e₂))
  map f (IfPE e₁ e₂ e₃) = (IfPE (mapp f e₁) (mapp f e₂) (mapp f e₃))
  map f (CasePE e₁ x e₂ y e₃) = (CasePE (mapp f e₁) x (mapp f e₂) y (mapp f e₃))
  map f (AppPE e₁ xs e₂) = (AppPE (mapp f e₁) xs (mapp f e₂))
  map f (ConvertZCEDPE e₁ e₂ ) = (ConvertZCEDPE (mapp f e₁) (mapp f e₂))
  map f (ConvertEPSZCPE e₁) = (ConvertEPSZCPE (mapp f e₁))
  map f (ConvertRENYIEDPE e₁ e₂) = (ConvertRENYIEDPE (mapp f e₁) (mapp f e₂))

deriving instance (Eq r) ⇒ Eq (PExp p r)
deriving instance (Ord r) ⇒ Ord (PExp p r)
deriving instance (Show r) ⇒ Show (PExp p r)

data GaussParams (p ∷ PRIV) r where
  EDGaussParams ∷ SExpSource 'ED r → SExpSource 'ED r → GaussParams 'ED r
  RenyiGaussParams ∷ SExpSource 'RENYI r → SExpSource 'RENYI r → GaussParams 'RENYI r
  TCGaussParams ∷ SExpSource 'TC r → SExpSource 'TC r → GaussParams 'TC r
  ZCGaussParams ∷ SExpSource 'ZC r → GaussParams 'ZC r
deriving instance (Eq r) ⇒  Eq (GaussParams p r)
deriving instance (Ord r) ⇒ Ord (GaussParams p r)
deriving instance (Show r) ⇒ Show (GaussParams p r)

data LaplaceParams (p ∷ PRIV) r where
  EpsLaplaceParams ∷ SExpSource 'EPS r → LaplaceParams 'EPS r
deriving instance (Eq r) ⇒   Eq (LaplaceParams p r)
deriving instance (Ord r) ⇒  Ord (LaplaceParams p r)
deriving instance (Show r) ⇒ Show (LaplaceParams p r)

data ExponentialParams (p ∷ PRIV) r where
  EDExponentialParams ∷ SExpSource 'ED r → ExponentialParams 'ED r
deriving instance (Eq r) ⇒   Eq (ExponentialParams p r)
deriving instance (Ord r) ⇒  Ord (ExponentialParams p r)
deriving instance (Show r) ⇒ Show (ExponentialParams p r)

data SVTParams (p ∷ PRIV) r where
  EPSSVTParams ∷ SExpSource 'EPS r → SVTParams 'EPS r
  EDSVTParams ∷ SExpSource 'ED r → SVTParams 'ED r
deriving instance (Eq r) ⇒   Eq (SVTParams p r)
deriving instance (Ord r) ⇒  Ord (SVTParams p r)
deriving instance (Show r) ⇒ Show (SVTParams p r)

instance Pretty (SExp p r) where pretty _ = ppLit "SEXP"
instance Pretty (PExp p r) where pretty _ = ppLit "PEXP"
