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
convertRENYIEDPr ∷ (One r,Plus r,Minus r,Divide r,Log r) ⇒ r → Pr 'RENYI r → Pr 'ED r
convertRENYIEDPr δ (RenyiPriv α ε) = EDPriv (ε + log (one / δ) / (α - one)) δ

-- JOE TODO: put a link here to the paper
convertZCEDPr ∷ (One r,Plus r,Minus r,Times r,Divide r,Root r,Log r) ⇒ r → Pr 'ZC r → Pr 'ED r
convertZCEDPr δ (ZCPriv ρ) = EDPriv (ρ + (one + one) × root (ρ × log (one / δ))) δ

-- JOE TODO: put a link here to the paper
convertEPSZCPr ∷ (One r,Plus r,Minus r,Times r,Divide r,Root r,Log r) ⇒ Pr 'EPS r → Pr 'ZC r
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
  | Type r :&: Type r
  | (𝕏 ∧ Type r) :⊸: ((ProgramVar ⇰ Sens r) ∧ Type r)
  | (𝕏 ∧ Type r) :⊸⋆: (PEnv r ∧ Type r)
  | ForallT 𝕏 Kind (Type r)
  | CxtT (𝑃 ProgramVar)
  | BoxedT (𝕏 ⇰ Sens r) (Type r)
  -- eventually we want:
  -- - contextual/lazy function, pair, and sum connectives
  deriving (Eq,Ord,Show)

class Substitution r where subst ∷ 𝕏 → r → r → r

instance Substitution RNF where subst = substRNF
instance Substitution RExp where subst = substRExp

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
    τ₁ :&: τ₂ →
      let (τ₁' :* n') = freshenType ρ β τ₁ n in
      let (τ₂' :* n'') = freshenType ρ β τ₂ n' in
      (τ₁' :&: τ₂') :* n''
    (x₁ :* τ₁) :⊸: (sσ₁ :* τ₂) →
      let x₁ⁿ = 𝕏 {𝕩name=(𝕩name x₁), 𝕩Gen=Some n} in
      let (τ₁' :* n') = freshenType ρ ((x₁↦ x₁ⁿ) ⩌ β) τ₁ nplusone in
      let (τ₂' :* n'') = freshenType ρ ((x₁↦ x₁ⁿ) ⩌ β) τ₂ n' in
      let sσ₁' = (mapp (\r → substAlphaRNF (list ρ) r) sσ₁) in
      let sσ₁'' ∷ (ProgramVar ⇰ _) = assoc $ map (\(x :* s) → freshenRef ρ ((x₁↦ x₁ⁿ) ⩌ β) x :* s) $ list sσ₁' in
      ((x₁ⁿ :* τ₁') :⊸: (sσ₁'' :* τ₂') :* n'')
    (x₁ :* τ₁) :⊸⋆: (PEnv (pσ₁ ∷ ProgramVar ⇰ Pr p RNF) :* τ₂) →
      let x₁ⁿ = 𝕏 {𝕩name=(𝕩name x₁), 𝕩Gen=Some n} in
      let (τ₁' :* n') = freshenType ρ ((x₁↦ x₁ⁿ) ⩌ β) τ₁ nplusone in
      let (τ₂' :* n'') = freshenType ρ ((x₁↦ x₁ⁿ) ⩌ β) τ₂ n' in
      let pσ₁' = (mapp (\r → substAlphaRNF (list ρ) r) pσ₁) in
      let pσ₁'' = assoc $ map (\(x :* p) → freshenRef ρ ((x₁↦ x₁ⁿ) ⩌ β) x :* p) $ list pσ₁' in
      ((x₁ⁿ :* τ₁') :⊸⋆: (PEnv pσ₁'' :* τ₂') :* n'')
    ForallT x κ τ →
      let xⁿ = 𝕏 {𝕩name=(𝕩name x), 𝕩Gen=Some n} in
      let (τ' :* n') = freshenType ((x↦ xⁿ) ⩌ ρ) β τ nplusone in
      (ForallT xⁿ κ τ' ) :* n'
    CxtT xs → do
      let xs' = pow $ map (\x → freshenRef ρ β x) $ list xs
      (CxtT xs' :* n)
    BoxedT sσ₁ τ₁ → undefined

substAlphaRExp ∷ 𝐿 (𝕏 ∧ 𝕏) → RExp → RExp
substAlphaRExp Nil r = r
substAlphaRExp ((x₁:*x₂):&ρ) r = substAlphaRExp ρ $ substRExp x₁ (varRE x₂) r

substAlphaRNF ∷ 𝐿 (𝕏 ∧ 𝕏) → RNF → RNF
substAlphaRNF Nil r = r
substAlphaRNF ((x₁:*x₂):&ρ) r = substAlphaRNF ρ $ substRNF x₁ (varRNF x₂) r

freshenTMV ∷ (𝕏 ⇰ 𝕏) → 𝕏 → 𝕏
freshenTMV β x = case β ⋕? x of
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
  VarME x → (VarME x) :* n
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
    (τ₁₁ :&: τ₁₂,τ₂₁ :&: τ₂₂) → (alphaEquiv ρ β τ₁₁ τ₂₁) ⩓ (alphaEquiv ρ β τ₁₂ τ₂₂)
    ((x₁ :* τ₁₁) :⊸: (sσ₁ :* τ₁₂),(x₂ :* τ₂₁) :⊸: (sσ₂ :* τ₂₂)) → do
      let sσ₁' = (mapp (\r → substAlphaRNF (list ρ) r) sσ₁)
      let sσ₁'' ∷ (ProgramVar ⇰ _) = assoc $ map (\(x :* s) → freshenRef ρ ((x₁↦ x₂) ⩌ β) x :* s) $ list sσ₁'
      let c₁ = (alphaEquiv ρ ((x₁ ↦ x₂) ⩌ β) τ₁₁ τ₂₁)
      let c₂ = (alphaEquiv ρ ((x₁ ↦ x₂) ⩌ β) τ₁₂ τ₂₂)
      let c₃ = (sσ₁'' ≡ sσ₂)
      c₁ ⩓ c₂ ⩓ c₃
    ((x₁ :* τ₁₁) :⊸⋆: (PEnv (pσ₁ ∷ ProgramVar ⇰ Pr p RNF) :* τ₁₂),(x₂ :* τ₂₁) :⊸⋆: (PEnv (pσ₂ ∷ ProgramVar ⇰ Pr p' RNF) :* τ₂₂)) →
      case eqPRIV (priv @ p) (priv @ p') of
        None → False
        Some Refl →
          let pσ₁' = (mapp (\r → substAlphaRNF (list ρ) r) pσ₁) in
          let pσ₁'' ∷ (ProgramVar ⇰ _) = assoc $ map (\(x :* p) → freshenRef ρ ((x₁↦ x₂) ⩌ β) x :* p) $ list pσ₁' in
          let c₁ = (alphaEquiv ρ ((x₁ ↦ x₂) ⩌ β) τ₁₁ τ₂₁) in
          let c₂ = (alphaEquiv ρ ((x₁ ↦ x₂) ⩌ β) τ₁₂ τ₂₂) in
          let c₃ = (pσ₁'' ≡ pσ₂) in
          c₁ ⩓ c₂ ⩓ c₃
    (ForallT x₁ κ₁ τ₁,ForallT x₂ κ₂ τ₂) → case (κ₁ ≡ κ₂) of
      True → alphaEquiv ((x₁↦x₂) ⩌ ρ) β τ₁ τ₂
      False → False
    (CxtT xs₁,CxtT xs₂) → xs₁ ≡ xs₂
    (BoxedT sσ₁ τ₁,BoxedT sσ₂ τ₂) → undefined
    _ → False

alphaEquivMExp ∷ (𝕏 ⇰ 𝕏) → (𝕏 ⇰ 𝕏) → MExp RNF → MExp RNF → 𝔹
alphaEquivMExp ρ β me₁' me₂' = case (me₁',me₂') of
  (EmptyME,EmptyME) → True
  (VarME x₁,VarME x₂) → x₁ ≡ x₂
  (ConsME τ₁ me₁,ConsME τ₂ me₂) → (alphaEquiv ρ β τ₁ τ₂) ⩓ (alphaEquivMExp ρ β me₁ me₂)
  (AppendME me₁₁ me₁₂,AppendME me₂₁ me₂₂) → (alphaEquivMExp ρ β me₁₁ me₂₁) ⩓ (alphaEquivMExp ρ β me₁₂ me₂₂)
  (RexpME r₁ τ₁,RexpME r₂ τ₂) → ((substAlphaRNF (list ρ) r₁) ≡ r₂) ⩓ (alphaEquiv ρ β τ₁ τ₂)

alphaEquivRows ∷ (𝕏 ⇰ 𝕏) → RowsT RNF → RowsT RNF → 𝔹
alphaEquivRows ρ rows₁ rows₂ = case (rows₁,rows₂) of
  (StarRT, StarRT) → True
  (RexpRT r₁, RexpRT r₂) → (substAlphaRNF (list ρ) r₁) ≡ r₂
  _ → False

data TLExp r =
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
  | TLExp r :&♭: TLExp r
  | (𝕏 ∧ TLExp r) :⊸♭: ((ProgramVar ⇰ Sens r) ∧ TLExp r)
  | (𝕏 ∧ TLExp r) :⊸⋆♭: (PEnv r ∧ TLExp r)
  | ForallTE 𝕏 Kind (TLExp r)
  | CxtTE (𝑃 𝕏)
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
  -- Privacy Stuff
  | PairTE (TLExp r) (TLExp r)
  deriving (Eq,Ord,Show)

type STLExp r = Annotated FullContext (STLExpPre r)
data STLExpPre r =
    VarSTE 𝕏
  -- Type Stuff
  | ℕˢSTE r
  | ℝˢSTE r
  | ℕSTE
  | ℝSTE
  | 𝕀STE r
  | 𝔹STE
  | 𝕊STE
  | SetSTE (STLExp r)
  | 𝕄STE Norm Clip (RowsT r) (MExp r)
  | 𝔻STE (STLExp r)
  | STLExp r :⊕♭♭: STLExp r
  | STLExp r :⊗♭♭: STLExp r
  | STLExp r :&♭♭: STLExp r
  | STLExp r :⊸♭♭: (Sens r ∧ STLExp r)
  | (𝕏 ∧ STLExp r) :⊸⋆♭♭: (PEnv r ∧ STLExp r)
  | ForallSTE 𝕏 Kind (STLExp r)
  | CxtSTE (𝑃 𝕏)
  -- | (𝐿 (𝕏 ∧ Kind) ∧ STLExp r) :⊸♭: (Sens r ∧ STLExp r)
  -- -- ∀α:κ,…,α:κ. (x:τ,…,x:τ) → {x⋅p,…,x⋅p} τ
  -- | (𝐿 (𝕏 ∧ Kind) ∧ 𝐿 (𝕏 ∧ STLExp r)) :⊸⋆♭: (PEnv r ∧ STLExp r)
  | BoxedSTE (𝕏 ⇰ Sens r) (STLExp r)
  -- RExp Stuff
  | NatSTE ℕ
  | NNRealSTE 𝔻
  | MaxSTE (STLExp r) (STLExp r)
  | MinSTE (STLExp r) (STLExp r)
  | PlusSTE (STLExp r) (STLExp r)
  | TimesSTE (STLExp r) (STLExp r)
  | DivSTE (STLExp r) (STLExp r)
  | RootSTE (STLExp r)
  | LogSTE (STLExp r)
  | TopSTE
  -- Privacy Stuff
  | PairSTE (STLExp r) (STLExp r)
  deriving (Eq,Ord)

frSTLExp ∷ STLExp r → TLExp r
frSTLExp = undefined

deriving instance (Show r) ⇒ Show (STLExpPre r)

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
    τ₁ :&: τ₂ → map f τ₁ :&: map f τ₂
    (x :* τ₁) :⊸: (s :* τ₂) → (x :* map f τ₁) :⊸: (mapp f s :*  map f τ₂)
    (x :* τ₁) :⊸⋆: (PEnv pσ :* τ₂) → (x :* map f τ₁) :⊸⋆: (PEnv (map (map f) pσ) :* map f τ₂)
    ForallT α κ τ → ForallT α κ $ map f τ
    CxtT xs → CxtT xs
    BoxedT σ τ → BoxedT (map (map f) σ) (map f τ)
    VarT x → VarT x

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
  TrueSE ∷ SExp p r
  FalseSE ∷ SExp p r
  VarSE ∷ 𝕏 → SExp p r
  LetSE ∷ 𝕏  → SExpSource p r → SExpSource p r → SExp p r
  SFunSE ∷ 𝕏  → TypeSource r → SExpSource p r → SExp p r
  AppSE ∷ SExpSource p r → 𝑂 (𝐿 ProgramVar) → SExpSource p r → SExp p r
  PFunSE ∷ 𝕏 → TypeSource r → PExpSource p r → SExp p r
  TAbsSE ∷ 𝕏 → Kind → SExpSource p r → SExp p r
  TAppSE ∷ SExpSource p r → TypeSource r → SExp p r
  deriving (Eq,Ord,Show)

instance Functor (SExp p) where
  map f (ℕˢSE n) = (ℕˢSE n)
  map f (ℝˢSE d) = (ℝˢSE d)
  map f (ℕSE n) = (ℕSE n)
  map f (ℝSE d) = (ℝSE d)
  map f (TrueSE) = (TrueSE)
  map f (FalseSE) = (FalseSE)
  map f (VarSE x) = (VarSE x)
  map f (LetSE x e₁ e₂) = (LetSE x (mapp f e₁) (mapp f e₂))
  map f (SFunSE x τ e) = (SFunSE x (mapp f τ) (mapp f e))
  map f (AppSE e₁ xs e₂) = (AppSE (mapp f e₁) xs (mapp f e₂))
  map f (PFunSE x τ e) = (PFunSE x (mapp f τ) (mapp f e))
  map f (TAbsSE x κ e) = (TAbsSE x κ (mapp f e))
  map f (TAppSE e τ) = (TAppSE (mapp f e) (mapp f τ))

type PExpSource (p ∷ PRIV) r = Annotated FullContext (PExp p r)
data PExp (p ∷ PRIV) r where
  ReturnPE ∷ SExpSource p r → PExp p r
  BindPE ∷ 𝕏 → PExpSource p r → PExpSource p r → PExp p r
  AppPE ∷ SExpSource p r → 𝑂 (𝐿 ProgramVar) → SExpSource p r → PExp p r

instance Functor (PExp p) where
  map f (ReturnPE e) = (ReturnPE (mapp f e))
  map f (BindPE x e₁ e₂) = (BindPE x (mapp f e₁) (mapp f e₂))
  map f (AppPE e₁ xs e₂) = (AppPE (mapp f e₁) xs (mapp f e₂))

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
