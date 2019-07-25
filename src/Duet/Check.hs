{-# LANGUAGE PartialTypeSignatures #-}

module Duet.Check where

import Duet.UVMHS

import Duet.Pretty ()
import Duet.Syntax
import Duet.RNF2

data TypeError = TypeError
  { typeErrorTerm ∷ Doc
  , typeErrorContext ∷ (𝕏 ⇰ Type RNF)
  , typeErrorType ∷ Type RNF
  , typeErrorExpected ∷ 𝐿 𝕊
  }
makePrettyRecord ''TypeError

data Context = Context
  { contextKind ∷ 𝕏 ⇰ Kind
  , contextType ∷ 𝕏 ⇰ Type RNF
  , contextMExp ∷ 𝕏 ⇰ MExp RNF
  }
makeLenses ''Context
makePrettyRecord ''Context

newtype SM (p ∷ PRIV) a = SM { unSM ∷ RWST Context (ProgramVar ⇰ Sens RNF) ℕ (ErrorT TypeError ID) a }
  deriving
  (Functor
  ,Return,Bind,Monad
  ,MonadError TypeError
  ,MonadReader Context
  ,MonadWriter (ProgramVar ⇰ Sens RNF)
  ,MonadState ℕ)

mkSM ∷ (𝕏 ⇰ Kind → 𝕏 ⇰ Type RNF → 𝕏 ⇰ MExp RNF → ℕ → TypeError ∨ (ℕ ∧ (ProgramVar ⇰ Sens RNF) ∧ a)) → SM p a
mkSM f = SM $ mkRWST $ \ (Context δ γ ᴍ) n → ErrorT $ ID $ f δ γ ᴍ n

runSM ∷ 𝕏 ⇰ Kind → 𝕏 ⇰ Type RNF → 𝕏 ⇰ MExp RNF → ℕ → SM p a → TypeError ∨ (ℕ ∧ (ProgramVar ⇰ Sens RNF) ∧ a)
runSM δ γ ᴍ n = unID ∘ unErrorT ∘ runRWST (Context δ γ ᴍ) n ∘ unSM

newtype PM (p ∷ PRIV) a = PM { unPM ∷ RWST Context (ProgramVar ⇰ Pr p RNF) ℕ (ErrorT TypeError ID) a }
  deriving
  (Functor
  ,Return,Bind,Monad
  ,MonadError TypeError
  ,MonadReader Context
  ,MonadWriter (ProgramVar ⇰ Pr p RNF)
  ,MonadState ℕ)

mkPM ∷ (𝕏 ⇰ Kind → 𝕏 ⇰ Type RNF → 𝕏 ⇰ MExp RNF → ℕ → TypeError ∨ (ℕ ∧ (ProgramVar ⇰ Pr p RNF) ∧ a)) → PM p a
mkPM f = PM $ mkRWST $ \ (Context δ γ ᴍ) n → ErrorT $ ID $ f δ γ ᴍ n

runPM ∷ 𝕏 ⇰ Kind → 𝕏 ⇰ Type RNF → 𝕏 ⇰ MExp RNF → ℕ → PM p a → TypeError ∨ (ℕ ∧ (ProgramVar ⇰ Pr p RNF) ∧ a)
runPM δ γ ᴍ n = unID ∘ unErrorT ∘ runRWST (Context δ γ ᴍ) n ∘ unPM

smFromPM ∷ PM p a → SM p a
smFromPM xM = mkSM $ \ δ γ ᴍ n →
  mapInr (mapFst $ mapSnd $ map $ Sens ∘ (×) top ∘ truncateRNF ∘ indicatorPr) $ runPM δ γ ᴍ n xM

pmFromSM ∷ (PRIV_C p) ⇒ SM p a → PM p a
pmFromSM xM = mkPM $ \ δ γ ᴍ n →
  mapInr (mapFst $ mapSnd $ map $ makePr ∘ (×) top ∘ truncateRNF ∘ unSens) $ runSM δ γ ᴍ n xM


pmFromSM' ∷ (PRIV_C p) ⇒ SM p a → PM p a
pmFromSM' xM = mkPM $ \ δ γ ᴍ n →
  mapInr (mapFst $ mapSnd $ map $ makePr ∘ (×) top ∘ unSens) $ runSM δ γ ᴍ n xM

mapPPM ∷ (Pr p₁ RNF → Pr p₂ RNF) → PM p₁ a → PM p₂ a
mapPPM f xM = mkPM $ \ δ γ ᴍ n → mapInr (mapFst $ mapSnd $ map f) $ runPM δ γ ᴍ n xM

checkSensLang ∷ TLExp RNF → 𝑂 (Sens RNF)
checkSensLang e = do
  η ← checkRExpLang e
  return $ Sens η

checkPrivLang ∷ (PRIV_C p) ⇒ PRIV_W p → TLExp RNF → 𝑂 (Pr p RNF)
checkPrivLang p e₀ = case p of
  EPS_W → do
    η ← checkRExpLang e₀
    return $ EpsPriv η
  ED_W → do
    case e₀ of
      PairTE e₁ e₂ → do
        η₁ ← checkRExpLang e₁
        η₂ ← checkRExpLang e₂
        return $ EDPriv η₁ η₂
      _ → error "non pair TLExp while coercing in ED_W mode"
  _ → undefined

privToTLExp ∷ Pr p RNF → TLExp RNF
privToTLExp = \case
  EpsPriv r → rnfToTLExp r
  EDPriv r₁ r₂ → PairTE (rnfToTLExp r₁) (rnfToTLExp r₂)
  RenyiPriv r₁ r₂ → PairTE (rnfToTLExp r₁) (rnfToTLExp r₂)
  ZCPriv r → rnfToTLExp r
  TCPriv r₁ r₂ → PairTE (rnfToTLExp r₁) (rnfToTLExp r₂)

sensToTLExp ∷ Sens RNF → TLExp RNF
sensToTLExp s = rnfToTLExp $ unSens s

rnfToTLExp ∷ RNF → TLExp RNF
rnfToTLExp = \case
  ConstantRNF r → case r of
    TopBT → TopTE
    BotBT → ℝˢTE $ dblRNF 0.0
    AddBT a → ℝˢTE $ dblRNF a

typeToTLExp ∷ Type RNF → TLExp RNF
typeToTLExp = \case
  VarT x → VarTE x
  ℕˢT r → ℕˢTE r
  ℝˢT r → ℝˢTE r
  ℕT → ℕTE
  ℝT → ℝTE
  𝕀T r → 𝕀TE r
  𝔹T → 𝔹TE
  𝕊T → 𝕊TE
  SetT τ → SetTE $ typeToTLExp τ
  𝕄T ℓ c rows cols → 𝕄TE ℓ c rows cols
  𝔻T τ → 𝔻TE $ typeToTLExp τ
  τ₁ :⊕: τ₂ → typeToTLExp τ₁ :⊕♭: typeToTLExp τ₂
  τ₁ :⊗: τ₂ → typeToTLExp τ₁ :⊗♭: typeToTLExp τ₂
  τ₁ :&: τ₂ → typeToTLExp τ₁ :&♭: typeToTLExp τ₂
  (x :* τ₁) :⊸: (sσ :* τ₂) → (x :* typeToTLExp τ₁) :⊸♭: (sσ :* typeToTLExp τ₂)
  (x :* τ₁) :⊸⋆: (pσ :* τ₂) → (x :* typeToTLExp τ₁) :⊸⋆♭: (pσ :* typeToTLExp τ₂)
  ForallT x κ τ → ForallTE x κ $ typeToTLExp τ

checkTypeLang ∷ TLExp RNF → 𝑂 (Type RNF)
checkTypeLang e₀ = case e₀ of
  VarTE x → return $ VarT x
  ℕˢTE r → return $ ℕˢT r
  ℝˢTE r → return $ ℝˢT r
  ℕTE → return ℕT
  ℝTE → return ℝT
  𝕀TE r → return $ 𝕀T r
  𝔹TE → return 𝔹T
  𝕊TE → return 𝕊T
  SetTE e → do
    τ ← checkTypeLang e
    return $ SetT τ
  𝕄TE ℓ c rows mexpr → return $ 𝕄T ℓ c rows mexpr
  𝔻TE e → do
    τ ← checkTypeLang e
    return $ 𝔻T τ
  e₁ :⊕♭: e₂ → do
    τ₁ ← checkTypeLang e₁
    τ₂ ← checkTypeLang e₂
    return $ τ₁ :⊕: τ₂
  e₁ :⊗♭: e₂ → do
    τ₁ ← checkTypeLang e₁
    τ₂ ← checkTypeLang e₂
    return $ τ₁ :⊗: τ₂
  e₁ :&♭: e₂ → do
    τ₁ ← checkTypeLang e₁
    τ₂ ← checkTypeLang e₂
    return $ τ₁ :&: τ₂
  (x :* e₁) :⊸♭: (sσ :* e₂) → do
    τ₁ ← checkTypeLang e₁
    τ₂ ← checkTypeLang e₂
    return $ (x :* τ₁) :⊸: (sσ :* τ₂)
  (x :* e₁) :⊸⋆♭: (pσ :* e₂) → do
    τ₁ ← checkTypeLang e₁
    τ₂ ← checkTypeLang e₂
    return $ (x :* τ₁) :⊸⋆: (pσ :* τ₂)
  _ → None

checkRExpLang ∷ TLExp RNF → 𝑂 RNF
checkRExpLang e₀ = case e₀ of
  VarTE x → return $ varRNF x
  NatTE n → return $ ConstantRNF $ AddBT $ dbl n
  NNRealTE r → return $ ConstantRNF $ AddBT r
  MaxTE e₁ e₂ → do
    η₁ ← checkRExpLang e₁
    η₂ ← checkRExpLang e₂
    return $ maxRNF η₁ η₂
  MinTE e₁ e₂ → do
    η₁ ← checkRExpLang e₁
    η₂ ← checkRExpLang e₂
    return $ minRNF η₁ η₂
  PlusTE e₁ e₂ → do
    η₁ ← checkRExpLang e₁
    η₂ ← checkRExpLang e₂
    return $ sumRNF η₁ η₂
  TimesTE e₁ e₂ → do
    η₁ ← checkRExpLang e₁
    η₂ ← checkRExpLang e₂
    return $ prodRNF η₁ η₂
  DivTE e₁ e₂ → do
    η₁ ← checkRExpLang e₁
    η₂ ← checkRExpLang e₂
    return $ η₁ / η₂
  RootTE e → do
    η ← checkRExpLang e
    return $ powerRNF (rat 1 / rat 2) η
  LogTE e → do
    η ← checkRExpLang e
    return $ logRNF η
  _ → None

checkSchemaVar ∷ 𝕏 → SM p ()
checkSchemaVar x = do
  ᴍ ← askL contextMExpL
  case ᴍ ⋕? x of
    Some _m → skip
    None → error $ concat
      [ "Schema variable lookup error: failed to find " ⧺ (pprender x) ⧺ " in the environment:\n"
      , pprender ᴍ
      ]

inferKindVar ∷ 𝕏 → SM p Kind
inferKindVar x = do
  δ ← askL contextKindL
  case δ ⋕? x of
    Some κ → return κ
    None → error $ concat
      [ "Kind variable lookup error: failed to find " ⧺ (pprender x) ⧺ " in the environment:\n"
      , pprender δ
      ]

checkProgramVar ∷ 𝕏 → SM p ()
checkProgramVar x = do
  σ ← askL contextTypeL
  case σ ⋕? x of
    Some _τ → return ()
    None → do
      δ ← askL contextKindL
      case δ ⋕? x of
        Some κ → case κ of
          CxtK → return ()
          _ → error $ concat
            [ "checkProgramVar: failed on " ⧺ (pprender x) ⧺ " in the environments:\n"
            , pprender σ
            , pprender δ
            ]
        None → error $ concat
          [ "checkProgramVar: failed on " ⧺ (pprender x) ⧺ " in the environments:\n"
          , pprender σ
          , pprender δ
          ]

checkSens ∷ Sens RExpPre → SM p ()
checkSens (Sens r) = checkKind ℝK r

checkPriv ∷ Pr p' RExpPre → SM p ()
checkPriv = \case
  EpsPriv r → checkKind ℝK r
  EDPriv r₁ r₂ → do
    checkKind ℝK r₁
    checkKind ℝK r₂
  RenyiPriv r₁ r₂ → do
    checkKind ℝK r₁
    checkKind ℝK r₂
  ZCPriv r → checkKind ℝK r
  TCPriv r₁ r₂ → do
    checkKind ℝK r₁
    checkKind ℝK r₂

checkKind ∷ Kind → RExpPre → SM p ()
checkKind κ r = return ()
-- checkKind κ r = do
--   κ' ← inferKind r
--   case κ' ⊑ κ of
--     True → return ()
--     False → error $ "kind error on : " ⧺ pprender r ⧺ ", expected: " ⧺ pprender κ' ⧺ " to be a subtype of " ⧺ pprender κ

frKindEM ∷ KindE → SM p Kind
frKindEM κ = case frKindE κ of
  None → error "kind error"
  Some κ → return κ

-- inferKind ∷ RExpPre → SM p Kind
-- inferKind _ = return ()

--inferkindrexp

-- inferKind ∷ RExpPre → SM p Kind
-- inferKind = \case
--   VarRE x → inferKindVar x
--   ConstRE Top → return ℝK
--   ConstRE (AddTop r)
--     | dbl (truncate r) ≡ r → return ℕK
--     | otherwise            → return ℝK
--   MaxRE e₁ e₂ → do
--     κ₁ ← inferKind $ extract e₁
--     κ₂ ← inferKind $ extract e₂
--     frKindEM $ toKindE κ₁ ⊔ toKindE κ₂
--   MinRE e₁ e₂ → do
--     κ₁ ← inferKind $ extract e₁
--     κ₂ ← inferKind $ extract e₂
--     frKindEM $ toKindE κ₁ ⊔ toKindE κ₂
--   PlusRE e₁ e₂ → do
--     κ₁ ← inferKind $ extract e₁
--     κ₂ ← inferKind $ extract e₂
--     frKindEM $ toKindE κ₁ ⊔ toKindE κ₂
--   TimesRE e₁ e₂ → do
--     κ₁ ← inferKind $ extract e₁
--     κ₂ ← inferKind $ extract e₂
--     frKindEM $ toKindE κ₁ ⊔ toKindE κ₂
--   PowRE q e → do
--     κ ← inferKind $ extract e
--     return $ case ratDen q ≡ 1 of
--       True → κ
--       False → ℝK
--   EfnRE e → do
--     void $ inferKind $ extract e
--     return ℝK
--   LogRE e → do
--     void $ inferKind $ extract e
--     return ℝK
--   DivRE e₁ e₂ → do
--     κ₁ ← inferKind $ extract e₁
--     κ₂ ← inferKind $ extract e₂
--     frKindEM $ toKindE κ₁ ⊔ toKindE κ₂

-- kind checking
checkType ∷ ∀ p. (PRIV_C p) ⇒ Type RNF → SM p ()
checkType _ = return ()

-- TODO: call on prims

-- checkType ∷ ∀ p. (PRIV_C p) ⇒ Type RNF → SM p ()
-- checkType τA = case τA of
--   ℕˢT η → checkKind ℕK $ extract η
--   ℝˢT η → checkKind ℝK $ extract η
--   ℕT → skip
--   ℝT → skip
--   𝕀T η → checkKind ℕK $ extract η
--   𝔹T → skip
--   𝕊T → skip
--   SetT τ → checkType τ
--   𝕄T _ℓ _c rows me → do
--     case rows of
--       RexpRT r → do
--         checkKind ℕK $ extract r
--       StarRT → skip
--     case me of
--       EmptyME → skip
--       VarME x → checkSchemaVar x
--       ConsME (τ ∷ Type RExp) (me ∷ MExp RExp) → undefined
--       AppendME (me₁ ∷ MExp RExp) (me₂ ∷ MExp RExp) → undefined
--       RexpME r τ → do
--         checkKind ℕK $ extract r
--         checkType τ
--   𝔻T τ → checkType τ
--   τ₁ :⊕: τ₂ → do
--     checkType τ₁
--     checkType τ₂
--   τ₁ :⊗: τ₂ → do
--     checkType τ₁
--     checkType τ₂
--   τ₁ :&: τ₂ → do
--     checkType τ₁
--     checkType τ₂
--   (x :* τ₁) :⊸: (sσ :* τ₂) → do
--     checkType τ₁
--     mapEnvL contextTypeL ( \ γ → (x ↦ map normalizeRNF τ₁) ⩌ γ) $ do
--       eachWith sσ $ \ (x' :* s) → do
--         -- TODO
--         -- void $ checkProgramVar x'
--         checkSens $ map extract s
--       checkType τ₂
--   (x :* τ₁) :⊸⋆: (PEnv (pσ ∷ ProgramVar ⇰ Pr p' RExp) :* τ₂) → do
--     checkType τ₁
--     mapEnvL contextTypeL ( \ γ → (x ↦ map normalizeRNF τ₁) ⩌ γ) $ do
--       eachWith pσ $ \ (x' :* p) → do
--         -- TODO
--         -- void $ checkProgramVar x'
--         checkPriv $ map extract p
--       checkType τ₂
--   VarT x → void $ inferKindVar x -- make sure the kind is TypeK
--   ForallT x κ τ → do
--     mapEnvL contextKindL ( \ γ → (x ↦ κ) ⩌ γ) $ do
--       checkType τ
--   _ → error $ "checkType error on " ⧺ pprender τA

freshenSM ∷ Type RNF → SM p (Type RNF)
freshenSM τ = do
  n ← get
  let τ' :* n' = freshenType dø dø τ n
  put n'
  return τ'

freshenPM ∷ Type RNF → PM p (Type RNF)
freshenPM τ = do
  n ← get
  let τ' :* n' = freshenType dø dø τ n
  put n'
  return τ'

fixTVs ∷ ∀ p a. (PRIV_C p) ⇒ (ProgramVar ⇰ a) → SM p (ProgramVar ⇰ a)
fixTVs tvs = do
  δ ← askL contextKindL
  return $ assoc $ map (\(tv :* a) → (fixTV δ tv :* a)) $ list tvs

fixTV ∷ (𝕏 ⇰ a) → ProgramVar → ProgramVar
fixTV δ tv = case tv of
  TMVar x → case δ ⋕? x of
    None → TMVar x
    Some x' → TLVar x
  -- should not happen
  TLVar x → error "fixTVs error"

instance FunctorM ((⇰) 𝕏) where mapM = mapMDict

mapMDict ∷ (Monad m, Ord k) ⇒ (a → m b) → k ⇰ a → m (k ⇰ b)
mapMDict f kvs = do
  lst ← mapM (mapM f) $ list kvs
  return $ assoc lst

-- TODO: kind-checking
inferPrimitives ∷ ∀ p . (PRIV_C p) ⇒ (𝕏 ⇰ Type RNF) → SM p (𝕏 ⇰ Type RNF)
inferPrimitives prims = do
  mapM inferType prims

inferType ∷ ∀ p. (PRIV_C p) ⇒ Type RNF → SM p (Type RNF)
inferType τinit = do
  case τinit of
    VarT x → return $ VarT x
    ℕˢT r → return $ ℕˢT r
    ℝˢT r → return $ ℝˢT r
    ℕT → return $ ℕT
    ℝT → return $ ℝT
    𝕀T r → return $ 𝕀T r
    𝔹T → return $ 𝔹T
    𝕊T → return $ 𝕊T
    SetT τ → do
      τ₁ ← inferType τ
      return $ SetT τ₁
    𝕄T l c rows cols → do
      cols' ← inferMExp cols
      return $ 𝕄T l c rows cols'
    𝔻T τ → do
      τ₁ ← inferType τ
      return $ 𝔻T τ
    τ₁ :⊕: τ₂ → do
      τ₁' ← inferType τ₁
      τ₂' ← inferType τ₂
      return $ τ₁' :⊕: τ₂'
    τ₁ :⊗: τ₂ →  do
      τ₁' ← inferType τ₁
      τ₂' ← inferType τ₂
      return $ τ₁' :⊗: τ₂'
    τ₁ :&: τ₂ →  do
      τ₁' ← inferType τ₁
      τ₂' ← inferType τ₂
      return $ τ₁' :&: τ₂'
    (x :* τ₁) :⊸: (σ :* τ₂) → do
      mapEnvL contextTypeL ( \ γ → (x ↦ τ₁) ⩌ γ) $ do
        τ₁' ← inferType τ₁
        τ₂' ← inferType τ₂
        σ' ← fixTVs σ
        freshenSM $ (x :* τ₁') :⊸: (σ' :* τ₂')
    (x :* τ₁) :⊸⋆: (PEnv σ :* τ₂) → do
      mapEnvL contextTypeL ( \ γ → (x ↦ τ₁) ⩌ γ) $ do
        τ₁' ← inferType τ₁
        τ₂' ← inferType τ₂
        σ' ← fixTVs σ
        freshenSM $ (x :* τ₁') :⊸⋆: (PEnv σ' :* τ₂')
    ForallT x κ τ → do
      mapEnvL contextKindL (\ δ → (x ↦ κ) ⩌ δ) $ do
        τ' ← inferType τ
        freshenSM $ ForallT x κ τ'
    CxtT xs → return $ CxtT xs
    _ → error "inferType missing/unexpected case"

inferMExp ∷ ∀ p. (PRIV_C p) ⇒ MExp RNF → SM p (MExp RNF)
inferMExp me = case me of
  EmptyME → return EmptyME
  VarME x → return $ VarME x
  ConsME τ me → do
    τ' ← inferType τ
    me' ← inferMExp me
    return $ ConsME τ' me'
  AppendME me₁ me₂ → do
    me₁' ← inferMExp me₁
    me₂' ← inferMExp me₂
    return $ AppendME me₁' me₂'
  RexpME r τ → do
    τ' ← inferType τ
    return $ RexpME r τ'

inferSens ∷ ∀ p. (PRIV_C p) ⇒ SExpSource p RNF → SM p (Type RNF)
inferSens eA = case extract eA of
  ℕˢSE n → return $ ℕˢT $ ι n
  ℝˢSE d → return $ ℝˢT $ ι d
  ℕSE _n → return $ ℕT
  ℝSE _d → return $ ℝT
  VarSE x → do
    γ ← askL contextTypeL
    case γ ⋕? x of
      None → error $ concat
            [ "Variable lookup error: failed to find " ⧺ (pprender x) ⧺ " in the environment:\n"
            , pprender γ
            , "\n"
            , pprender $ ppLineNumbers $ pretty $ annotatedTag eA
            ]
      Some τ → do
        tell (TMVar x ↦ ι 1.0)
        return τ
  LetSE x e₁ e₂ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    σ₂ :* τ₂ ← hijack $ mapEnvL contextTypeL (\ γ → (x ↦ τ₁) ⩌ γ) $ inferSens e₂
    let (ς :* σ₂') = ifNone (zero :* σ₂) $ dview (TMVar x) σ₂
    do
        tell $ ς ⨵ σ₁
        tell σ₂'
        return τ₂
  TAbsSE x κ e → do
    mapEnvL contextKindL (\ δ → (x ↦ κ) ⩌ δ) $ do
      τ ← inferSens e
      return $ ForallT x κ τ
  TAppSE e τ' → do
    τ ← inferSens e
    case τ of
      ForallT x κ τ → do
        let τ'' = case κ of
              ℕK → case extract τ' of
                ℕˢT r → substTypeR x r τ
                VarT x' → substTypeR x (varRNF x') τ
                _ → error $ "in type-level application: expected static nat, got: " ⧺ pprender τ'
              ℝK → case extract τ' of
                ℝˢT r → substTypeR x r τ
                VarT x' → substTypeR x (varRNF x') τ
                _ → error $ "in type-level application: expected static real, got: " ⧺ pprender τ'
              CxtK → case extract τ' of
                CxtT xs → substTypeCxt x (list $ iter $ xs) τ
              TypeK → checkOption $ checkTypeLang $ substTL x (typeToTLExp $ extract τ') (typeToTLExp τ)
        return τ''
      _ → error $ "expected ForallT, got: " ⧺ pprender τ
  SFunSE x τ e → do
      checkType $ extract τ
      let τ' = extract τ
      σ :* τ'' ← hijack $ mapEnvL contextTypeL (\ γ → (x ↦ τ') ⩌ γ) $ inferSens e
      let σ' = case σ ⋕? TMVar x of
                 None → (TMVar x ↦ bot) ⩌ σ
                 Some _ → σ
      let σ'' = assoc $ map (\(TMVar x' :* s) → (TMVar x' :* s)) $ list σ'
      do
          tell $ snd $ ifNone (zero :* σ') $ dview (TMVar x) σ'
          return $ (x :* τ') :⊸: (σ'' :* τ'')
  AppSE e₁ xsO e₂ → do
    τ₁ ← inferSens e₁
    σ₂ :* τ₂ ← hijack $ inferSens e₂
    allInScopeₜₘ ← map pow $ mapp TMVar $ map list $ map keys $ askL contextTypeL
    allInScopeₜₗ ← map pow $ mapp TLVar $ map list $ map keys $ askL contextKindL
    let xsₜₘ = elim𝑂 allInScopeₜₘ (\xs0' → pow $ getTMVs xs0' Nil) xsO
    let xsₜₗ = elim𝑂 allInScopeₜₗ (\xs0' → pow $ getTLVs xs0' Nil) xsO
    let xs = xsₜₘ ∪ xsₜₗ
    case xsₜₘ ⊆ allInScopeₜₘ ⩓ xsₜₗ ⊆ allInScopeₜₗ of
      True → skip
      False → error $ "provided variables to application which are not in scope: " ⧺ show𝕊 (xsₜₘ ∖ allInScopeₜₘ) ⧺ show𝕊 (xsₜₗ ∖ allInScopeₜₗ)
    case (τ₁) of
      (x :* τ₁₁) :⊸: (sσ :* τ₁₂) | alphaEquiv dø dø τ₁₁ τ₂ → do
        tell $ (sσ ⋕! (TMVar x)) ⨵ (restrict xs σ₂)
        tell $ top ⨵ (without xs σ₂)
        tell $ without (single $ TMVar x) sσ
        return $ substGammaSens σ₂ x τ₁₂
      (x :* τ₁₁) :⊸: (sσ :* τ₁₂) → error $ concat
            [ "AppSE error 1 (argument type mismatch): \n"
            , "expected: " ⧺ pprender τ₁₁
            , "\n"
            , "got: " ⧺ pprender τ₂
            , "\n"
            , "in the function: " ⧺ (pprender ((x :* τ₁₁) :⊸: (sσ :* τ₁₂)))
            , pprender $ ppLineNumbers $ pretty $ annotatedTag eA
            ]
      _ →  error $ concat
            [ "AppSE error 2 (tried to apply a non sλ): "
            , pprender τ₁
            , pprender $ ppLineNumbers $ pretty $ annotatedTag eA
            ]
  PFunSE x τ e → do
    checkType $ extract τ
    let τ' = extract τ
    σ :* τ'' ← smFromPM $ hijack $ mapEnvL contextTypeL (\ γ → (x ↦ τ') ⩌ γ) $ inferPriv e
    return $ (x :* τ') :⊸⋆: (PEnv σ :* τ'')
  _ → error $ concat
        [ "inferSens unknown expression type: "
        , "\n"
        , pprender $ ppLineNumbers $ pretty $ annotatedTag eA
        ]

inferPriv ∷ ∀ p. (PRIV_C p) ⇒ PExpSource p RNF → PM p (Type RNF)
inferPriv eA = case extract eA of
  ReturnPE e → do
    pmFromSM $ inferSens e
  BindPE x e₁ e₂ → do
    τ₁ ← inferPriv e₁
    σ₂ :* τ₂ ← hijack $ mapEnvL contextTypeL (\ γ → (x ↦ τ₁) ⩌ γ) $ inferPriv e₂
    tell $ delete (TMVar x) σ₂
    return τ₂
  AppPE e₁ xsO e₂ → do
    τ₁ ← pmFromSM $ inferSens e₁
    σ₂ :* τ₂ ← pmFromSM $ hijack $ inferSens e₂
    allInScopeₜₘ ← map pow $ mapp TMVar $ map list $ map keys $ askL contextTypeL
    allInScopeₜₗ ← map pow $ mapp TLVar $ map list $ map keys $ askL contextKindL
    let xsₜₘ = elim𝑂 allInScopeₜₘ (\xs0' → pow $ getTMVs xs0' Nil) xsO
    let xsₜₗ = elim𝑂 allInScopeₜₗ (\xs0' → pow $ getTLVs xs0' Nil) xsO
    let xs = xsₜₘ ∪ xsₜₗ
    case xsₜₘ ⊆ allInScopeₜₘ ⩓ xsₜₗ ⊆ allInScopeₜₗ of
      True → skip
      False → error $ "provided variables to application which are not in scope: " ⧺ show𝕊 (xsₜₘ ∖ allInScopeₜₘ) ⧺ show𝕊 (xsₜₗ ∖ allInScopeₜₗ)
    case τ₁ of
      (x :* τ₁₁) :⊸⋆: (PEnv (σ' ∷ ProgramVar ⇰ Pr p' RNF) :* τ₁₂) | (τ₁₁ ≡ τ₂) ⩓ (joins (values σ₂) ⊑ one) →
        case eqPRIV (priv @ p) (priv @ p') of
          None → error "not same priv mode"
          Some Refl → do
            let (pₓ :* σ'') = ifNone (makePr zero :* σ') $ dview (TMVar x) σ'
            -- TODO: change iteratePr to something functionally the same but less hacky
            let σ₂' = mapOn (restrict xs σ₂) $ (\ i → iteratePr i pₓ) ∘ truncateRNF ∘ unSens
            let σinf = mapOn (without xs σ₂) $ (\ i → iteratePr i $ makePr top) ∘ truncateRNF ∘ unSens
            tell $ σ₂'
            tell $ σinf
            tell σ''
            return $ substGammaPr σ₂ x τ₁₂
      (x :* τ₁₁) :⊸⋆: (PEnv (σ' ∷ ProgramVar ⇰ Pr p' RNF) :* τ₁₂) → error $ concat
            [ "AppPE error 1 (argument type/sensitivity mismatch): "
            , "expected: " ⧺ pprender τ₁₁
            , "\n"
            , "got: " ⧺ pprender τ₂
            , "\n"
            , pprender $ ppLineNumbers $ pretty $ annotatedTag eA
            , "\n or sσ: \n"
            , pprender σ₂
            , "\nhas max sensitivity GT one"
            ]
      _ → error $ "AppPE expected pλ, got: " ⧺ pprender τ₁
  _ → error $ concat
        [ "inferPriv unknown expression type: "
        , "\n"
        , pprender $ ppLineNumbers $ pretty $ annotatedTag eA
        ]

checkOption ∷ 𝑂 a → a
checkOption = \case
  None → error "checkOption failed"
  Some α → α


substTLMExp ∷ 𝕏 → TLExp RNF → MExp RNF → MExp RNF
substTLMExp x tl = \case
  EmptyME → EmptyME
  VarME x' → VarME x'
  ConsME τ me →
    ConsME (checkOption $ checkTypeLang (substTL x tl (typeToTLExp τ))) (substTLMExp x tl me)
  AppendME me₁ me₂ → AppendME (substTLMExp x tl me₁) (substTLMExp x tl me₂)
  RexpME r τ → RexpME r (checkOption $ checkTypeLang (substTL x tl (typeToTLExp τ)))


substTL ∷ 𝕏 → TLExp RNF → TLExp RNF → TLExp RNF
substTL x tl₁ tl₂ = case tl₂ of
  VarTE x' → case x ≡ x' of
    True → tl₁
    False → VarTE x'
  -- Type Stuff →
  ℕˢTE r → ℕˢTE r
  ℝˢTE r → ℝˢTE r
  ℕTE → ℕTE
  ℝTE → ℝTE
  𝕀TE r → 𝕀TE r
  𝔹TE → 𝔹TE
  𝕊TE → 𝕊TE
  SetTE τ → SetTE $ substTL x tl₁ τ
  𝕄TE ℓ c rows cols → 𝕄TE ℓ c rows $ substTLMExp x tl₁ cols
  𝔻TE τ → 𝔻TE $ substTL x tl₁ τ
  τ₁ :⊕♭: τ₂ → substTL x tl₁ τ₁ :⊕♭: substTL x tl₁ τ₂
  τ₁ :⊗♭: τ₂ → substTL x tl₁ τ₁ :⊗♭: substTL x tl₁ τ₂
  τ₁ :&♭: τ₂ → substTL x tl₁ τ₁ :&♭: substTL x tl₁ τ₂
  -- TODO: sens -> tlexp -> then substTL -> sens
  (x' :* τ₁) :⊸♭: (sσ :* τ₂) → (x' :* substTL x tl₁ τ₁) :⊸♭: (sσ :* substTL x tl₁ τ₂)
  (x' :* τ₁) :⊸⋆♭: (pσ :* τ₂) → (x' :* substTL x tl₁ τ₁) :⊸⋆♭: (pσ :* substTL x tl₁ τ₂)
  ForallTE x' κ τ → ForallTE x' κ $ substTL x tl₁ τ
   -- RExp Stuff →
  NatTE n → NatTE n
  NNRealTE d → NNRealTE d
  MaxTE τ₁ τ₂ → MaxTE (substTL x tl₁ τ₁) (substTL x tl₁ τ₂)
  MinTE τ₁ τ₂ → MinTE (substTL x tl₁ τ₁) (substTL x tl₁ τ₂)
  PlusTE τ₁ τ₂ → PlusTE (substTL x tl₁ τ₁) (substTL x tl₁ τ₂)
  TimesTE τ₁ τ₂ → TimesTE (substTL x tl₁ τ₁) (substTL x tl₁ τ₂)
  DivTE τ₁ τ₂ → DivTE (substTL x tl₁ τ₁) (substTL x tl₁ τ₂)
  RootTE τ → RootTE $ substTL x tl₁ τ
  LogTE τ → LogTE $ substTL x tl₁ τ
  TopTE → TopTE
   -- Privacy Stuff →
  PairTE τ₁ τ₂ → PairTE (substTL x tl₁ τ₁) (substTL x tl₁ τ₂)

substPriv ∷ (PRIV_C p) ⇒ 𝕏 → Pr p RNF → Type RNF → Type RNF
substPriv x p τ =
  let τ' = checkTypeLang $ substTL x (privToTLExp p) (typeToTLExp τ) in
        case τ' of
          None → error "type coercion failed"
          Some τ'' → τ''

substPrivExp ∷ ∀ p p'. (PRIV_C p, PRIV_C p') ⇒ 𝕏 → Pr p' RNF → Pr p RNF → Pr p' RNF
substPrivExp x pe pr =
  case eqPRIV (priv @ p) (priv @ p') of
    None → error "privacy variants dont match"
    Some Refl → do
      case (pe,pr) of
        ((EpsPriv r) , (EpsPriv r')) → EpsPriv $ substRNF x r r'
        ((EDPriv r₁ r₂) , (EDPriv r₁' r₂')) → EDPriv (substRNF x r₁ r₁') (substRNF x r₂ r₂')
        ((RenyiPriv r₁ r₂) , (RenyiPriv r₁' r₂')) → RenyiPriv (substRNF x r₁ r₁') (substRNF x r₂ r₂')
        ((ZCPriv r) , (ZCPriv r')) → ZCPriv $ substRNF x r r'
        ((TCPriv r₁ r₂) , (TCPriv r₁' r₂')) → TCPriv (substRNF x r₁ r₁') (substRNF x r₂ r₂')

substSens ∷ 𝕏 → Sens RNF → Type RNF → Type RNF
substSens x s τ =
  let τ' = checkTypeLang $ substTL x (sensToTLExp s) (typeToTLExp τ) in
        case τ' of
          None → error "type coercion failed"
          Some τ'' → τ''

substType ∷ 𝕏 → Type RNF → Type RNF → Type RNF
substType x τ₁ τ₂ =
  let τ' = checkTypeLang $ substTL x (typeToTLExp τ₁) (typeToTLExp τ₁) in
        case τ' of
          None → error "type coercion failed"
          Some τ'' → τ''

substMExpR ∷ 𝕏 → RNF → MExp RNF → MExp RNF
substMExpR x r' = \case
  EmptyME → EmptyME
  VarME x' → VarME x'
  ConsME τ me → ConsME (substTypeR x r' τ) (substMExpR x r' me)
  AppendME me₁ me₂ → AppendME (substMExpR x r' me₁) (substMExpR x r' me₂)
  RexpME r τ → RexpME (substRNF x  r' r) (substTypeR x r' τ)

substPrivR ∷ 𝕏 → RNF → Pr p RNF → Pr p RNF
substPrivR x' r' p' = case p' of
  EpsPriv r → EpsPriv $ substRNF x' r' r
  EDPriv r₁ r₂ → EDPriv (substRNF x' r' r₁) (substRNF x' r' r₂)
  RenyiPriv r₁ r₂ → RenyiPriv (substRNF x' r' r₁) (substRNF x' r' r₂)
  ZCPriv r → ZCPriv $ substRNF x' r' r
  TCPriv r₁ r₂ → TCPriv (substRNF x' r' r₁) (substRNF x' r' r₂)

substMExpCxt ∷ 𝕏 → 𝐿 ProgramVar → MExp RNF → MExp RNF
substMExpCxt x xs = \case
  EmptyME → EmptyME
  VarME x' → VarME x'
  ConsME τ me → ConsME (substTypeCxt x xs τ) (substMExpCxt x xs me)
  AppendME me₁ me₂ → AppendME (substMExpCxt x xs me₁) (substMExpCxt x xs me₂)
  RexpME r τ → RexpME r (substTypeCxt x xs τ)

substTypeCxt ∷ 𝕏 → 𝐿 ProgramVar → Type RNF → Type RNF
substTypeCxt x' xs τ' = case τ' of
  VarT x → VarT x
  ℕˢT r → ℕˢT r
  ℝˢT r → ℝˢT r
  ℕT → ℕT
  ℝT → ℝT
  𝕀T r → 𝕀T r
  𝔹T → 𝔹T
  𝕊T → 𝕊T
  SetT τ → SetT $ substTypeCxt x' xs τ
  𝕄T ℓ c rs me → 𝕄T ℓ c rs $ substMExpCxt x' xs me
  𝔻T τ → 𝔻T $ substTypeCxt x' xs τ
  τ₁ :⊕: τ₂ → substTypeCxt x' xs τ₁ :⊕: substTypeCxt x' xs τ₂
  τ₁ :⊗: τ₂ → substTypeCxt x' xs τ₁ :⊗: substTypeCxt x' xs τ₂
  τ₁ :&: τ₂ → substTypeCxt x' xs τ₁ :&: substTypeCxt x' xs τ₂
  (x :* τ₁) :⊸: (sσ :* τ₂) → (x :* substTypeCxt x' xs τ₁) :⊸: ((spliceCxt x' xs sσ) :* substTypeCxt x' xs τ₂)
  (x :* τ₁) :⊸⋆: (PEnv pσ :* τ₂) → (x :* substTypeCxt x' xs τ₁) :⊸⋆: (PEnv (spliceCxt x' xs pσ) :* substTypeCxt x' xs τ₂)
  ForallT x κ τ → ForallT x κ $ substTypeCxt x' xs τ

spliceCxt ∷ 𝕏 → 𝐿 ProgramVar → ProgramVar ⇰ a → ProgramVar ⇰ a
spliceCxt x' xs σ = case σ ⋕? (TLVar x') of
  None → σ
  Some a → without (single (TLVar x')) (spliceCxt' xs a σ)

spliceCxt' ∷ 𝐿 ProgramVar → a → ProgramVar ⇰ a → ProgramVar ⇰ a
spliceCxt' Nil _a σ = σ
spliceCxt' (x:&xs) a σ = spliceCxt' xs a $ (x ↦ a) ⩌ σ

substTypeR ∷ 𝕏 → RNF → Type RNF → Type RNF
substTypeR x' r' τ' = case τ' of
  VarT x → VarT x
  ℕˢT r → ℕˢT $ substRNF x' r' r
  ℝˢT r → ℝˢT $ substRNF x' r' r
  ℕT → ℕT
  ℝT → ℝT
  𝕀T r → 𝕀T $ substRNF x' r' r
  𝔹T → 𝔹T
  𝕊T → 𝕊T
  SetT τ → SetT $ substTypeR x' r' τ
  𝕄T ℓ c rs me →
    let rs' = case rs of
          RexpRT r → RexpRT $ substRNF x' r' r
          StarRT → StarRT
    in 𝕄T ℓ c rs' $ substMExpR x' r' me
  𝔻T τ → 𝔻T $ substTypeR x' r' τ
  τ₁ :⊕: τ₂ → substTypeR x' r' τ₁ :⊕: substTypeR x' r' τ₂
  τ₁ :⊗: τ₂ → substTypeR x' r' τ₁ :⊗: substTypeR x' r' τ₂
  τ₁ :&: τ₂ → substTypeR x' r' τ₁ :&: substTypeR x' r' τ₂
  (x :* τ₁) :⊸: (sσ :* τ₂) →
    (x :* substTypeR x' r' τ₁) :⊸: (assoc (map (\(xₐ :* s) → xₐ :* Sens (substRNF x' r' (unSens s))) (iter sσ)) :* substTypeR x' r' τ₂)
  (x :* τ₁) :⊸⋆: (PEnv pσ :* τ₂) →
    (x :* substTypeR x' r' τ₁) :⊸⋆: ((PEnv (assoc (map (\(xₐ :* p) → xₐ :* substPrivR x' r' p) (iter pσ)))) :* substTypeR x' r' τ₂)
  ForallT x κ τ → ForallT x κ $ substTypeR x' r' τ
  _ → error $ "error in substTypeR: " ⧺ pprender τ'

freshenSTerm ∷ ∀ p. (PRIV_C p) ⇒ (𝕏 ⇰ 𝕏) → (𝕏 ⇰ 𝕏) → SExpSource p RNF → ℕ → SExpSource p RNF ∧ ℕ
freshenSTerm ρ β eA nInit = do
  let np1 = nInit + one
  let ecxt = annotatedTag eA
  let (z :* nFinal) = case extract eA of
        ℕˢSE n → (ℕˢSE n :* nInit)
        ℝˢSE d → (ℝˢSE d :* nInit)
        ℕSE n → (ℕSE n :* nInit)
        ℝSE d → (ℝSE d :* nInit)
        VarSE x → (VarSE (freshenTMV β x) :* nInit)
        LetSE x e₁ e₂ → do
          let xⁿ = 𝕏 {𝕩name=(𝕩name x), 𝕩Gen=Some nInit}
          let e₁' :* n' = freshenSTerm ρ β e₁ np1
          let e₂' :* n'' = freshenSTerm ρ ((x↦ xⁿ) ⩌ β) e₂ n'
          (LetSE xⁿ e₁' e₂' :* n'')
        TAbsSE x κ e → do
          let xⁿ = 𝕏 {𝕩name=(𝕩name x), 𝕩Gen=Some nInit}
          let e' :* n' = freshenSTerm ((x↦ xⁿ) ⩌ ρ) β e np1
          (TAbsSE xⁿ κ e' :* n')
        TAppSE e τ → do
          let e' :* n' = freshenSTerm ρ β e nInit
          let tcxt = annotatedTag τ
          let τ' :* n'' = freshenType ρ β (extract τ) n'
          (TAppSE e' (Annotated tcxt τ') :* n'')
        SFunSE x τ e → do
          let tcxt = annotatedTag τ
          let τ' :* n' = freshenType ρ β (extract τ) np1
          let xⁿ = 𝕏 {𝕩name=(𝕩name x), 𝕩Gen=Some nInit}
          let e' :* n'' = freshenSTerm ρ ((x↦ xⁿ) ⩌ β) e n'
          (SFunSE xⁿ (Annotated tcxt τ') e' :* n'')
        AppSE e₁ xsO e₂ → do
          let e₁' :* n' = freshenSTerm ρ β e₁ nInit
          let xsO' = mapp (\x → freshenRef ρ β x) xsO
          let e₂' :* n'' = freshenSTerm ρ β e₂ n'
          (AppSE e₁' xsO' e₂' :* n'')
        PFunSE x τ e → do
          let tcxt = annotatedTag τ
          let xⁿ = 𝕏 {𝕩name=(𝕩name x), 𝕩Gen=Some nInit}
          let τ' :* n' = freshenType ρ β (extract τ) np1
          let e' :* n'' = freshenPTerm ρ ((x↦ xⁿ) ⩌ β) e n'
          (PFunSE xⁿ (Annotated tcxt τ') e' :* n'')
  (Annotated ecxt z) :* nFinal

freshenPTerm ∷ ∀ p. (PRIV_C p) ⇒ (𝕏 ⇰ 𝕏) → (𝕏 ⇰ 𝕏) → PExpSource p RNF → ℕ → PExpSource p RNF ∧ ℕ
freshenPTerm ρ β eA nInit = do
  let np1 = nInit + one
  let ecxt = annotatedTag eA
  let (z :* nFinal) = case extract eA of
        ReturnPE e → do
          let e' :* n' = freshenSTerm ρ β e nInit
          (ReturnPE e' :* n')
        BindPE x e₁ e₂ → do
          let xⁿ = 𝕏 {𝕩name=(𝕩name x), 𝕩Gen=Some nInit}
          let e₁' :* n' = freshenPTerm ρ β e₁ np1
          let e₂' :* n'' = freshenPTerm ρ ((x↦ xⁿ) ⩌ β) e₂ n'
          (BindPE xⁿ e₁' e₂' :* n'')
        AppPE e₁ xsO e₂ → do
          let e₁' :* n' = freshenSTerm ρ β e₁ nInit
          let xsO' = mapp (\x → freshenRef ρ β x) xsO
          let e₂' :* n'' = freshenSTerm ρ β e₂ n'
          (AppPE e₁' xsO' e₂' :* n'')
  (Annotated ecxt $ z) :* nFinal

substGammaSens ∷ (ProgramVar ⇰ Sens RNF) → 𝕏 → Type RNF → Type RNF
substGammaSens σ₉ x₉ τ₉ = case τ₉ of
  VarT x → VarT x
  ℕˢT r → ℕˢT r
  ℝˢT r → ℝˢT r
  ℕT → ℕT
  ℝT → ℝT
  𝕀T r → 𝕀T r
  𝔹T → 𝔹T
  𝕊T → 𝕊T
  SetT τ → SetT $ substGammaSens σ₉ x₉ τ
  𝕄T ℓ c rs me → 𝕄T ℓ c rs $ substGammaMexpSens σ₉ x₉ me
  𝔻T τ → 𝔻T $ substGammaSens σ₉ x₉ τ
  τ₁ :⊕: τ₂ → substGammaSens σ₉ x₉ τ₁ :⊕: substGammaSens σ₉ x₉ τ₂
  τ₁ :⊗: τ₂ → substGammaSens σ₉ x₉ τ₁ :⊗: substGammaSens σ₉ x₉ τ₂
  τ₁ :&: τ₂ → substGammaSens σ₉ x₉ τ₁ :&: substGammaSens σ₉ x₉ τ₂
  (x :* τ₁) :⊸: (sσ :* τ₂) → do
    (x :* substGammaSens σ₉ x₉ τ₁) :⊸: ((substGammaSensEnv σ₉ x₉ sσ) :* substGammaSens σ₉ x₉ τ₂)
  (x :* τ₁) :⊸⋆: (PEnv pσ :* τ₂) → do
    (x :* substGammaSens σ₉ x₉ τ₁) :⊸⋆: (PEnv (substGammaPrEnv σ₉ x₉ pσ) :* substGammaSens σ₉ x₉ τ₂)
  ForallT x κ τ → ForallT x κ $ substGammaSens σ₉ x₉ τ

substGammaPr ∷ (ProgramVar ⇰ Sens RNF) → 𝕏 → Type RNF → Type RNF
substGammaPr σ₉ x₉ τ₉ = case τ₉ of
  VarT x → VarT x
  ℕˢT r → ℕˢT r
  ℝˢT r → ℝˢT r
  ℕT → ℕT
  ℝT → ℝT
  𝕀T r → 𝕀T r
  𝔹T → 𝔹T
  𝕊T → 𝕊T
  SetT τ → SetT $ substGammaPr σ₉ x₉ τ
  𝕄T ℓ c rs me → 𝕄T ℓ c rs $ substGammaMexpPr σ₉ x₉ me
  𝔻T τ → 𝔻T $ substGammaPr σ₉ x₉ τ
  τ₁ :⊕: τ₂ → substGammaPr σ₉ x₉ τ₁ :⊕: substGammaPr σ₉ x₉ τ₂
  τ₁ :⊗: τ₂ → substGammaPr σ₉ x₉ τ₁ :⊗: substGammaPr σ₉ x₉ τ₂
  τ₁ :&: τ₂ → substGammaPr σ₉ x₉ τ₁ :&: substGammaPr σ₉ x₉ τ₂
  (x :* τ₁) :⊸: (sσ :* τ₂) → do
    (x :* substGammaPr σ₉ x₉ τ₁) :⊸: (sσ :* substGammaPr σ₉ x₉ τ₂)
  (x :* τ₁) :⊸⋆: (PEnv pσ :* τ₂) → do
    (x :* substGammaPr σ₉ x₉ τ₁) :⊸⋆: (PEnv (substGammaPrEnv σ₉ x₉ pσ) :* substGammaPr σ₉ x₉ τ₂)
  ForallT x κ τ → ForallT x κ $ substGammaPr σ₉ x₉ τ

substGammaSensEnv ∷ (ProgramVar ⇰ Sens RNF) → 𝕏 → (ProgramVar ⇰ Sens RNF) → (ProgramVar ⇰ Sens RNF)
substGammaSensEnv σ₉ x₉ ς = case ς ⋕? TMVar x₉ of
  None → ς
  Some η → without (single $ TMVar x₉) $ (η ⨵ σ₉) ⩌ ς

substGammaPrEnv ∷ ∀ p. (PRIV_C p) ⇒ (ProgramVar ⇰ Sens RNF) → 𝕏 → (ProgramVar ⇰ Pr p RNF) → (ProgramVar ⇰ Pr p RNF)
substGammaPrEnv σ₉ x₉ ς = case ς ⋕? TMVar x₉ of
  None → ς
  Some η → without (single $ TMVar x₉) $ (map (\x → iteratePr (unSens x) η) σ₉) ⩌ ς

substGammaMexpSens ∷ (ProgramVar ⇰ Sens RNF) → 𝕏 → MExp RNF → MExp RNF
substGammaMexpSens σ₉ x₉ me₉ = case me₉ of
  EmptyME → EmptyME
  VarME x' → VarME x'
  ConsME τ me → ConsME (substGammaSens σ₉ x₉ τ) (substGammaMexpSens σ₉ x₉ me)
  AppendME me₁ me₂ → AppendME (substGammaMexpSens σ₉ x₉ me₁) (substGammaMexpSens σ₉ x₉ me₂)
  RexpME r τ → RexpME r (substGammaSens σ₉ x₉ τ)

substGammaMexpPr ∷ (ProgramVar ⇰ Sens RNF) → 𝕏 → MExp RNF → MExp RNF
substGammaMexpPr σ₉ x₉ me₉ = case me₉ of
  EmptyME → EmptyME
  VarME x' → VarME x'
  ConsME τ me → ConsME (substGammaPr σ₉ x₉ τ) (substGammaMexpPr σ₉ x₉ me)
  AppendME me₁ me₂ → AppendME (substGammaMexpPr σ₉ x₉ me₁) (substGammaMexpPr σ₉ x₉ me₂)
  RexpME r τ → RexpME r (substGammaPr σ₉ x₉ τ)

getTMVs ∷ 𝐿 ProgramVar → 𝐿 ProgramVar → 𝐿 ProgramVar
getTMVs Nil acc = acc
getTMVs (TMVar x :& xs) acc = getTMVs xs (TMVar x :& acc)
getTMVs (TLVar x :& xs) acc = getTMVs xs acc

getTLVs ∷ 𝐿 ProgramVar → 𝐿 ProgramVar → 𝐿 ProgramVar
getTLVs Nil acc = acc
getTLVs (TMVar x :& xs) acc = getTLVs xs acc
getTLVs (TLVar x :& xs) acc = getTLVs xs (TLVar x :& acc)

getConsMAt :: (MExp r) → ℕ → (Type r)
getConsMAt EmptyME _ = error "matrix/dataframe column index error"
getConsMAt (ConsME τ _) 0 = τ
getConsMAt (ConsME _ m) n = (getConsMAt m (n-1))
getConsMAt _ _ = error "expected ConsME"

joinConsMs :: (MExp r) → (MExp r) → (MExp r)
joinConsMs (ConsME τ me₁) me₂ = (ConsME τ (joinConsMs me₁ me₂))
joinConsMs EmptyME me = me
joinConsMs _ _ = error "joinConsMs error: expected ConsME or EmptyME"

isRealMExp ∷ MExp RNF → PM p 𝔹
isRealMExp me = case me of
  EmptyME → do
    return False
  VarME x → do
    ᴍ ← askL contextMExpL
    case ᴍ ⋕? x of
      None → error $ "isRealMExp: " ⧺ fromString (show x) -- TypeSource Error
      Some m → do
        isRealMExp $ m
  ConsME τ me₁ → do
    let b = isRealType τ
    a ← isRealMExp $ me₁
    return $ a ⩓ b
  AppendME me₁ me₂ → do
    a ← isRealMExp $ me₁
    b ← isRealMExp $ me₂
    return $ a ⩓ b
  RexpME _r τ → return $ isRealType τ

isRealType :: (Type r) → 𝔹
isRealType (ℝˢT _r) = True
isRealType (ℝT) = True
isRealType _ = False

matchArgPrivs ∷ 𝐿 (𝕏 ⇰ Sens RNF) → 𝐿 (Pr p RNF) → 𝐿 (𝕏 ⇰ Pr p RNF)
matchArgPrivs xss xps = list $ zipWith (↦) (fold Nil (⧺) (map (list ∘ uniques ∘ keys) xss)) xps
