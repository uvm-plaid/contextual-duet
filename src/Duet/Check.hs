{-# LANGUAGE PartialTypeSignatures #-}

module Duet.Check where

import Duet.UVMHS

import Duet.Pretty ()
import Duet.Syntax
import Duet.RNF2

getConsMAt :: (MExp r) → ℕ → (Type r)
getConsMAt EmptyME _ = error "matrix/dataframe column index error"
getConsMAt (ConsME τ _) 0 = τ
getConsMAt (ConsME _ m) n = (getConsMAt m (n-1))
getConsMAt _ _ = error "expected ConsME"

joinConsMs :: (MExp r) → (MExp r) → (MExp r)
joinConsMs (ConsME τ me₁) me₂ = (ConsME τ (joinConsMs me₁ me₂))
joinConsMs EmptyME me = me
joinConsMs _ _ = error "joinConsMs error: expected ConsME or EmptyME"

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

newtype SM (p ∷ PRIV) a = SM { unSM ∷ ReaderT Context (WriterT (𝕏 ⇰ Sens RNF) (ErrorT TypeError ID)) a }
  deriving
  (Functor
  ,Return,Bind,Monad
  ,MonadError TypeError
  ,MonadReader Context
  ,MonadWriter (𝕏 ⇰ Sens RNF))

mkSM ∷ (𝕏 ⇰ Kind → 𝕏 ⇰ Type RNF → 𝕏 ⇰ MExp RNF → TypeError ∨ ((𝕏 ⇰ Sens RNF) ∧ a)) → SM p a
mkSM f = SM $ ReaderT $ \ (Context δ γ ᴍ) → WriterT $ ErrorT $ ID $ f δ γ ᴍ

runSM ∷ 𝕏 ⇰ Kind → 𝕏 ⇰ Type RNF → 𝕏 ⇰ MExp RNF → SM p a → TypeError ∨ ((𝕏 ⇰ Sens RNF) ∧ a)
runSM δ γ ᴍ = unID ∘ unErrorT ∘ unWriterT ∘ runReaderT (Context δ γ ᴍ) ∘ unSM

newtype PM (p ∷ PRIV) a = PM { unPM ∷ ReaderT Context (WriterT (𝕏 ⇰ Pr p RNF) (ErrorT TypeError ID)) a }
  deriving
  (Functor
  ,Return,Bind,Monad
  ,MonadError TypeError
  ,MonadReader Context
  ,MonadWriter (𝕏 ⇰ Pr p RNF))

mkPM ∷ (𝕏 ⇰ Kind → 𝕏 ⇰ Type RNF → 𝕏 ⇰ MExp RNF → TypeError ∨ ((𝕏 ⇰ Pr p RNF) ∧ a)) → PM p a
mkPM f = PM $ ReaderT $ \ (Context δ γ ᴍ) → WriterT $ ErrorT $ ID $ f δ γ ᴍ

--      kind env   type env    expression   type error    sens costs     expressions' type
--         ⌄⌄         ⌄⌄           ⌄⌄         ⌄⌄             ⌄⌄            ⌄⌄
runPM ∷ 𝕏 ⇰ Kind → 𝕏 ⇰ Type RNF → 𝕏 ⇰ MExp RNF → PM p a → TypeError ∨ ((𝕏 ⇰ Pr p RNF) ∧ a)
runPM δ γ ᴍ = unID ∘ unErrorT ∘ unWriterT ∘ runReaderT (Context δ γ ᴍ) ∘ unPM

smFromPM ∷ PM p a → SM p a
smFromPM xM = mkSM $ \ δ γ ᴍ →
  mapInr (mapFst $ map $ Sens ∘ (×) top ∘ truncateRNF ∘ indicatorPr) $ runPM δ γ ᴍ xM

pmFromSM ∷ (PRIV_C p) ⇒ SM p a → PM p a
pmFromSM xM = mkPM $ \ δ γ ᴍ →
  mapInr (mapFst $ map $ makePr ∘ (×) top ∘ truncateRNF ∘ unSens) $ runSM δ γ ᴍ xM

mapPPM ∷ (Pr p₁ RNF → Pr p₂ RNF) → PM p₁ a → PM p₂ a
mapPPM f xM = mkPM $ \ δ γ ᴍ → mapInr (mapFst $ map f) $ runPM δ γ ᴍ xM

checkSensLang ∷ TLExp RExp → 𝑂 (Sens RExp)
checkSensLang e = do
  η ← checkRExpLang e
  return $ Sens η

checkPrivLang ∷ (PRIV_C p) ⇒ PRIV_W p → TLExp RExp → 𝑂 (Pr p RExp)
checkPrivLang p e₀ = case p of
  EPS_W → do
    η ← checkRExpLang e₀
    return $ EpsPriv η
  ED_W → do
    case extract e₀ of
      PairTE e₁ e₂ → do
        η₁ ← checkRExpLang e₁
        η₂ ← checkRExpLang e₂
        return $ EDPriv η₁ η₂
      _ → error "non pair TLExp while coercing in ED_W mode"
  _ → undefined


privToTLExp ∷ Pr p RExp → TLExpPre RExp
privToTLExp p = undefined

sensToTLExp ∷ Sens RExp → TLExpPre RExp
sensToTLExp s = undefined

typeToTLExp ∷ Type RExp → TLExpPre RExp
typeToTLExp τ = undefined

rexpToTLExp ∷ Type RExp → TLExpPre RExp
rexpToTLExp τ = undefined

-- TODO: QUESTION: need parser context
-- typeToTLExp ∷ Type RExp → TLExpPre RExp
-- typeToTLExp tl₁  = \case
--   VarT x → VarTE x
--   ℕˢT r → ℕˢTE r
--   ℝˢT r → ℝˢTE r
--   ℕT → ℕTE
--   ℝT → ℝTE
--   𝕀T r → 𝕀TE r
--   𝔹T → 𝔹TE
--   𝕊T → 𝕊TE
--   SetT τ → SetTE $ typeToTLExp τ
--   𝕄T ℓ c rows cols → 𝕄TE ℓ c rows cols
--   𝔻T τ → 𝔻TE $ typeToTLExp τ
--   τ₁ :⊕: τ₂ → typeToTLExp τ₁ :⊕♭: typeToTLExp τ₂
--   τ₁ :⊗: τ₂ → typeToTLExp τ₁ :⊗♭: typeToTLExp τ₂
--   τ₁ :&: τ₂ → typeToTLExp τ₁ :&♭: typeToTLExp τ₂
--   τ₁ :⊸: (s :* τ₂) → typeToTLExp τ₁ :⊸♭: (s :* typeToTLExp τ₂)
--   (x :* τ₁) :⊸⋆: (pσ :* τ₂) → (x :* typeToTLExp τ₁) :⊸⋆♭: (pσ :* typeToTLExp τ₂)
--   ForallT x κ τ → ForallTE x κ $ typeToTLExp τ

checkTypeLang ∷ TLExp RExp → 𝑂 (Type RExp)
checkTypeLang e₀ = case extract e₀ of
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
  e₁ :⊸♭: (s :* e₂) → do
    τ₁ ← checkTypeLang e₁
    τ₂ ← checkTypeLang e₂
    return $ τ₁ :⊸: (s :* τ₂)
  (x :* e₁) :⊸⋆♭: (pσ :* e₂) → do
    τ₁ ← checkTypeLang e₁
    τ₂ ← checkTypeLang e₂
    return $ (x :* τ₁) :⊸⋆: (pσ :* τ₂)
  _ → None

checkRExpLang ∷ TLExp RExp → 𝑂 RExp
checkRExpLang e₀ = siphon e₀ ^$ case extract e₀ of
  VarTE x → return $ VarRE x
  NatTE n → return $ ConstRE $ AddTop $ dbl n
  NNRealTE r → return $ ConstRE $ AddTop r
  MaxTE e₁ e₂ → do
    η₁ ← checkRExpLang e₁
    η₂ ← checkRExpLang e₂
    return $ MaxRE η₁ η₂
  MinTE e₁ e₂ → do
    η₁ ← checkRExpLang e₁
    η₂ ← checkRExpLang e₂
    return $ MinRE η₁ η₂
  PlusTE e₁ e₂ → do
    η₁ ← checkRExpLang e₁
    η₂ ← checkRExpLang e₂
    return $ PlusRE η₁ η₂
  TimesTE e₁ e₂ → do
    η₁ ← checkRExpLang e₁
    η₂ ← checkRExpLang e₂
    return $ TimesRE η₁ η₂
  DivTE e₁ e₂ → do
    η₁ ← checkRExpLang e₁
    η₂ ← checkRExpLang e₂
    return $ DivRE η₁ η₂
  RootTE e → do
    η ← checkRExpLang e
    return $ PowRE (rat 1 / rat 2) η
  LogTE e → do
    η ← checkRExpLang e
    return $ LogRE η
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

checkSens ∷ Sens RExpPre → SM p ()
checkSens (Sens r) = checkKind ℝK r

checkPriv ∷ Pr p' RExpPre → SM p ()
-- multiple cases..
checkPriv _ = undefined

checkKind ∷ Kind → RExpPre → SM p ()
checkKind κ r = do
  κ' ← inferKind r
  when (not $ κ' ⊑ κ) $ error "kind error"

inferKind ∷ RExpPre → SM p Kind
inferKind = \case
  VarRE x → inferKindVar x
  ConstRE Top → return ℝK
  ConstRE (AddTop r)
    | dbl (truncate r) ≡ r → return ℕK
    | otherwise            → return ℝK
  MaxRE e₁ e₂ → do
    κ₁ ← inferKind $ extract e₁
    κ₂ ← inferKind $ extract e₂
    return $ κ₁ ⊔ κ₂
  MinRE e₁ e₂ → do
    κ₁ ← inferKind $ extract e₁
    κ₂ ← inferKind $ extract e₂
    return $ κ₁ ⊔ κ₂
  PlusRE e₁ e₂ → do
    κ₁ ← inferKind $ extract e₁
    κ₂ ← inferKind $ extract e₂
    return $ κ₁ ⊔ κ₂
  TimesRE e₁ e₂ → do
    κ₁ ← inferKind $ extract e₁
    κ₂ ← inferKind $ extract e₂
    return $ κ₁ ⊔ κ₂
  PowRE q e → do
    κ ← inferKind $ extract e
    return $ case ratDen q ≡ 1 of
      True → κ
      False → ℝK
  EfnRE e → do
    void $ inferKind $ extract e
    return ℝK
  LogRE e → do
    void $ inferKind $ extract e
    return ℝK

checkType ∷ ∀ p. (PRIV_C p) ⇒ Type RExp → SM p ()
checkType τA = case τA of
  ℕˢT η → checkKind ℕK $ extract η
  ℝˢT η → checkKind ℝK $ extract η
  ℕT → skip
  ℝT → skip
  𝕀T η → checkKind ℕK $ extract η
  𝔹T → skip
  𝕊T → skip
  SetT τ → checkType τ
  𝕄T _ℓ _c rows me → do
    case rows of
      RexpRT r → do
        checkKind ℕK $ extract r
      StarRT → skip
    case me of
      EmptyME → skip
      VarME x → checkSchemaVar x
      ConsME (τ ∷ Type RExp) (me ∷ MExp RExp) → undefined
      AppendME (me₁ ∷ MExp RExp) (me₂ ∷ MExp RExp) → undefined
      RexpME r τ → do
        checkKind ℕK $ extract r
        checkType τ
  𝔻T τ → checkType τ
  τ₁ :⊕: τ₂ → do
    checkType τ₁
    checkType τ₂
  τ₁ :⊗: τ₂ → do
    checkType τ₁
    checkType τ₂
  τ₁ :&: τ₂ → do
    checkType τ₁
    checkType τ₂
  τ₁ :⊸: (s :* τ₂) → do
    checkType τ₁
    checkType τ₂
    checkSens $ map extract s
  (x :* τ₁) :⊸⋆: (PEnv (pσ ∷ 𝕏 ⇰ Pr p' RExp) :* τ₂) → do
    checkType τ₁
    mapEnvL contextTypeL ( \ γ → (x ↦ map normalizeRNF τ₁) ⩌ γ) $ do
      eachWith pσ $ \ (x' :* p) → do
        void $ inferKindVar x'
        checkPriv $ map extract p
      checkType τ₂
  BoxedT _σ τ → checkType τ -- TODO: get rid of
  VarT x → void $ inferKindVar x
  _ → error $ "checkType error on " ⧺ pprender τA

-- checkTypeP ∷ ∀ p₁ p₂. (PRIV_C p₁) ⇒ (Type RExp ∧ Pr p₂ RExp) → SM p₁ ()
-- checkTypeP (τ :* p) = do
--   checkType τ
--   checkKindP p
--
-- checkKindP :: ∀ p₁ p₂. Pr p₂ RExp → SM p₁ 𝔹
-- checkKindP p = case p of
--   (EDPriv ε δ) → do
--     κ₁ ← inferKind $ extract ε
--     κ₂ ← inferKind $ extract δ
--     return $ and [κ₁ ⊑ ℝK,κ₂ ⊑ ℝK]
--   -- TODO: account for other privacy variants
--   _ → return True

inferSens ∷ ∀ p. (PRIV_C p) ⇒ SExpSource p → SM p (Type RNF)
inferSens eA = case extract eA of
  ℕˢSE n → return $ ℕˢT $ ι n
  ℝˢSE d → return $ ℝˢT $ ι d
  DynSE e → do
    τ ← inferSens e
    case τ of
      ℕˢT _η → return ℕT
      ℝˢT _η → return ℝT
      𝕀T _η → return ℕT
      _ → undefined -- TypeError
  ℕSE _n → return $ ℕT
  ℝSE _d → return $ ℝT
  RealSE e → do
    τ ← inferSens e
    case τ of
      ℕT → return ℝT
      ℕˢT η → return $ ℝˢT η
      _ → undefined -- TypeError
  MaxSE e₁ e₂ → do
    τ₁ ← inferSens e₁
    τ₂ ← inferSens e₂
    case (τ₁,τ₂) of
      (ℕˢT η₁,ℕˢT η₂) → return $ ℕˢT $ η₁ ⊔ η₂
      (ℝˢT η₁,ℝˢT η₂) → return $ ℝˢT $ η₁ ⊔ η₂
      (𝕀T η₁,𝕀T η₂) → return $ 𝕀T $ η₁ ⊔ η₂
      (ℕT,ℕT) → return ℕT
      (ℝT,ℝT) → return ℝT
      (𝔻T ℝT,𝔻T ℝT) → return $ 𝔻T ℝT
      _ → undefined -- TypeError
  MinSE e₁ e₂ → do
    τ₁ ← inferSens e₁
    τ₂ ← inferSens e₂
    case (τ₁,τ₂) of
      (ℕˢT η₁,ℕˢT η₂) → return $ ℕˢT $ η₁ ⊓ η₂
      (ℝˢT η₁,ℝˢT η₂) → return $ ℝˢT $ η₁ ⊓ η₂
      (𝕀T η₁,𝕀T η₂) → return $ 𝕀T $ η₁ ⊓ η₂
      (ℕT,ℕT) → return ℕT
      (ℝT,ℝT) → return ℝT
      (𝔻T ℝT,𝔻T ℝT) → return $ 𝔻T ℝT
      _ → undefined -- TypeError
  PlusSE e₁ e₂ → do
    τ₁ ← inferSens e₁
    τ₂ ← inferSens e₂
    case (τ₁,τ₂) of
      (ℕˢT η₁,ℕˢT η₂) → return $ ℕˢT $ η₁ + η₂
      (ℝˢT η₁,ℝˢT η₂) → return $ ℝˢT $ η₁ + η₂
      (𝕀T η₁,𝕀T η₂) → return $ 𝕀T $ η₁ + η₂
      (ℕT,ℕT) → return ℕT
      (ℝT,ℝT) → return ℝT
      (𝔻T ℝT,𝔻T ℝT) → return $ 𝔻T ℝT
      _ → error $ concat
            [ "Plus error: "
            , pprender $ (τ₁ :* τ₂)
            , "\n"
            , pprender $ ppLineNumbers $ pretty $ annotatedTag eA
            ]

  TimesSE e₁ e₂ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    σ₂ :* τ₂ ← hijack $ inferSens e₂
    case (τ₁,τ₂) of
      (ℕˢT η₁,ℕˢT η₂) → do tell $ σ₁ ⧺ σ₂ ; return $ ℕˢT $ η₁ × η₂
      (ℝˢT η₁,ℝˢT η₂) → do tell $ σ₁ ⧺ σ₂ ; return $ ℝˢT $ η₁ × η₂
      (𝕀T η₁,𝕀T η₂) →   do tell $ σ₁ ⧺ σ₂ ; return $ 𝕀T $ η₁ × η₂
      (ℕˢT η₁,ℕT) → do
        tell $ σ₁ ⧺ ι η₁ ⨵  σ₂
        return ℕT
      (ℕT,ℕˢT η₂) → do
        tell $ ι η₂ ⨵ σ₁ ⧺ σ₂
        return ℕT
      (ℝˢT η₁,ℝT) → do
        tell $ σ₁ ⧺ ι η₁ ⨵ σ₂
        return ℝT
      (ℝT,ℝˢT η₂) → do
        tell $ ι η₂ ⨵ σ₁ ⧺ σ₂
        return ℝT
      (𝕀T η₁,ℕT) → do
        tell $ σ₁ ⧺ ι η₁ ⨵ σ₂
        return ℕT
      (ℕT,𝕀T η₂) → do
        tell $ ι η₂ ⨵ σ₁ ⧺ σ₂
        return ℕT
      (ℕT,ℕT) → do tell $ σ₁ ⧺ σ₂ ; return ℕT
      (ℝT,ℝT) → do tell $ σ₁ ⧺ σ₂ ; return ℝT
      (𝔻T ℝT,𝔻T ℝT) → do tell $ σ₁ ⧺ σ₂ ; return $ 𝔻T ℝT
      _ → error $ "Times error: " ⧺ (pprender $ (τ₁ :* τ₂))
  DivSE e₁ e₂ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    σ₂ :* τ₂ ← hijack $ inferSens e₂
    case (τ₁,τ₂) of
      (ℝˢT η₁,ℝˢT η₂) → do tell $ σ₁ ⧺ σ₂ ; return $ ℝˢT $ η₁ / η₂
      (ℝˢT _η₁,ℝT) → do
        tell $ σ₁ ⧺ top ⨵ σ₂
        return $ ℝT
      (ℝT,ℝˢT η₂) → do
        tell $ ι (one / η₂) ⨵ σ₁ ⧺ σ₂
        return $ ℝT
      (ℝT,ℝT) → do
        tell $ map (Sens ∘ (×) top ∘ truncateRNF ∘ unSens) σ₁
        tell $ map (Sens ∘ (×) top ∘ truncateRNF ∘ unSens) σ₂
        return ℝT
      (𝔻T ℝT,𝔻T ℝT) → do
        tell σ₁
        tell σ₂
        return $ 𝔻T ℝT
      _ → undefined -- TypeError
  RootSE e → do
    σ :* τ ← hijack $ inferSens e
    case τ of
      ℝˢT η → do tell σ ; return $ ℝˢT $ powerRNF (rat 1 / rat 2) η
      ℝT → do tell $ top ⨵ σ ; return ℝT
      𝔻T ℝT → return $ 𝔻T ℝT
      _ → undefined -- TypeError
  LogSE e → do
    σ :* τ ← hijack $ inferSens e
    case τ of
      ℝˢT η → do tell σ ; return $ ℝˢT $ logRNF η
      ℝT → do tell $ top ⨵ σ ; return ℝT
      𝔻T ℝT → return $ 𝔻T ℝT
      _ → undefined -- TypeError
  ModSE e₁ e₂ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    σ₂ :* τ₂ ← hijack $ inferSens e₂
    case (τ₁,τ₂) of
      (ℕˢT _η₁,ℕˢT _η₂) → do tell $ σ₁ ⧺ σ₂ ; return ℕT
      (𝕀T _η₁,𝕀T _η₂)   → do tell $ σ₁ ⧺ σ₂ ; return ℕT
      (ℕˢT η₁,ℕT) → do
        tell $ σ₁ ⧺ ι η₁ ⨵ σ₂
        return ℕT
      (ℕT,ℕˢT η₂) → do
        tell $ ι η₂ ⨵ σ₁ ⧺ σ₂
        return ℕT
      -- TODO: check that this is ok
      (𝕀T η₁,ℕT) → do
        tell $ σ₁ ⧺ ι η₁ ⨵ σ₂
        return $ 𝕀T η₁
      (ℕT,𝕀T η₂) → do
        tell $ ι η₂ ⨵ σ₁ ⧺ σ₂
        return ℕT
      (ℕT,ℕT) → do tell $ top ⨵ σ₁ ⧺ σ₂ ; return ℕT
      _ → error $ "Mod error: " ⧺ (pprender $ (τ₁ :* τ₂)) -- TypeError
  MinusSE e₁ e₂ → do
    τ₁ ← inferSens e₁
    τ₂ ← inferSens e₂
    case (τ₁,τ₂) of
      (ℝˢT _η₁,ℝˢT _η₂) → return ℝT
      (ℕT,ℕT) → return ℕT
      (ℝT,ℝT) → return ℝT
      (𝔻T ℝT,𝔻T ℝT) → return $ 𝔻T ℝT
      _ → error $ "Minus error: " ⧺ (pprender $ (τ₁ :* τ₂)) -- TypeError
  MCreateSE ℓ e₁ e₂ x₁ x₂ e₃ → do
    τ₁ ← inferSens e₁
    τ₂ ← inferSens e₂
    case (τ₁,τ₂) of
      (ℕˢT ηₘ,ℕˢT ηₙ) → do
        σ₃ :* τ₃ ← hijack $ mapEnvL contextTypeL (\ γ → dict [x₁ ↦ 𝕀T ηₘ,x₂ ↦ 𝕀T ηₙ] ⩌ γ) $ inferSens e₃
        let σ₃' = without (pow [x₁,x₂]) σ₃
        tell $ ι (ηₘ × ηₙ) ⨵ σ₃'
        return $ 𝕄T ℓ UClip (RexpRT ηₘ) (RexpME ηₙ τ₃)
      _ → undefined -- TypeError
  -- CSVtoMatrixSE f τ → do
  --   case map normalizeRNF (extract τ) of
  --     (𝕄T _ℓ _c StarRT (RexpME r τ₁')) → return (𝕄T _ℓ _c StarRT (RexpME r τ₁'))
  --     _ → error $ "CSVtoMatrixSE error: " ⧺ (pprender $ (f :* τ)) -- TypeError
  MIndexSE e₁ e₂ e₃ → do
    τ₁ ← inferSens e₁
    τ₂ ← inferSens e₂
    τ₃ ← inferSens e₃
    case (τ₁,τ₂,τ₃) of
      (𝕄T _ℓ _c (RexpRT ηₘ) (RexpME r τ),𝕀T ηₘ',𝕀T ηₙ') | (ηₘ' ≤ ηₘ) ⩓ (ηₙ' ≤ r) → return τ
      -- dataframe etc.
      -- TODO
      -- (𝕄T _ℓ _c (RexpRT _ηₘ) (ConsME τ m), _ηₘ', ℕˢT (dblRNF ηₙ')) → return $ getConsMAt (ConsME τ m) ηₙ'
      (𝕄T _ℓ _c StarRT (RexpME r τ),𝕀T _ηₘ',𝕀T ηₙ') | (ηₙ' ≤ r) → return τ
      -- TODO
      -- (𝕄T _ℓ _c StarRT (ConsME τ m), _ηₘ',ℕˢT (dblRNF ηₙ')) → return $ getConsMAt (ConsME τ m) ηₙ'
      -- had error: duet: ⟨⟨𝕄 [L∞ U|1,n] ℝ,ℕ⟩,ℕ⟩
      _ → error $ "Index error: " ⧺ (pprender $ (τ₁ :* τ₂ :* τ₃)) -- TypeError
  MUpdateSE e₁ e₂ e₃ e₄ → do
    τ₁ ← inferSens e₁
    τ₂ ← inferSens e₂
    τ₃ ← inferSens e₃
    τ₄ ← inferSens e₄
    case (τ₁,τ₂,τ₃,τ₄) of
      -- TODO: why does this check fail for FW?
      (𝕄T ℓ c ηₘ (RexpME r τ),𝕀T _ηₘ',𝕀T ηₙ',τ') | {-(ηₘ' ≤ ηₘ) ⩓ -}(ηₙ' ≤ r) ⩓ (τ ≡ τ') →
                                          return $ 𝕄T ℓ c ηₘ (RexpME r τ)
      _ → error $ "Update error: " ⧺ (pprender $ (τ₁ :* τ₂ :* τ₃ :* τ₄)) -- TypeError
  MRowsSE e → do
    σ :* τ ← hijack $ inferSens e
    case τ of
      𝕄T _ℓ _c (RexpRT ηₘ) _ηₙ → return $ ℕˢT ηₘ
      𝕄T _ℓ _c StarRT _ηₙ → do
        tell σ
        return $ ℕT
      _ → undefined -- TypeSource Error
  MColsSE e → do
    _ :* τ ← hijack $ inferSens e
    case τ of
      𝕄T _ℓ _c _ηₘ (RexpME r _τ') → return $ ℕˢT r
      _ → undefined -- TypeSource Error
  MClipSE ℓ e → do
    τ ← inferSens e
    case τ of
      𝕄T ℓ' _c ηₘ (RexpME r τ') | τ' ≡ (𝔻T ℝT) → return $ 𝕄T ℓ' (NormClip ℓ) ηₘ (RexpME r τ')
      𝕄T ℓ' _c ηₘ (RexpME r τ') | τ' ≡ (ℝT) → return $ 𝕄T ℓ' (NormClip ℓ) ηₘ (RexpME r (𝔻T ℝT))
      _ → undefined -- TypeSource Error
  MConvertSE e → do
    τ ← inferSens e
    case τ of
      𝕄T _ℓ (NormClip ℓ) ηₘ (RexpME r τ') | τ' ≡ 𝔻T ℝT → return $ 𝕄T ℓ UClip ηₘ (RexpME r ℝT)
      --QUESTION: is this ok? - CA
      -- 𝕄T ℓ _c ηₘ (RexpME r τ') | τ' ≡ 𝔻T ℝT → return $ 𝕄T ℓ UClip ηₘ (RexpME r ℝT)
      _ → error $ "MConvert error: " ⧺ (pprender τ)
  MLipGradSE _g e₁ e₂ e₃ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    tell $ top ⨵ σ₁
    σ₂ :* τ₂ ← hijack $ inferSens e₂
    σ₃ :* τ₃ ← hijack $ inferSens e₃
    case (τ₁,τ₂,τ₃) of
      -- _ → error "TODO"
      (𝕄T _ℓ₁ _c₁ ( RexpRT rₘ₁ ) (RexpME r₁ τ₁'),𝕄T _ℓ₂ (NormClip ℓ) ( RexpRT rₘ₂ ) (RexpME r₂ τ₂'),𝕄T _ℓ₃ _c₃ ( RexpRT rₘ₃ ) (RexpME r₃ τ₃'))
        | meets
          [ τ₁' ≡ ℝT
          , τ₂' ≡ 𝔻T ℝT
          , τ₃' ≡ 𝔻T ℝT
          , rₘ₁ ≡ one
          , r₃ ≡ one
          , r₁ ≡ r₂
          , rₘ₂ ≡ rₘ₃
          ]
        → do tell $ ι (ι 1 / rₘ₂) ⨵ (σ₂ ⧺ σ₃)
             return $ 𝕄T ℓ UClip (RexpRT one) (RexpME r₁ ℝT)
      _ → error $ "Lipschitz grad error: " ⧺ (pprender (τ₁ :* τ₂ :* τ₃))
  MUnbGradSE _g e₁ e₂ e₃ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    tell $ top ⨵ σ₁
    σ₂ :* τ₂ ← hijack $ inferSens e₂
    σ₃ :* τ₃ ← hijack $ inferSens e₃
    case (τ₁,τ₂,τ₃) of
      -- _ → error "TODO"
      (𝕄T _ℓ₁ _c₁ ( RexpRT rₘ₁ ) (RexpME r₁ τ₁'),𝕄T _ℓ₂ _c₂ ( RexpRT rₘ₂ ) (RexpME r₂ τ₂'),𝕄T _ℓ₃ _c₃ ( RexpRT rₘ₃ ) (RexpME r₃ τ₃'))
        | meets
          [ τ₁' ≡ ℝT
          , τ₂' ≡ 𝔻T ℝT
          , τ₃' ≡ 𝔻T ℝT
          , rₘ₁ ≡ one
          , r₃ ≡ one
          , r₁ ≡ r₂
          , rₘ₂ ≡ rₘ₃
          ]
        → do tell $ ι (ι 1 / rₘ₂) ⨵ (σ₂ ⧺ σ₃)
             return $ 𝕄T LInf UClip (RexpRT one) (RexpME r₁ $ 𝔻T ℝT)
      _ → undefined -- TypeSource Error
  MMapSE e₁ x e₂ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    case τ₁ of
      𝕄T ℓ _c (RexpRT ηₘ) (RexpME r τ₁') → do
        σ₂ :* τ₂ ← hijack $ mapEnvL contextTypeL (\ γ → (x ↦ τ₁') ⩌ γ) $ inferSens e₂
        let (ς :* σ₂') = ifNone (zero :* σ₂) $ dview x σ₂
        tell $ ς ⨵ σ₁
        tell $ ι (ηₘ × r) ⨵ σ₂'
        return $ 𝕄T ℓ UClip (RexpRT ηₘ) (RexpME r τ₂)
      _  → undefined -- TypeSource Error
  MTimesSE e₁ e₂ → do
    τ₁ ← inferSens e₁
    τ₂ ← inferSens e₂
    case (τ₁,τ₂) of
      (𝕄T ℓ c (RexpRT η₁) (RexpME r₁ τ₁'),𝕄T _ _ (RexpRT η₂) (RexpME r₂ τ₂'))
        | (τ₁' ≡ τ₂') ⩓ (r₁ ≡ η₂) → do
          return $ 𝕄T ℓ c (RexpRT η₁) (RexpME r₂ τ₁')
      _  → error $ "matrix multiplication error"
  MTransposeSE e₁ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    case τ₁ of
      𝕄T ℓ _c (RexpRT η₁) (RexpME r₁ τ₁') → do
        tell $ ι η₁ ⨵ σ₁
        return $ 𝕄T ℓ UClip (RexpRT r₁) (RexpME η₁ τ₁')
      𝕄T L1 _c (RexpRT η₁) (RexpME r₁ τ₁') → do
        tell $ σ₁
        return $ 𝕄T L1 UClip (RexpRT r₁) (RexpME η₁ τ₁')
      _  → error $ "matrix transpose error"
  -- TODO: QUESTION: how to patten match on nats in rnf
  -- JoinSE e₁ e₂ e₃ e₄ → do
  --   τ₁ ← inferSens e₁
  --   τ₂ ← inferSens e₂
  --   τ₃ ← inferSens e₃
  --   τ₄ ← inferSens e₄
  --   case (τ₁,τ₂,τ₃,τ₄) of
  --     (𝕄T _ _ _ me₁, ℕˢT (dblRNF η₁),𝕄T _ _ _ me₂, ℕˢT (dblRNF η₂))
  --       | (getConsMAt me₁ η₁) ≡ (getConsMAt me₂ η₂) → do
  --         return $ 𝕄T LInf UClip StarRT (joinConsMs me₁ me₂)
  --     _  → error $ "join₁ failed" ⧺ (pprender $ (τ₁ :* τ₂ :* τ₃ :* τ₄))
  BMapSE e₁ x e₂ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    case τ₁ of
      BagT ℓ _c τ₁' → do
        σ₂ :* τ₂ ← hijack $ mapEnvL contextTypeL (\ γ → (x ↦ τ₁') ⩌ γ) $ inferSens e₂
        let (ς :* σ₂') = ifNone (zero :* σ₂) $ dview x σ₂
        tell $ ς ⨵ σ₁
        tell $ σ₂'
        return $ BagT ℓ UClip τ₂
      _  → undefined -- TypeSource Error
  MMap2SE e₁ e₂ x₁ x₂ e₃ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    σ₂ :* τ₂ ← hijack $ inferSens e₂
    case (τ₁,τ₂) of
      (𝕄T ℓ₁ _c₁ (RexpRT r₁) (RexpME r₂ τ₁'),𝕄T ℓ₂ _c₂ (RexpRT r₁') (RexpME r₂' τ₂'))
        | meets
          [ ℓ₁ ≡ ℓ₂
          , r₁ ≡ r₁'
          , r₂ ≡ r₂'
          , τ₁' ≡ τ₂'
          ]
        → do σ₃ :* τ₃ ←
               hijack $
               mapEnvL contextTypeL (\ γ → dict [x₁ ↦ τ₁',x₂ ↦ τ₂'] ⩌ γ) $
               inferSens e₃
             let (ς₁ :* σ₃') = ifNone (zero :* σ₃) $ dview x₁ σ₃
                 (ς₂ :* σ₃'') = ifNone (zero :* σ₃') $ dview x₂ σ₃'
             tell $ ς₁ ⨵ σ₁
             tell $ ς₂ ⨵ σ₂
             tell $ ι (r₁ × r₂) ⨵ σ₃''
             return $ 𝕄T ℓ₁ UClip (RexpRT r₁) (RexpME r₂ τ₃)
      _ → error $ "Map2 error: " ⧺ (pprender $ (τ₁ :* τ₂))
  BMap2SE e₁ e₂ x₁ x₂ e₃ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    σ₂ :* τ₂ ← hijack $ inferSens e₂
    case (τ₁,τ₂) of
      (BagT ℓ₁ _c₁ τ₁',BagT ℓ₂ _c₂ τ₂')
        | ℓ₁ ≡ ℓ₂
        → do σ₃ :* τ₃ ←
               hijack $
               mapEnvL contextTypeL (\ γ → dict [x₁ ↦ τ₁',x₂ ↦ τ₂'] ⩌ γ) $
               inferSens e₃
             let (ς₁ :* σ₃') = ifNone (zero :* σ₃) $ dview x₁ σ₃
                 (ς₂ :* σ₃'') = ifNone (zero :* σ₃') $ dview x₂ σ₃'
             tell $ ς₁ ⨵ σ₁
             tell $ ς₂ ⨵ σ₂
             tell $ σ₃''
             return $ BagT ℓ₁ UClip τ₃
      _ → error $ "Map2 error: " ⧺ (pprender $ (τ₁ :* τ₂))
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
        tell (x ↦ ι 1.0)
        return τ
  LetSE x e₁ e₂ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    σ₂ :* τ₂ ← hijack $ mapEnvL contextTypeL (\ γ → (x ↦ τ₁) ⩌ γ) $ inferSens e₂
    let (ς :* σ₂') = ifNone (zero :* σ₂) $ dview x σ₂
    -- let fvs = freeBvs τ₂
    -- let isClosed = (fvs ∩ single𝑃 x) ≡ pø
    -- case isClosed of
    --   False → error $ "Let type/scoping error in return expression of type: " ⧺ (pprender τ₂)
    --   True → do
    do
        tell $ ς ⨵ σ₁
        tell σ₂'
        return τ₂
  SFunSE x τ e → do
    -- mapEnvL contextKindL (\ δ → assoc ακs ⩌ δ) $ do
      checkType $ extract τ
      let τ' = map normalizeRNF $ extract τ
      σ :* τ'' ← hijack $ mapEnvL contextTypeL (\ γ → (x ↦ τ') ⩌ γ) $ inferSens e
      let (ς :* σ') = ifNone (zero :* σ) $ dview x σ
      -- let fvs = freeBvs τ''
      -- let isClosed = (fvs ∩ single𝑃 x) ≡ pø
      -- case isClosed of
      --   False → error $ "Lambda type/scoping error in return expression of type: " ⧺ (pprender τ'')
      --   True → do
      do
          tell σ'
          return $ τ' :⊸: (ς :* τ'')
  -- DiscFSE e₁ → do
  --   τ₁ ← inferSens e₁
  --   case τ₁ of
  --     (ακs :* τ') :⊸: (_ς :* ℝT) → return $ (ακs :* τ') :⊸: (one :* 𝔻T ℝT)
  AppSE e₁ e₂ → do
    τ₁ ← inferSens e₁
    σ₂ :* τ₂ ← hijack $ inferSens e₂
    case τ₁ of
      τ₁₁ :⊸: (s :* τ₁₂) | τ₁₁ ≡ τ₂ → do
        tell $ s ⨵ σ₂
        return τ₁₂
  PFunSE x τ e → do
    checkType $ extract τ
    let τ' = map normalizeRNF $ extract τ
    σ :* τ'' ← smFromPM $ hijack $ mapEnvL contextTypeL (\ γ → (x ↦ τ') ⩌ γ) $ inferPriv e
    return $ (x :* τ') :⊸⋆: (PEnv σ :* τ'')
    -- let (ς :* σ') = ifNone (zero :* σ) $ dview x σ
    -- let xτs' = map (mapSnd (map normalizeRNF ∘ extract)) xτs
    --     xs = map fst xτs
    -- mapEnvL contextKindL (\ δ → assoc ακs ⩌ δ) $ do
    --   σ :* τ ←
    --     smFromPM
    --     $ hijack
    --     $ mapEnvL contextTypeL (\ γ → assoc xτs' ⩌ γ)
    --     $ inferPriv e
    --   each checkType $ map (extract ∘ snd) xτs
    --   -- let fvs = freeBvs τ
    --   -- let isClosed = (fvs ∩ pow xs) ≡ pø
    --   -- case isClosed of
    --   --   False → error $ "Lambda type/scoping error in return expression of type: " ⧺ (pprender τ)
    --   --   True → do
    --   do
    --       -- TODO: make a name for: Sens ∘ (×) top ∘ truncateRNF ∘ indicatorPr ∘ unPriv
    --       tell $ map (Sens ∘ (×) top ∘ truncateRNF ∘ indicatorPr) $ without (pow xs) σ
    --       let pσ = dict $ mapOn xτs' $ \ (x :* _) → x ↦ ifNone null (σ ⋕? x)
    --       return $ (ακs :* mapp (map normalizeRNF ∘ extract) xτs) :⊸⋆: (PEnv pσ :* τ)
  SetSE es → do
    -- homogeneity check
    l ← mapM (hijack ∘ inferSens) es
    let hm = 1 ≡ (count $ uniques $ map snd l)
    case hm of
      False → error "Set expression is not homogenous/unique"
      True → do
        case es of
          (x :& _xs) → do
            τ ← inferSens x
            return $ SetT τ
          _ → error $ "typing error in SetSE"
  UnionAllSE e → do
    τ ← inferSens e
    case τ of
      (SetT (SetT τ')) → return (SetT τ')
      _ → error $ "UnionAllSE expected a set of sets as its argument" ⧺ pprender τ
  MemberSE e₁ e₂ → do
    τ₁ ← inferSens e₁
    τ₂ ← inferSens e₂
    case (τ₁,τ₂) of
      (τ₁', SetT τ₂') | τ₁' ≡ τ₂' → return 𝔹T
      _ → error $ "MemberSE error: " ⧺ (pprender (τ₁, τ₂))
  TupSE e₁ e₂ → do
    τ₁ ← inferSens e₁
    τ₂ ← inferSens e₂
    return $ τ₁ :⊗: τ₂
  UntupSE x₁ x₂ e₁ e₂ → do
    σ₁ :* τₜ ← hijack $ inferSens e₁
    case τₜ of
      (τ₁ :⊗: τ₂) → do
        σ₂ :* τ₃ ← hijack $ mapEnvL contextTypeL (\ γ → (x₁ ↦ τ₁) ⩌ (x₂ ↦ τ₂) ⩌ γ) $ inferSens e₂
        let (ς₁ :* σ₂') = ifNone (zero :* σ₂) $ dview x₁ σ₂
            (ς₂ :* σ₂'') = ifNone (zero :* σ₂') $ dview x₂ σ₂'
        tell $ (ς₁ ⊔ ς₂) ⨵ σ₁
        tell σ₂''
        return τ₃
      _ → error $ "Untup error: " ⧺ (pprender $ τₜ)
  IdxSE e → do
    σ :* τ ← hijack $ inferSens e
    case τ of
      ℕˢT η → do tell σ ; return $ 𝕀T η
      _ → undefined -- TypeError
  RecordColSE a₁ e → do
    τ ← inferSens e
    case τ of
      RecordT as → do
        -- TODO: I (Joe) am not a wizard at this
        let f ∷ (𝕊 ∧ Type RNF) → 𝑂 (Type RNF) → 𝑂 (Type RNF) = \ p acc →
               case p of
                 (a₂ :* v) | a₁ ≡ a₂ → Some v
                 _ → acc
            τₐ ∷ 𝑂 (Type RNF) = fold None f as
        case τₐ of
          Some τ' → return τ'
          _ → error $ "RecordColSE attribute not found: " ⧺ (pprender (τ, τₐ))
      _ → error $ "RecordColSE error: " ⧺ (pprender τ)
  EqualsSE e₁ e₂ → do
    τ₁ ← inferSens e₁
    τ₂ ← inferSens e₂
    case τ₁ ≡ τ₂ of
      True → return 𝔹T
      _ → error $ "Equals error: " ⧺ (pprender (τ₁, τ₂))
  TrueSE → return 𝔹T
  FalseSE → return 𝔹T
  DFPartitionSE e₁ a e₂ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    τ₂ ← inferSens e₂
    -- TODO: check that τ₁ and τ₂ overlap on some subset of their schemas
    case (τ₁, τ₂) of
      (BagT ℓ c (RecordT as), SetT τ₃) → do
        -- TODO: helper?
        let f ∷ (𝕊 ∧ Type RNF) → 𝑂 (Type RNF) → 𝑂 (Type RNF) = \ p acc →
               case p of
                 (a₂ :* v) | a ≡ a₂ → Some v
                 _ → acc
            τₐ ∷ 𝑂 (Type RNF) = fold None f as
        case τₐ of
          Some τ' → do
            case τ' ≡ τ₃ of
              False → error $ "Partition attribute type mismatch: " ⧺ (pprender (τ₁, τ₃))
              True → do
                tell σ₁
                -- TODO: make sure ℓ and c are right
                return $ BagT ℓ c τ₁
          _ → error $ "Partition attribute not found: " ⧺ (pprender (τ₁, τₐ))
      _ → error $ "Partition error: " ⧺ (pprender (τ₁, τ₂))
  BoxSE e → do
    σ :* τ ← hijack $ inferSens e
    return (BoxedT σ τ)
  UnboxSE e → do
    τ₁ ← inferSens e
    case τ₁ of
      BoxedT σ τ₂ → do
        tell σ
        return τ₂
      _ → error $ "Cannot unbox type: " ⧺ (pprender τ₁)
  ClipSE e → do
    σ :* τ ← hijack $ inferSens e
    case τ of
      𝔻T τ₁ → do
        tell σ
        return τ₁
      _ → error $ "Cannot clip type: " ⧺ (pprender τ)
  ConvSE e → do
    σ :* τ ← hijack $ inferSens e
    case τ of
      𝔻T τ₁ → do
        tell $ map (Sens ∘ (×) top ∘ truncateRNF ∘ unSens) σ
        return τ₁
      _ → error $ "Cannot conv type: " ⧺ (pprender τ)
  DiscSE e → do
    σ :* τ ← hijack $ inferSens e
    tell $ map (Sens ∘ truncateRNF ∘ unSens) σ
    return $ 𝔻T τ
  CountSE e → do
    τ ← inferSens e
    case τ of
      𝕄T ℓ c (RexpRT ηₘ) (RexpME r τ₁') → do
        return $ ℝT
  LoopSE e₂ e₃ x₁ x₂ e₄ → do
    τ₂ ← inferSens e₂
    τ₃ ← inferSens e₃
    σ₄ :* τ₄ ← hijack $ mapEnvL contextTypeL (\ γ → dict [x₁ ↦ ℕT,x₂ ↦ τ₃] ⩌ γ) $ inferSens e₄
    let σ₄' = without (pow [x₁,x₂]) σ₄
    case τ₂ of
      ℕˢT ηₙ | τ₄ ≡ τ₃ → do
        -- tell $ map (Sens ∘ truncate Inf ∘ unSens) σ₄ -- wrong - want to multiply by ηₙ
        tell $ (Sens ηₙ) ⨵ σ₄'
        return τ₃
      _ → error $ concat
            [ "Loop error: "
            , (pprender $ (τ₂ :* τ₃ :* τ₄ :* σ₄))
            , "\n"
            , pprender $ ppLineNumbers $ pretty $ annotatedTag eA
            ]

  MZipSE e₁ e₂ → do
    τ₁ ← inferSens e₁
    τ₂ ← inferSens e₂
    case (τ₁, τ₂) of
      (𝕄T ℓ₁ c₁ r₁ s₁, 𝕄T ℓ₂ c₂ r₂ s₂) | r₁ ≡ r₂ → do
        let m₁ = 𝕄T ℓ₁ c₁ (RexpRT one) s₁
            m₂ = 𝕄T ℓ₂ c₂ (RexpRT one) s₂
        return $ 𝕄T LInf UClip r₁ $ ConsME (m₁ :⊗: m₂) EmptyME
      _ → error $ concat
            [ "Zip error: "
            , (pprender $ (τ₁ :* τ₂))
            , "\n"
            , pprender $ ppLineNumbers $ pretty $ annotatedTag eA
            ]

  Chunks2SE e₁ e₂ e₃ → do
    τ₁ ← inferSens e₁
    τ₂ ← inferSens e₂
    τ₃ ← inferSens e₃
    case (τ₁, τ₂, τ₃) of
      (ℕˢT ηb, 𝕄T ℓ₁ c₁ r₁₁ s₁, 𝕄T ℓ₂ c₂ r₁₂ s₂) | r₁₁ ≡ r₁₂ → do
        let mt₁ = 𝕄T ℓ₁ c₁ (RexpRT ηb) s₁
            mt₂ = 𝕄T ℓ₂ c₂ (RexpRT ηb) s₂
            s   = ConsME (mt₁ :⊗: mt₂) EmptyME
        return $ 𝕄T LInf UClip (RexpRT ηb) s -- TODO: ηb is wrong here, but doesn't affect sens.
      _ → error $ concat
            [ "Chunks error: "
            , (pprender $ (τ₁ :* τ₂ :* τ₃))
            , "\n"
            , pprender $ ppLineNumbers $ pretty $ annotatedTag eA
            ]

  ChunksSE e₁ e₂ → do
    τ₁ ← inferSens e₁
    τ₂ ← inferSens e₂
    case (τ₁, τ₂) of
      (ℕˢT ηb, 𝕄T ℓ₁ c₁ r₁₁ s₁) → do
        let mt₁ = 𝕄T ℓ₁ c₁ (RexpRT ηb) s₁
            s   = ConsME (mt₁) EmptyME
        return $ 𝕄T LInf UClip (RexpRT ηb) s -- TODO: ηb is wrong here, but doesn't affect sens.
      _ → error $ concat
            [ "Chunks error: "
            , (pprender $ (τ₁ :* τ₂))
            , "\n"
            , pprender $ ppLineNumbers $ pretty $ annotatedTag eA
            ]

  MFilterSE e₁ x e₂ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    case τ₁ of
      𝕄T ℓ c r s → do
        let m = 𝕄T ℓ c (RexpRT one) s
        σ₂ :* τ₂ ← hijack $ mapEnvL contextTypeL (\ γ → (x ↦ m) ⩌ γ) $ inferSens e₂
        let (ς :* σ₂') = ifNone (zero :* σ₂) $ dview x σ₂
        tell $ ς ⨵ σ₁
        tell $ map (Sens ∘ (×) top ∘ truncateRNF ∘ unSens) σ₂'
        case τ₂ of
          𝔹T → return $ 𝕄T ℓ c StarRT s
          _  → error $ "MFilter error: " ⧺ (pprender (τ₁, τ₂))
      _ → error $ concat
            [ "MFilter error: "
            , (pprender $ (τ₁))
            , "\n"
            , pprender $ ppLineNumbers $ pretty $ annotatedTag eA
            ]

  MMapColSE e₁ x e₂ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    case τ₁ of
      𝕄T ℓ c (RexpRT ηₘ) (RexpME r τ₁') → do
        let m = 𝕄T ℓ c (RexpRT ηₘ) (RexpME one τ₁')
        σ₂ :* τ₂ ← hijack $ mapEnvL contextTypeL (\ γ → (x ↦ m) ⩌ γ) $ inferSens e₂
        let (ς :* σ₂') = ifNone (zero :* σ₂) $ dview x σ₂
        tell $ (ι r × ς) ⨵ σ₁
        tell $ ι (ηₘ × r) ⨵ σ₂'
        case τ₂ of
          𝕄T ℓ₂ c₂ (RexpRT ηₘ₂) (RexpME one τ₂') →
            return $ 𝕄T ℓ₂ c₂ (RexpRT ηₘ₂) (RexpME r τ₂')
          _ → return $ 𝕄T LInf UClip (RexpRT one) (RexpME r τ₂)
--          _ → error $ pprender τ₂
      _  → undefined -- TypeSource Error

  MMapCol2SE e₁ e₂ x₁ x₂ e₃ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    σ₂ :* τ₂ ← hijack $ inferSens e₂
    case (τ₁, τ₂) of
      (𝕄T ℓ₁ c₁ (RexpRT ηₘ₁) (RexpME r τ₁'), 𝕄T ℓ₂ c₂ (RexpRT ηₘ₂) (RexpME r₂ τ₂'))
       | (r ≡ r₂) → do
        let m₁ = 𝕄T ℓ₁ c₁ (RexpRT ηₘ₁) (RexpME one τ₁')
        let m₂ = 𝕄T ℓ₁ c₁ (RexpRT ηₘ₂) (RexpME one τ₂')
        σ₃ :* τ₃ ← hijack $ mapEnvL contextTypeL (\ γ → dict [x₁ ↦ m₁,x₂ ↦ m₂] ⩌ γ) $ inferSens e₃
        let (ς₁ :* σ₃')  = ifNone (zero :* σ₃)  $ dview x₁ σ₃
        let (ς₂ :* σ₃'') = ifNone (zero :* σ₃') $ dview x₂ σ₃'
        case ℓ₁ of
          LInf → tell $ ς₁ ⨵ σ₁
          _ → tell $ (ι r × ς₁) ⨵ σ₁
        case ℓ₂ of
          LInf → tell $ ς₂ ⨵ σ₂
          _ → tell $ (ι r × ς₂) ⨵ σ₂
        tell $ (ι r × ς₂) ⨵ σ₂
        tell $ ι r ⨵ σ₃''
        case τ₃ of
          𝕄T ℓ₃ c₃ (RexpRT ηₘ₃) (RexpME one τ₃') →
            return $ 𝕄T ℓ₃ c₃ (RexpRT ηₘ₃) (RexpME r τ₃')
          _ → return $ 𝕄T LInf UClip (RexpRT one) (RexpME r τ₃)
      _  → undefined -- TypeSource Error


  MFoldSE e₁ e₂ x₁ x₂ e₃ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    σ₂ :* τ₂ ← hijack $ inferSens e₂
    case τ₂ of
      𝕄T ℓ c (RexpRT r₁) s → do
        let τᵢ = 𝕄T ℓ c (RexpRT one) s
        σ₃ :* τ₃ ← hijack $ mapEnvL contextTypeL (\ γ → dict [x₁ ↦ τ₁,x₂ ↦ τᵢ] ⩌ γ) $
                     inferSens e₃
        let (_ :* σ₃')  = ifNone (zero :* σ₃)  $ dview x₁ σ₃
            (ς₂ :* σ₃'') = ifNone (zero :* σ₃') $ dview x₂ σ₃'
        tell $ map (Sens ∘ (×) top ∘ truncateRNF ∘  unSens) σ₁
        tell $ ς₂ ⨵ σ₂
        tell $ ι r₁ ⨵ σ₃''
        return τ₃
      _ → error $ concat
            [ "MFold error: "
            , (pprender $ (τ₁ :* τ₂))
            , "\n"
            , pprender $ ppLineNumbers $ pretty $ annotatedTag eA
            ]

  MMapRowSE e₁ x e₂ → do
    σ₁ :* τ₁ ← hijack $ inferSens e₁
    case τ₁ of
      𝕄T ℓ c (RexpRT ηₘ) (RexpME r τ₁') → do
        let m = 𝕄T ℓ c (RexpRT one) (RexpME r τ₁')
        σ₂ :* τ₂ ← hijack $ mapEnvL contextTypeL (\ γ → (x ↦ m) ⩌ γ) $ inferSens e₂
        let (ς :* σ₂') = ifNone (zero :* σ₂) $ dview x σ₂
        tell $ ς ⨵ σ₁
        tell $ ι r ⨵ σ₂'
        case τ₂ of
          𝕄T ℓ₂ c₂ (RexpRT ηₘ₂) (RexpME ηₙ₂ τ₂') | (ηₘ₂ ≡ one) ⩓ (ηₙ₂ ≡ r) →
            return $ 𝕄T ℓ₂ c₂ (RexpRT ηₘ) (RexpME r τ₂')
          _ → return $ 𝕄T LInf UClip (RexpRT ηₘ) (RexpME one τ₂)
      _  → undefined -- TypeSource Error


  _ → error $ concat
        [ "inferSens unknown expression type: "
        , "\n"
        , pprender $ ppLineNumbers $ pretty $ annotatedTag eA
        ]

isRealMExp ∷ MExp RNF → PM p 𝔹
isRealMExp me = case me of
  EmptyME → do
    return False
  VarME x → do
    ᴍ ← askL contextMExpL
    case ᴍ ⋕? x of
      None → error $ fromString (show x) -- TypeSource Error
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

-- TODO: define and use these in place of truncate

-- truncateSS ∷ Sens r → Sens r → Sens r
-- truncateSS = undefined
--
-- truncatePP ∷ Priv p r → Priv p r → Priv p r
-- truncatePP = undefined
--
-- truncateSP ∷ Sens r → Priv p r → Priv p r
-- truncateSP = undefined

inferPriv ∷ ∀ p. (PRIV_C p) ⇒ PExpSource p → PM p (Type RNF)
inferPriv eA = case extract eA of
  ReturnPE e → pmFromSM $ inferSens e
  BindPE x e₁ e₂ → do
    τ₁ ← inferPriv e₁
    σ₂ :* τ₂ ← hijack $ mapEnvL contextTypeL (\ γ → (x ↦ τ₁) ⩌ γ) $ inferPriv e₂
    tell $ delete x σ₂
    return τ₂
  -- MMapPE e₁ x e₂ → do
  --   σ₁ :* τ₁ ← pmFromSM $ hijack $ inferSens e₁
  --   case τ₁ of
  --     𝕄T ℓ _c (RexpRT ηₘ) (RexpME r τ₁') | (joins (values σ₁) ⊑ ι 1) → do
  --       σ₂ :* τ₂ ← hijack $ mapEnvL contextTypeL (\ γ → (x ↦ τ₁') ⩌ γ) $ inferPriv e₂
  --       let (p :* σ₂') = ifNone (bot :* σ₂) $ dview x σ₂
  --       tell $ mapp (iteratePr (ηₘ × r)) $ σ₂
  --       case (ιview @ (Pr p RNF) p) of
  --         (Some p') → do
  --           tell $ map (Priv ∘ truncate (iteratePr (ηₘ × r) p') ∘ unSens) σ₁
  --           return $ 𝕄T ℓ UClip (RexpRT ηₘ) (RexpME r τ₂)
  --         _ → do
  --           tell $ map (Priv ∘ truncate Inf ∘ unSens) σ₁
  --           return $ 𝕄T ℓ UClip (RexpRT ηₘ) (RexpME r τ₂)
  --     _  → undefined -- TypeSource Error
  AppPE e₁ e₂ → do
    τ₁ ← pmFromSM $ inferSens e₁
    σ₂ :* τ₂ ← pmFromSM $ hijack $ inferSens e₂
    case τ₁ of
      (x :* τ₁₁) :⊸⋆: (PEnv (σ' ∷ 𝕏 ⇰ Pr p' RNF) :* τ₁₂) | (τ₁₁ ≡ τ₂) ⩓ (joins σ₂ ⊑ one) →
        case eqPRIV (priv @ p) (priv @ p') of
          None → error "not same priv mode"
          Some Refl → do
            let (pₓ :* σ'') = ifNone (zero :* σ') $ dview x σ'
            -- TODO: change iteratePr to something functionally the same but less hacky
            let σ₂' = mapOn σ₂ $ (\ i → iteratePr i pₓ) ∘ truncateRNF ∘ unSens
            tell $ σ₂'
            tell $ σ''
            return τ₁₂
  IfPE e₁ e₂ e₃ → do
    τ₁ ← pmFromSM $ inferSens e₁
    σ₂ :* τ₂ ← hijack $ inferPriv e₂
    σ₃ :* τ₃ ← hijack $ inferPriv e₃
    case (τ₂ ≡ τ₃) of
      False → error $ "IfPE type mismatch" ⧺ (pprender (τ₂,τ₃))
      True → case τ₁ of
        𝔹T → do
          tell (σ₃ ⊔ σ₂)
          return τ₂
        _ → error $ "IfPE expected a boolean in the test position" ⧺ pprender τ₁
  EDLoopPE e₁ e₂ e₃ xs x₁ x₂ e₄ → do
    undefined
    -- GOOD CODE?
    -- let xs' = pow xs
    -- τ₁ ← pmFromSM $ inferSens e₁
    -- τ₂ ← pmFromSM $ inferSens e₂
    -- τ₃ ← pmFromSM $ inferSens e₃
    -- σ₄ :* τ₄ ← hijack $ mapEnvL contextTypeL (\ γ → dict [x₁ ↦ ℕT,x₂ ↦ τ₃] ⩌ γ) $ inferPriv e₄
    -- let σ₄' = without (pow [x₁,x₂]) σ₄
    -- let σ₄Keep = restrict xs' σ₄'
    --     σ₄KeepMax = joins $ values σ₄Keep
    --     σ₄Toss = without xs' σ₄'
    -- case (τ₁,τ₂,σ₄KeepMax) of
    --   (ℝˢT ηᵟ',ℕˢT ηₙ, (EDPriv ηᵋ ηᵟ)) | τ₄ ≡ τ₃ → do
    --     let ε = ι 2 × ηᵋ × root (ι 2 × ηₙ × log (ι 1 / ηᵟ'))
    --         δ = ηᵟ' + ηₙ × ηᵟ
    --     tell $ map (Priv ∘ truncate (EDPriv ε δ) ∘ unPriv) σ₄Keep
    --     tell $ map (Priv ∘ truncate Inf ∘ unPriv) σ₄Toss
    --     return τ₃
    --   _ → error $ "EDloop error: " ⧺ (pprender $ (τ₁ :* τ₂ :* τ₃ :* τ₄ :* σ₄KeepMax :* σ₄Keep))
    --   END GOOD CODE
  -- TODO: push
  -- LoopPE e₂ e₃ xs x₁ x₂ e₄ → do
  --   let xs' = pow xs
  --   τ₂ ← pmFromSM $ inferSens e₂
  --   τ₃ ← pmFromSM $ inferSens e₃
  --   σ₄ :* τ₄ ← hijack $ mapEnvL contextTypeL (\ γ → dict [x₁ ↦ ℕT,x₂ ↦ τ₃] ⩌ γ) $ inferPriv e₄
  --   let σ₄' = without (pow [x₁,x₂]) σ₄
  --   let σ₄Keep = restrict xs' σ₄'
  --       σ₄KeepMax = joins $ values σ₄Keep
  --       σ₄Toss = without xs' σ₄'
  --   case (τ₂,ιview @ (Pr p RNF) σ₄KeepMax) of
  --     (ℕˢT ηₙ,Some p) | τ₄ ≡ τ₃ → do
  --       let p' = iteratePr ηₙ p
  --       tell $ map (Priv ∘ truncate p' ∘ unPriv) σ₄Keep
  --       tell $ map (Priv ∘ truncate Inf ∘ unPriv) σ₄Toss
  --       return τ₃
  --     _ → error $ "EDloop error: " ⧺ (pprender $ (τ₂ :* τ₃ :* τ₄ :* σ₄KeepMax :* σ₄Keep))
  -- GaussPE e₁ (EDGaussParams e₂ e₃) xs e₄ → do
  --   let xs' = pow xs
  --   τ₁ ← pmFromSM $ inferSens e₁
  --   τ₂ ← pmFromSM $ inferSens e₂
  --   τ₃ ← pmFromSM $ inferSens e₃
  --   σ₄ :* τ₄ ← pmFromSM $ hijack $ inferSens e₄
  --   let σ₄Keep = restrict xs' σ₄
  --       σ₄KeepMax = joins $ values σ₄Keep
  --       σ₄Toss = without xs' σ₄
  --   -- TODO: fix this ιview thing as in MGauss
  --   case (τ₁,τ₂,τ₃,τ₄,ιview @ RNF σ₄KeepMax) of
  --     (ℝˢT ηₛ,ℝˢT ηᵋ,ℝˢT ηᵟ,ℝT,Some ς) | ς ⊑ ηₛ → do
  --       tell $ map (Priv ∘ truncate (EDPriv ηᵋ ηᵟ) ∘ unSens) σ₄Keep
  --       tell $ map (Priv ∘ truncate Inf ∘ unSens) σ₄Toss
  --       return ℝT
  --     _ → error $ "Gauss error: " ⧺ (pprender $ (τ₁ :* τ₂ :* τ₃ :* τ₄ :* ιview @ RNF σ₄KeepMax))
  -- LaplacePE e₁ (EpsLaplaceParams e₂) xs e₄ → do
  --   let xs' = pow xs
  --   τ₁ ← pmFromSM $ inferSens e₁
  --   τ₂ ← pmFromSM $ inferSens e₂
  --   σ₄ :* τ₄ ← pmFromSM $ hijack $ inferSens e₄
  --   let σ₄Keep = restrict xs' σ₄
  --       σ₄KeepMax = joins $ values σ₄Keep
  --       σ₄Toss = without xs' σ₄
  --   -- TODO: fix this ιview thing as in MGauss
  --   case (τ₁,τ₂,τ₄,ιview @ RNF σ₄KeepMax) of
  --     (ℝˢT ηₛ,ℝˢT ηᵋ,ℝT,Some ς) | ς ⊑ ηₛ → do
  --       tell $ map (Priv ∘ truncate (EpsPriv ηᵋ) ∘ unSens) σ₄Keep
  --       tell $ map (Priv ∘ truncate Inf ∘ unSens) σ₄Toss
  --       return ℝT
  --     _ → error $ "Laplace error: " ⧺ (pprender $ (τ₁ :* τ₂ :* τ₄ :* ιview @ RNF σ₄KeepMax))
  -- ParallelPE e₀ e₁ x₂ e₂ x₃ x₄ e₃ → do
  --   σ₀ :* τ₀ ← pmFromSM  $ hijack $ inferSens e₀
  --   σ₁ :* τ₁ ← pmFromSM $ hijack $ inferSens e₁
  --   case τ₀ of
  --     (𝕄T ℓ c StarRT me) | joins (values σ₀) ⊑ ι 1 →
  --       case τ₁ of
  --         (SetT τ₁') → do
  --           σ₂ :* τ₂ ← pmFromSM
  --             $ hijack
  --             $ mapEnvL contextTypeL (\ γ → (x₂ ↦ (𝕄T ℓ c (RexpRT (dblRNF 1)) me)) ⩌ γ)
  --             $ inferSens e₂
  --           let σₓ₂ = without (single𝑃 x₂) σ₂
  --           case (τ₁' ≡ τ₂) of
  --             False → error $ "ParallelPE partitioning type mismatch" ⧺ (pprender (τ₁',τ₂))
  --             True | and $ values (map (⊑ (dblRNF 1)) (map unSens σₓ₂)) → do
  --               σ₃ :* τ₃ ← hijack $ mapEnvL contextTypeL (\ γ → (x₃ ↦ τ₁') ⩌ (x₄ ↦ (𝕄T ℓ c StarRT me)) ⩌ γ) $ inferPriv e₃
  --               let σₓ₃ = without (single𝑃 x₃) σ₃
  --               -- p is ⟨ε,δ⟩ in type rule
  --               let p':*σₓ₃₄ = ifNone (bot :* σₓ₃) $ dview x₄ σₓ₃
  --               tell $ map (Priv ∘ truncate Inf ∘ unSens) σ₁
  --               tell $ map (Priv ∘ truncate Inf ∘ unSens) σₓ₂
  --               tell $ map (Priv ∘ truncate Inf ∘ unPriv) σₓ₃₄
  --               tell $ map (Priv ∘ truncate (unPriv p') ∘ unSens) σ₀
  --               return $ (SetT τ₃)
  --             _ → error $ "sensitivity error in ParallelPE"
  --         _ → error $ "℘ expected in second argument of ParallelPE" ⧺ (pprender τ₁)
  --     _ → error $ "𝕄T type expected in first argument of ParallelPE" ⧺ (pprender τ₀)
  -- SVTPE (EDSVTParams e₁) e₂ e₃ xs e₄ → do
  --   let xs' = pow xs
  --   τ₁ ← pmFromSM $ inferSens e₁
  --   τ₂ ← pmFromSM $ inferSens e₂
  --   τ₃ ← pmFromSM $ inferSens e₃
  --   σ₄ :* τ₄ ← pmFromSM $ hijack $ inferSens e₄
  --   let σ₄Keep = restrict xs' σ₄
  --       σ₄KeepMax = joins $ values σ₄Keep
  --       σ₄Toss = without xs' σ₄
  --   case (τ₁, τ₂, τ₃, τ₄) of
  --     (ℝˢT ηᵋ, 𝕄T _ UClip (RexpRT l) (RexpME r₂ ((αs :* τ₅) :⊸: (ηₛ :* ℝT))), ℝT, τ₅')
  --       | (τ₅ ≡ τ₅')
  --       ⩓ (l ≡ one)
----         ⩓ (ηₛ ≡ Sens (Quantity one)) -- TODO: why doesn't this one pass?
  --       → do
  --         tell $ map (Priv ∘ truncate (EDPriv ηᵋ zero) ∘ unSens) σ₄Keep
  --         tell $ map (Priv ∘ truncate Inf ∘ unSens) σ₄Toss
  --         return $ 𝕀T r₂
  --     _ → error $ concat
  --           [ "Sparse Vector Technique error: "
  --           , "\n"
  --           , "τ₁: " ⧺ (pprender τ₁)
  --           , "\n"
  --           , "τ₂: " ⧺ (pprender τ₂)
  --           , "\n"
  --           , "τ₃: " ⧺ (pprender τ₃)
  --           , "\n"
  --           , "τ₄: " ⧺ (pprender τ₄)
  --           , "\n"
  --           , "Sensitivity bound: " ⧺ (pprender $ ιview @ RNF σ₄KeepMax)
  --           , "\n"
  --           , pprender $ ppLineNumbers $ pretty $ annotatedTag eA
  --           ]
  -- SVTPE (EPSSVTParams e₁) e₂ e₃ xs e₄ → do
  --   let xs' = pow xs
  --   τ₁ ← pmFromSM $ inferSens e₁
  --   τ₂ ← pmFromSM $ inferSens e₂
  --   τ₃ ← pmFromSM $ inferSens e₃
  --   σ₄ :* τ₄ ← pmFromSM $ hijack $ inferSens e₄
  --   let σ₄Keep = restrict xs' σ₄
  --       σ₄KeepMax = joins $ values σ₄Keep
  --       σ₄Toss = without xs' σ₄
  --   case (τ₁, τ₂, τ₃, τ₄) of
  --     (ℝˢT ηᵋ, 𝕄T L1 UClip (RexpRT l) (RexpME r₂ ((αs :* τ₅) :⊸: (ηₛ :* ℝT))), ℝT, τ₅')
  --       | (τ₅ ≡ τ₅')
  --       ⩓ (l ≡ one)
----         ⩓ (ηₛ ≡ Sens (Quantity one)) -- TODO: why doesn't this one pass?
  --       → do
  --         tell $ map (Priv ∘ truncate (EpsPriv ηᵋ) ∘ unSens) σ₄Keep
  --         tell $ map (Priv ∘ truncate Inf ∘ unSens) σ₄Toss
  --         return $ 𝕀T r₂
  --     _ → error $ concat
  --           [ "Sparse Vector Technique error: "
  --           , "\n"
  --           , "τ₁: " ⧺ (pprender τ₁)
  --           , "\n"
  --           , "τ₂: " ⧺ (pprender τ₂)
  --           , "\n"
  --           , "τ₃: " ⧺ (pprender τ₃)
  --           , "\n"
  --           , "τ₄: " ⧺ (pprender τ₄)
  --           , "\n"
  --           , "Sensitivity bound: " ⧺ (pprender $ ιview @ RNF σ₄KeepMax)
  --           , "\n"
  --           , pprender $ ppLineNumbers $ pretty $ annotatedTag eA
  --           ]

  -- MGaussPE e₁ (EDGaussParams e₂ e₃) xs e₄ → do
  --   let xs' = pow xs
  --   τ₁ ← pmFromSM $ inferSens e₁
  --   τ₂ ← pmFromSM $ inferSens e₂
  --   τ₃ ← pmFromSM $ inferSens e₃
  --   σ₄ :* τ₄ ← pmFromSM $ hijack $ inferSens e₄
  --   let σ₄Keep = restrict xs' σ₄
  --       σ₄KeepMax = joins $ values σ₄Keep
  --       σ₄Toss = without xs' σ₄
  --   case (τ₁,τ₂,τ₃,τ₄) of
  --     (ℝˢT ηₛ,ℝˢT ηᵋ,ℝˢT ηᵟ,𝕄T ℓ _c ηₘ ηₙ)
  --       | (σ₄KeepMax ⊑ ι ηₛ)
  --       ⩓ (ℓ ≢ LInf)
  --       → do
  --         b ← isRealMExp ηₙ
  --         when (not b) $ throw (error "MGauss error isRealMExp check failed " ∷ TypeError)
  --         tell $ map (Priv ∘ truncate (EDPriv ηᵋ ηᵟ) ∘ unSens) σ₄Keep
  --         tell $ map (Priv ∘ truncate Inf ∘ unSens) σ₄Toss
  --         return $ 𝕄T LInf UClip ηₘ ηₙ
  --     (ℝˢT ηₛ,ℝˢT ηᵋ,ℝˢT ηᵟ,𝕄T ℓ _c ηₘ ηₙ) | (ℓ ≢ LInf) →
  --         error $ concat
  --           [ "MGauss error: "
  --           , "Claimed sensitivity bound (" ⧺ (pprender ηₛ) ⧺ ") is less than actual sensitivity bound (" ⧺ (pprender σ₄KeepMax) ⧺ ")\n"
  --           , "Debug info: "
  --           , pprender $ (τ₁ :* τ₂ :* τ₃ :* τ₄ :* ιview @ RNF σ₄KeepMax)
  --           , pprender σ₄
  --           , "\n"
  --           , pprender $ ppLineNumbers $ pretty $ annotatedTag eA
  --           ]
  --     _ → error $ concat
  --           [ "MGauss error: "
  --           , pprender $ (τ₁ :* τ₂ :* τ₃ :* τ₄ :* ιview @ RNF σ₄KeepMax)
  --           , "\n"
  --           , pprender $ ppLineNumbers $ pretty $ annotatedTag eA
  --           ]
  -- MGaussPE e₁ (ZCGaussParams e₂) xs e₄ → do
  --   let xs' = pow xs
  --   τ₁ ← pmFromSM $ inferSens e₁
  --   τ₂ ← pmFromSM $ inferSens e₂
  --   σ₄ :* τ₄ ← pmFromSM $ hijack $ inferSens e₄
  --   let σ₄Keep = restrict xs' σ₄
  --       σ₄KeepMax = joins $ values σ₄Keep
  --       σ₄Toss = without xs' σ₄
  --   case (τ₁,τ₂,τ₄,ιview @ RNF σ₄KeepMax) of
  --     (ℝˢT ηₛ,ℝˢT ηᵨ,𝕄T L2 _c ηₘ ηₙ,Some ς) | ς ⊑ ηₛ → do
  --       b ← isRealMExp ηₙ
  --       when (not b) $ throw (error "MGauss error isRealMExp check failed" ∷ TypeError)
  --       tell $ map (Priv ∘ truncate (ZCPriv ηᵨ) ∘ unSens) σ₄Keep
  --       tell $ map (Priv ∘ truncate Inf ∘ unSens) σ₄Toss
  --       return $ 𝕄T LInf UClip ηₘ ηₙ
  --     _ → error $ "MGauss error: " ⧺ (pprender $ (τ₁ :* τ₂ :* τ₄ :* ιview @ RNF σ₄KeepMax))
  -- MGaussPE e₁ (RenyiGaussParams e₂ e₃) xs e₄ → do
  --   let xs' = pow xs
  --   τ₁ ← pmFromSM $ inferSens e₁
  --   τ₂ ← pmFromSM $ inferSens e₂
  --   τ₃ ← pmFromSM $ inferSens e₃
  --   σ₄ :* τ₄ ← pmFromSM $ hijack $ inferSens e₄
  --   let σ₄Keep = restrict xs' σ₄
  --       σ₄KeepMax = joins $ values σ₄Keep
  --       σ₄Toss = without xs' σ₄
  --   case (τ₁,τ₂,τ₃,τ₄,ιview @ RNF σ₄KeepMax) of
  --     (ℝˢT ηₛ,ℝˢT ηᵅ,ℝˢT ηᵋ,𝕄T L2 _c ηₘ ηₙ,Some ς) | ς ⊑ ηₛ → do
  --       b ← isRealMExp ηₙ
  --       when (not b) $ throw (error "MGauss error isRealMExp check failed" ∷ TypeError)
  --       tell $ map (Priv ∘ truncate (RenyiPriv ηᵅ ηᵋ) ∘ unSens) σ₄Keep
  --       tell $ map (Priv ∘ truncate Inf ∘ unSens) σ₄Toss
  --       return $ 𝕄T LInf UClip ηₘ ηₙ
  --     _ → error $ "MGauss error: " ⧺ (pprender $ (τ₁ :* τ₂ :* τ₃ :* τ₄ :* ιview @ RNF σ₄KeepMax))
  -- MGaussPE e₁ (TCGaussParams e₂ e₃) xs e₄ → do
  --   let xs' = pow xs
  --   τ₁ ← pmFromSM $ inferSens e₁
  --   τ₂ ← pmFromSM $ inferSens e₂
  --   τ₃ ← pmFromSM $ inferSens e₃
  --   σ₄ :* τ₄ ← pmFromSM $ hijack $ inferSens e₄
  --   let σ₄Keep = restrict xs' σ₄
  --       σ₄KeepMax = joins $ values σ₄Keep
  --       σ₄Toss = without xs' σ₄
  --   case (τ₁,τ₂,τ₃,τ₄,ιview @ RNF σ₄KeepMax) of
  --     (ℝˢT ηₛ,ℝˢT ρ,ℕˢT ω,𝕄T L2 _c ηₘ ηₙ,Some ς) | ς ⊑ ηₛ → do
  --       b ← isRealMExp ηₙ
  --       when (not b) $ throw (error "MGauss error isRealMExp check failed" ∷ TypeError)
  --       tell $ map (Priv ∘ truncate (TCPriv ρ ω) ∘ unSens) σ₄Keep
  --       tell $ map (Priv ∘ truncate Inf ∘ unSens) σ₄Toss
  --       return $ 𝕄T LInf UClip ηₘ ηₙ
  --     _ → error $ "MGauss error: " ⧺ (pprender $ (τ₁ :* τ₂ :* τ₃ :* τ₄ :* ιview @ RNF σ₄KeepMax))
  -- BGaussPE e₁ (EDGaussParams e₂ e₃) xs e₄ → do
  --   let xs' = pow xs
  --   τ₁ ← pmFromSM $ inferSens e₁
  --   τ₂ ← pmFromSM $ inferSens e₂
  --   τ₃ ← pmFromSM $ inferSens e₃
  --   σ₄ :* τ₄ ← pmFromSM $ hijack $ inferSens e₄
  --   let σ₄Keep = restrict xs' σ₄
  --       σ₄KeepMax = joins $ values σ₄Keep
  --       σ₄Toss = without xs' σ₄
  --   case (τ₁,τ₂,τ₃,τ₄,ιview @ RNF σ₄KeepMax) of
  --     -- TODO: do something with ℓ and c
  --     (ℝˢT ηₛ,ℝˢT ηᵋ,ℝˢT ηᵟ,BagT ℓ c ℝT,Some ς) | ς ⊑ ηₛ → do
  --       tell $ map (Priv ∘ truncate (EDPriv ηᵋ ηᵟ) ∘ unSens) σ₄Keep
  --       tell $ map (Priv ∘ truncate Inf ∘ unSens) σ₄Toss
  --       -- TODO: make sure ℓ and c are correct
  --       return $ BagT ℓ c ℝT
  --     _ → error $ "BGauss ED error: " ⧺ (pprender $ (τ₁ :* τ₂ :* τ₃ :* τ₄ :* ιview @ RNF σ₄KeepMax))
  -- BGaussPE e₁ (ZCGaussParams e₂) xs e₄ → do
  --   let xs' = pow xs
  --   τ₁ ← pmFromSM $ inferSens e₁
  --   τ₂ ← pmFromSM $ inferSens e₂
  --   σ₄ :* τ₄ ← pmFromSM $ hijack $ inferSens e₄
  --   let σ₄Keep = restrict xs' σ₄
  --       σ₄KeepMax = joins $ values σ₄Keep
  --       σ₄Toss = without xs' σ₄
  --   case (τ₁,τ₂,τ₄,ιview @ RNF σ₄KeepMax) of
  --     -- TODO: do something with ℓ and c
  --     (ℝˢT ηₛ,ℝˢT ηᵨ,BagT ℓ c ℝT,Some ς) | ς ⊑ ηₛ → do
  --       tell $ map (Priv ∘ truncate (ZCPriv ηᵨ) ∘ unSens) σ₄Keep
  --       tell $ map (Priv ∘ truncate Inf ∘ unSens) σ₄Toss
  --       -- TODO: make sure ℓ and c are correct
  --       return $ BagT ℓ c ℝT
  --     _ → error $ "BGauss error: " ⧺ (pprender $ (τ₁ :* τ₂ :* τ₄ :* ιview @ RNF σ₄KeepMax))
  -- BGaussPE e₁ (RenyiGaussParams e₂ e₃) xs e₄ → do
  --   let xs' = pow xs
  --   τ₁ ← pmFromSM $ inferSens e₁
  --   τ₂ ← pmFromSM $ inferSens e₂
  --   τ₃ ← pmFromSM $ inferSens e₃
  --   σ₄ :* τ₄ ← pmFromSM $ hijack $ inferSens e₄
  --   let σ₄Keep = restrict xs' σ₄
  --       σ₄KeepMax = joins $ values σ₄Keep
  --       σ₄Toss = without xs' σ₄
  --   case (τ₁,τ₂,τ₃,τ₄,ιview @ RNF σ₄KeepMax) of
  --     -- TODO: do something with ℓ and c
  --     (ℝˢT ηₛ,ℝˢT ηᵅ,ℝˢT ηᵋ,BagT ℓ c ℝT,Some ς) | ς ⊑ ηₛ → do
  --       tell $ map (Priv ∘ truncate (RenyiPriv ηᵅ ηᵋ) ∘ unSens) σ₄Keep
  --       tell $ map (Priv ∘ truncate Inf ∘ unSens) σ₄Toss
  --       -- TODO: make sure ℓ and c are correct
  --       return $ BagT ℓ c ℝT
  --     _ → error $ "BGauss error: " ⧺ (pprender $ (τ₁ :* τ₂ :* τ₃ :* τ₄ :* ιview @ RNF σ₄KeepMax))
  -- GaussPE _e₁ (RenyiGaussParams _e₂ _e₃) _xs _e₄ → undefined
  -- GaussPE _e₁ (ZCGaussParams _e₂) _xs _e₃ → undefined
  -- ExponentialPE e₁ (EDExponentialParams e₂) e₃ xs x e₄ → do
  --   let xs' = pow xs
  --   τ₁ ← pmFromSM $ inferSens e₁
  --   τ₂ ← pmFromSM $ inferSens e₂
  --   mat ← pmFromSM $ inferSens e₃
  --   case mat of
  --     𝕄T _ℓ _c (RexpRT r₁) (RexpME r₂ τ₃) → do
  --       σ₄ :* τ₄ ← pmFromSM $ hijack $ mapEnvL contextTypeL (\ γ → (x ↦ τ₃) ⩌ γ) $ inferSens e₄
  --       let σ₄' = delete x σ₄
  --           σ₄Keep = restrict xs' σ₄'
  --           σ₄KeepMax = joins $ values σ₄Keep
  --           σ₄Toss = without xs' σ₄'
  --       case (τ₁,τ₂,ιview @ RNF σ₄KeepMax) of
  --         (ℝˢT ηₛ,ℝˢT ηᵋ,Some ς) | (ς ⊑ ηₛ) ⩓ (τ₄ ≡ ℝT) ⩓ (r₁ ≡ one) → do
  --           tell $ map (Priv ∘ truncate (EDPriv ηᵋ zero) ∘ unSens) σ₄Keep
  --           tell $ map (Priv ∘ truncate Inf ∘ unSens) σ₄Toss
  --           return $ 𝕀T r₂

  --         _ → error $ "Exponential error: " ⧺ (pprender $ (τ₁ :* τ₂ :* τ₃ :* τ₄ :* ιview @ RNF σ₄KeepMax))
  --     _ → error "type error: ExponentialPE"
  -- ConvertZCEDPE e₁ e₂ → do
  --   τ₁ ← pmFromSM $ inferSens e₁
  --   case τ₁ of
  --     ℝˢT ηᵟ → do
  --       mapPPM (onPriv $ map $ convertZCEDPr ηᵟ) $ inferPriv e₂
  --     _ → error "type error: ConvertZCEDPE"
  -- ConvertRENYIEDPE e₁ e₂ → do
  --   τ₁ ← pmFromSM $ inferSens e₁
  --   case τ₁ of
  --     ℝˢT ηᵟ → do
  --       mapPPM (onPriv $ map $ convertRENYIEDPr ηᵟ) $ inferPriv e₂
  --     _ → error "type error: ConvertRENYIEDPE"
  -- ConvertEPSZCPE e₁ → do
  --   mapPPM (onPriv $ map $ convertEPSZCPr) $ inferPriv e₁
  -- EDSamplePE en exs eys xs' ys' e → do
  --   _ :* τn ← pmFromSM $ hijack $ inferSens en -- throw away the cost
  --   σ₁ :* τxs ← pmFromSM $ hijack $ inferSens exs
  --   σ₂ :* τys ← pmFromSM $ hijack $ inferSens eys
  --   -- check that upper bound on each of σ₁ and σ₂ is less than 1
  --   case (τn,τxs,τys) of
  --     (ℕˢT ηrows',𝕄T ℓ₁ c₁ (RexpRT ηrows₁) ς₁,𝕄T ℓ₂ c₂ (RexpRT ηrows₂) ς₂)
  --       | (ηrows₁ ≡ ηrows₂) ⩓ (joins (values σ₁) ⊑ ι 1) ⩓ (joins (values σ₂) ⊑ ι 1) {-⩓ (ηrows' ≤ ηrows₁)-} → do
  --           let τxs' = 𝕄T ℓ₁ c₁ (RexpRT ηrows') ς₁
  --               τys' = 𝕄T ℓ₂ c₂ (RexpRT ηrows') ς₂
  --               sε = ι 2 × ηrows' / ηrows₁
  --               sδ = ηrows' / ηrows₁
  --           σ :* τ ← hijack $ mapEnvL contextTypeL (\ γ → (xs' ↦ τxs') ⩌ (ys' ↦ τys') ⩌ γ) $ inferPriv e
  --           let σxs' = σ ⋕! xs'
  --               σys' = σ ⋕! ys'
  --               σ' = without (pow [xs',ys']) σ
  --           case (σxs',σys') of
  --             ((EDPriv ε₁ δ₁), (EDPriv ε₂ δ₂)) → do
  --               tell $ map (Priv ∘ truncate (EDPriv (ε₁×sε) (δ₁×sδ)) ∘ unSens) σ₁
  --               tell $ map (Priv ∘ truncate (EDPriv (ε₂×sε) (δ₂×sδ)) ∘ unSens) σ₂
  --               tell σ'
  --               return τ
  --             _ → error $ "type error in EDSamplePE." ⧺ (pprender (σxs',σys'))
  --           -- pull out privacies p₁ for xs' p₂ and ys'
  --           -- truncate everything in σ₁ to be p₁ scaled by ⟨sε,sδ⟩
  --           -- truncate everything in σ₂ to be p₂ scaled by ⟨sε,sδ⟩
  --           -- output σ₁, σ₂, and leftovers from σ
  --     _ → error "type error in EDSamplePE"
  -- TCSamplePE en exs eys xs' ys' e → do
  --   _ :* τn ← pmFromSM $ hijack $ inferSens en
  --   σ₁ :* τxs ← pmFromSM $ hijack $ inferSens exs
  --   σ₂ :* τys ← pmFromSM $ hijack $ inferSens eys
  --   case (τn,τxs,τys) of
  --     (ℕˢT ηrows',𝕄T ℓ₁ c₁ (RexpRT ηrows₁) ς₁,𝕄T ℓ₂ c₂ (RexpRT ηrows₂) ς₂)
  --       | (ηrows₁ ≡ ηrows₂) ⩓ (joins (values σ₁) ⊑ ι 1) ⩓ (joins (values σ₂) ⊑ ι 1) → do
  --           let τxs' = 𝕄T ℓ₁ c₁ (RexpRT ηrows') ς₁
  --               τys' = 𝕄T ℓ₂ c₂ (RexpRT ηrows') ς₂
  --               s = ηrows' / ηrows₁
  --           σ :* τ ← hijack $ mapEnvL contextTypeL (\ γ → (xs' ↦ τxs') ⩌ (ys' ↦ τys') ⩌ γ) $ inferPriv e
  --           let σxs' = σ ⋕! xs'
  --               σys' = σ ⋕! ys'
  --               σ' = without (pow [xs',ys']) σ
  --           case (σxs',σys') of
  --             ((TCPriv ρ₁ _ω₁), (TCPriv ρ₂ _ω₂)) → do
  --               tell $ map (Priv ∘ truncate ((TCPriv ((dblRNF 13.0) × s × s × ρ₁) ((log ((dblRNF 1.0)/s)) / ((dblRNF 4.0) × ρ₁)))) ∘ unSens) σ₁
  --               tell $ map (Priv ∘ truncate ((TCPriv ((dblRNF 13.0) × s × s × ρ₂) ((log ((dblRNF 1.0)/s)) / ((dblRNF 4.0) × ρ₂)))) ∘ unSens) σ₂
  --               tell σ'
  --               return τ
  --             _ → error $ "type error in TCSamplePE." ⧺ (pprender (σxs',σys'))
  --     _ → error "type error in TCSamplePE"
  -- RenyiSamplePE en exs eys xs' ys' e → do
  --   _ :* τn ← pmFromSM $ hijack $ inferSens en
  --   σ₁ :* τxs ← pmFromSM $ hijack $ inferSens exs
  --   σ₂ :* τys ← pmFromSM $ hijack $ inferSens eys
  --   case (τn,τxs,τys) of
  --     (ℕˢT ηrows',𝕄T ℓ₁ c₁ (RexpRT ηrows₁) ς₁,𝕄T ℓ₂ c₂ (RexpRT ηrows₂) ς₂)
  --       | (ηrows₁ ≡ ηrows₂) ⩓ (joins (values σ₁) ⊑ ι 1) ⩓ (joins (values σ₂) ⊑ ι 1) → do
  --           let τxs' = 𝕄T ℓ₁ c₁ (RexpRT ηrows') ς₁
  --               τys' = 𝕄T ℓ₂ c₂ (RexpRT ηrows') ς₂
  --               s = ηrows' / ηrows₁
  --           σ :* τ ← hijack $ mapEnvL contextTypeL (\ γ → (xs' ↦ τxs') ⩌ (ys' ↦ τys') ⩌ γ) $ inferPriv e
  --           let σxs' = σ ⋕! xs'
  --               σys' = σ ⋕! ys'
  --               σ' = without (pow [xs',ys']) σ
  --           case (σxs',σys') of
  --             ((RenyiPriv α₁ ϵ₁), (RenyiPriv α₂ ϵ₂)) → do
  --               tell $ map (Priv ∘ truncate (RenyiPriv α₁ (renyiϵ' (dblRNF 2.0) α₁ s ϵ₁)) ∘ unSens) σ₁
  --               tell $ map (Priv ∘ truncate (RenyiPriv α₂ (renyiϵ' (dblRNF 2.0) α₂ s ϵ₂)) ∘ unSens) σ₂
  --               tell σ'
  --               return τ
  --             _ → error $ "type error in RenyiSamplePE." ⧺ (pprender (σxs',σys'))
  --     _ → error "type error in RenyiSamplePE"

  -- TODO: I think this is broken
  -- PFldRowsPE e₁ e₂ e₃ → do
  --   σ₁ :* τ₁ ← pmFromSM $ hijack $ inferSens e₁
  --   σ₂ :* τ₂ ← pmFromSM $ hijack $ inferSens e₂
  --   τ₃ ← pmFromSM $ inferSens e₃
  --   case (τ₁, τ₂) of
  --     ( 𝕄T ℓ₁ c₁ (RexpRT ηr₁) (RexpME ηc₁ (𝔻T ℝT)) :×: 𝕄T ℓ₂ c₂ (RexpRT ηr₂) (RexpME ηc₂ (𝔻T ℝT)),
  --        (αs :* as) :⊸⋆: τ₅ ) -- | τ₁ ≡ τ₅
  --       → error $ pprender (τ₁ :* τ₂)

--   PFldRows2PE e₁ e₂ e₃ e₄ e₅ → do
--     τ₁ ← pmFromSM $ inferSens e₁
--     τ₂ ← pmFromSM $ inferSens e₂
--     σ₃ :* τ₃ ← pmFromSM $ hijack $ inferSens e₃
--     σ₄ :* τ₄ ← pmFromSM $ hijack $ inferSens e₄
--     τ₅ ← pmFromSM $ inferSens e₅
--     case (τ₁, τ₃, τ₄, τ₅) of
--       (ℕˢT ηb,
--        𝕄T ℓ₁ c₁ (RexpRT ηr₁) (RexpME ηc₁ (𝔻T ℝT)),
--        𝕄T ℓ₂ c₂ (RexpRT ηr₂) (RexpME ηc₂ (𝔻T ℝT)),
--        (αs :* as) :⊸⋆: τ₆ ) -- | τ₁ ≡ τ₅
--         → case as of
--             (PArgs ((𝕄T ℓ₁' c₁' (RexpRT ηr₁') (RexpME ηc₁' (𝔻T ℝT)) :* (p₁ ∷ Pr p₁ RNF)) :&
--                     (𝕄T ℓ₂' c₂' (RexpRT ηr₂') (RexpME ηc₂' (𝔻T ℝT)) :* (p₂ ∷ Pr p₂ RNF)) :&
--                     (τ₂prime :* p₃) :& Nil))
--              | (ℓ₁ ≡ ℓ₁') ⩓ (ℓ₂ ≡ ℓ₂') ⩓
--                (c₁ ≡ c₁') ⩓ (c₂ ≡ c₂') ⩓
--                (ηr₁' ≡ ηb) ⩓ (ηc₁ ≡ ηc₁') ⩓
--                (ηr₂' ≡ ηb) ⩓ (ηc₂ ≡ ηc₂')
--               → case (eqPRIV (priv @ p) (priv @ p₁), eqPRIV (priv @ p) (priv @ p₂)) of
--                   (Some Refl, Some Refl) → do
--                     case (p₁,p₂) of
--                       (ED,ED) → do
--                         tell $ map (Priv ∘ truncate (unPriv p₁') ∘ unSens) σ₃
--                         tell $ map (Priv ∘ truncate (unPriv p₂') ∘ unSens) σ₄
--                         return τ₂
--             _ → error $ "Fold error " ⧺ (pprender (τ₃ :* τ₄ :* τ₅))
--
--   PMapColPE e₁ x e₂ → do
--     σ₁ :* τ₁ ← pmFromSM $ hijack $ inferSens e₁
--     case τ₁ of
--       𝕄T LInf UClip (RexpRT ηₘ) (RexpME r (𝔻T τ₁')) -- TODO: this breaks | (joins (values σ₁) ⊑ ι 1)
--        → do
--         let mcol = 𝕄T LInf UClip (RexpRT ηₘ) (RexpME one (𝔻T τ₁'))
--         σ₂ :* τ₂ ← hijack $ mapEnvL contextTypeL (\ γ → (x ↦ mcol) ⩌ γ) $ inferPriv e₂
--         let (p :* σ₂') = ifNone (bot :* σ₂) $ dview x σ₂
--         tell $ mapp (iteratePr (ηₘ × r)) $ (map unPriv σ₂)
--         case (ιview @ (Pr p RNF) p) of
--           (Some p') → do
--             tell $ map (Priv ∘ truncate (iteratePr r p') ∘ unSens) σ₁
--             return $ 𝕄T LInf UClip (RexpRT one) (RexpME r τ₂)
--           _ → do
--             tell $ map (Priv ∘ truncate Inf ∘ unSens) σ₁
--             return $ 𝕄T LInf UClip (RexpRT one) (RexpME r τ₂)
--       _  → undefined -- TypeSource Error

  _ → error $ concat
        [ "inferPriv unknown expression type: "
        , "\n"
        , pprender $ ppLineNumbers $ pretty $ annotatedTag eA
        ]

--  e → error $ fromString $ show e

-- renyiϵ' ∷ RNF → RNF → RNF → RNF → RNF
-- -- TODO
-- renyiϵ' j α s ϵ = (one / (α - one)) × log ((dblRNF 1.0) + (renyiϵ'Σpess j α s ϵ))
--
-- renyiϵ'Σpess ∷ RNF → RNF → RNF → RNF → RNF
-- renyiϵ'Σpess j α s ϵ = α × ((dblRNF 2.0) × (s^α)) × (α^α) × (exp ((α - one) × ϵ))

-- renyiϵ'Σ ∷ RNF → RNF → RNF → RNF → RNF
-- renyiϵ'Σ j α s ϵ = case α < j of
--   True → (dblRNF 0.0)
--   False → (((dblRNF 2.0) × (s^j)) × (choose α j) × (exp ((j - one) × ϵ))) + renyiϵ'Σ (j + (dblRNF 1.0)) α s ϵ
--
-- fac :: RNF → RNF
-- fac (dblRNF 0.0) = (dblRNF 1.0)
-- fac (dblRNF 1.0) = (dblRNF 1.0)
-- fac n = n × (fac (n - one))

-- choose :: RNF → RNF → RNF
-- choose n k = (fac n) / ((fac k) × (fac (n - k)))

-- conv type to tl, subst, back to type
substTL ∷ 𝕏 → TLExp r → TLExp r → TLExp r
substTL x tl₁ tl₂ = case extract tl₂ of
  VarTE x' → case x ≡ x' of
    True → tl₁
    False → siphon tl₁ $ VarTE x'
  -- Type Stuff →
  ℕˢTE r → siphon tl₁ $ ℕˢTE r
  ℝˢTE r → siphon tl₁ $ ℝˢTE r
  ℕTE → siphon tl₁ $ ℕTE
  ℝTE → siphon tl₁ $ ℝTE
  𝕀TE r → siphon tl₁ $ 𝕀TE r
  𝔹TE → siphon tl₁ $ 𝔹TE
  𝕊TE → siphon tl₁ $ 𝕊TE
  SetTE τ → siphon tl₁ $ SetTE $ substTL x tl₁ τ
  --TODO: need substitution here
  𝕄TE ℓ c rows cols → siphon tl₁ $ 𝕄TE ℓ c rows cols
  𝔻TE τ → siphon tl₁ $ 𝔻TE $ substTL x tl₁ τ
  τ₁ :⊕♭: τ₂ → siphon tl₁ $ substTL x tl₁ τ₁ :⊕♭: substTL x tl₁ τ₂
  τ₁ :⊗♭: τ₂ → siphon tl₁ $ substTL x tl₁ τ₁ :⊗♭: substTL x tl₁ τ₂
  τ₁ :&♭: τ₂ → siphon tl₁ $ substTL x tl₁ τ₁ :&♭: substTL x tl₁ τ₂
  -- TODO: sens -> tlexp -> then substTL -> sens
  τ₁ :⊸♭: (s :* τ₂) → siphon tl₁ $ substTL x tl₁ τ₁ :⊸♭: (s :* substTL x tl₁ τ₂)
  (x :* τ₁) :⊸⋆♭: (penv :* τ₂) → siphon tl₁ $ (x :* substTL x tl₁ τ₁) :⊸⋆♭: (penv :* substTL x tl₁ τ₂)
  ForallTE x κ τ → siphon tl₁ $ ForallTE x κ $ substTL x tl₁ τ
   -- RExp Stuff →
  NatTE n → siphon tl₁ $ NatTE n
  NNRealTE d → siphon tl₁ $ NNRealTE d
  MaxTE τ₁ τ₂ → siphon tl₁ $ MaxTE (substTL x tl₁ τ₁) (substTL x tl₁ τ₂)
  MinTE τ₁ τ₂ → siphon tl₁ $ MinTE (substTL x tl₁ τ₁) (substTL x tl₁ τ₂)
  PlusTE τ₁ τ₂ → siphon tl₁ $ PlusTE (substTL x tl₁ τ₁) (substTL x tl₁ τ₂)
  TimesTE τ₁ τ₂ → siphon tl₁ $ TimesTE (substTL x tl₁ τ₁) (substTL x tl₁ τ₂)
  DivTE τ₁ τ₂ → siphon tl₁ $ DivTE (substTL x tl₁ τ₁) (substTL x tl₁ τ₂)
  RootTE τ → siphon tl₁ $ RootTE $ substTL x tl₁ τ
  LogTE τ → siphon tl₁ $ LogTE $ substTL x tl₁ τ
  TopTE → siphon tl₁ $ TopTE
   -- Privacy Stuff →
  PairTE τ₁ τ₂ → siphon tl₁ $ PairTE (substTL x tl₁ τ₁) (substTL x tl₁ τ₂)

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

-- substPrivR ∷ (PRIV_C p) ⇒ 𝑃 𝕏 → 𝕏 → Pr p RNF → 𝑃 𝕏 → Type RNF → Type RNF
-- substPrivR 𝓈 x p' fv = undefined

substSens ∷ 𝕏 → Sens RNF → Type RNF → Type RNF
substSens x s τ = checkTypeLang $ substTL x (sensToTLExp s) (typeToTLExp τ)

-- substSensR ∷ 𝑃 𝕏 → 𝕏 → Sens RNF → 𝑃 𝕏 → Type RNF → Type RNF
-- substSensR 𝓈 x s' fv = undefined

substType ∷ 𝕏 → Type RNF → Type RNF → 𝑂 (Type RNF)
substType x τ₁ τ₂ = checkTypeLang $ substTL x (typeToTLExp τ₁) (typeToTLExp τ₁)

-- substTypeR ∷ 𝑃 𝕏 → 𝕏 → Type RNF → 𝑃 𝕏 → Type RNF → Type RNF
-- substTypeR 𝓈 x r' fv = undefined

substRExp ∷ 𝕏 → RNF → Type RNF → Type RNF
substRExp x r τ = checkTypeLang $ substTL x (rexpToTLExp r) (typeToTLExp τ)

-- substRExp ∷ 𝕏 → RNF → Type RNF → Type RNF
-- substRExp x r τ = substRExpR pø x r (fvRNF r) τ

-- substMExpR ∷ 𝑃 𝕏 → 𝕏 → RNF → 𝑃 𝕏 → MExp RNF → MExp RNF
-- substMExpR 𝓈 x r' fv = \case
--   EmptyME → EmptyME
--   VarME x' → VarME x'
--   ConsME τ me → ConsME (substRExpR 𝓈 x r' fv τ) (substMExpR 𝓈 x r' fv me)
--   AppendME me₁ me₂ → AppendME (substMExpR 𝓈 x r' fv me₁) (substMExpR 𝓈 x r' fv me₂)
--   RexpME r τ → RexpME (substRNF x (renameRNF (renaming 𝓈 fv) r') r) (substRExpR 𝓈 x r' fv τ)

-- substRExpR ∷ 𝑃 𝕏 → 𝕏 → RNF → 𝑃 𝕏 → Type RNF → Type RNF
-- substRExpR 𝓈 x r' fv = undefined
