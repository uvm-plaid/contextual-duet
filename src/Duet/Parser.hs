module Duet.Parser where

import Duet.UVMHS

import Duet.Syntax
import Duet.RNF2

data Token =
    TokenName 𝕊
  | TokenLiteral 𝕊
  | TokenInteger ℤ
  | TokenDouble 𝔻
  | TokenComment
  | TokenSpace
  deriving (Eq,Ord,Show)
makePrisms ''Token
makePrettyUnion ''Token

tokKeywords ∷ 𝐿 𝕊
tokKeywords = list
  ["let","in","sλ","pλ","return","on"
  ,"ℕ","ℝ","ℝ⁺","𝔻","𝕀","𝕄","𝔻𝔽","𝔹","𝕊","★","∷","⋅","[]","⧺","☆"
  ,"∀","⊥","⊤","sens","priv","∞","cxt","schema"
  ,"LR","L2","U"
  ,"real","set"
  ,"matrix","℘","𝐝","∈"
  ,"sample","rand-nat"
  ,"L1","L2","L∞","U"
  ,"ZCDP","RENYI","EPSDP"
  ,"box","unbox","boxed"
  ,"if","then","else"
  ,"true","false"
  ,"primitive"
  ,"CSVtoMatrix"
  ,"fst","snd","inl","inr","case","of"
  ]

tokPunctuation ∷ 𝐿 𝕊
tokPunctuation = list
  ["=",":","@",".","⇒","→","←","#","↦","≡","⧼","⧽"
  ,"[","]","(",")","{","}","<",">",",",";","|","⟨","⟩"
  ,"⊔","⊓","+","⋅","/","√","㏒"
  ,"-","%","≟"
  ,"×","&","⊸","⊸⋆"
  ,"∧","∨"
  ,"?","!"
  ]

tokComment ∷ Parser ℂ ()
tokComment = pNew "comment" $ do
  void $ pWord "--"
  void $ pMany $ pSatisfies "not newline" $ \ c → c ≢ '\n'
  void $ pLit '\n'

tokMLComment ∷ Parser ℂ ()
tokMLComment = pNew "multiline comment" $ do
  () ← void $ pWord "{-"
  afterOther
  where
    afterOther = tries
      [ do () ← void $ pSatisfies "non-delimiter" $ \ c → c ∉ pow ['{','-']
           afterOther
      , do () ← void $ pLit '{'
           afterBrack
      , do () ← void $ pLit '-'
           afterDash
      ]
    afterBrack = tries
      [ do () ← void $ pSatisfies "non-delimiter" $ \ c → c ∉ pow ['{','-']
           afterOther
      , do () ← void $ pLit '{'
           afterBrack
      , do () ← void $ pLit '-'
           () ← afterOther
           afterOther
      ]
    afterDash = tries
      [ do () ← void $ pSatisfies "non-delimiter" $ \ c → c ∉ pow ['{','-','}']
           afterOther
      , do () ← void $ pLit '{'
           afterBrack
      , do () ← void $ pLit '-'
           afterDash
      , do void $ pLit '}'
      ]

tokDuet ∷ 𝐿 (Parser ℂ Token)
tokDuet = list $ concat
  [ TokenLiteral ^∘ pRender (FG darkYellow) ∘ pRender BD ∘ pWord ^$ tokKeywords
  , TokenLiteral ^∘ pRender (FG darkGray) ∘ pWord ^$ tokPunctuation
  , single $ TokenName ^$ pRender (FG black) pName
  , single $ map (elimChoice TokenInteger TokenDouble) $ pRender (FG darkRed) pNumber
  , map (const TokenComment) ∘ pRender (FG gray) ∘ pRender IT ^$ list [tokComment,tokMLComment]
  , single $ const TokenSpace ^$ pWhitespace
  ]

parLit ∷ 𝕊 → Parser Token ()
parLit = void ∘ pLit ∘ TokenLiteral

parVar ∷ Parser Token 𝕏
parVar = var ^$ pShaped "name" $ view tokenNameL

parName ∷ Parser Token 𝕊
parName = pShaped "name" $ view tokenNameL

parInt ∷ Parser Token ℤ
parInt = pShaped "int" $ view tokenIntegerL

parNat ∷ Parser Token ℕ
parNat = pShaped "nat" $ \ t → do
  i ← view tokenIntegerL t
  natO i

parDbl ∷ Parser Token 𝔻
parDbl = pShaped "dbl" $ view tokenDoubleL

parNNDbl ∷ Parser Token 𝔻
parNNDbl = pShaped "nn-dbl" $ \ t → do
  d ← view tokenDoubleL t
  case d ≥ 0.0 of
    True → return d
    False → abort

parKind ∷ Parser Token Kind
parKind = pNew "kind" $ tries
  [ do parLit "ℕ" ; return ℕK
  , do parLit "ℝ⁺" ; return ℝK
  , do parLit "☆" ; return TypeK
  , do parLit "cxt" ; return CxtK
  , do parLit "schema" ; return SchemaK
  ]

parPEnv ∷ (PRIV_C p) ⇒ PRIV_W p → Parser Token (PEnv RExp)
parPEnv mode = tries
  [ do
      parLit "["
      xprs ← pManySepBy (parLit ",") $ do
        x ← parProgramVar
        parLit "⋅"
        pr ← parPriv mode
        return (x :* pr)
      parLit "]"
      return $ PEnv $ assoc xprs
  ]

parSEnv ∷ Parser Token (ProgramVar ⇰ Sens RExp)
parSEnv = tries
  [ do
      parLit "["
      xsens ← pManySepBy (parLit ",") $ do
        x ← parProgramVar
        parLit "⋅"
        sens ← parSens
        return (x :* sens)
      parLit "]"
      return $ assoc xsens
  ]

parPrimitives ∷ (PRIV_C p) ⇒ PRIV_W p → Parser Token (𝕏 ⇰ Type RExp)
parPrimitives mode = tries
  [ do
      prims ← pManySepBy (parLit ",") $ do
        parLit "primitive"
        x ← parVar
        parLit ":"
        τ ← parType mode
        return (x :* τ)
      return $ assoc prims
  ]


parProgramVar ∷ Parser Token (ProgramVar)
parProgramVar = tries
  [ do
      parLit "["
      x ← parVar
      parLit "]"
      return $ TLVar x
  , do x ← parVar; return $ TMVar x
  ]

parRowsT ∷ Parser Token (RowsT RExp)
parRowsT = tries
  [ do const StarRT ^$ parLit "★"
  , do η ← parRExp; return $ RexpRT η
  ]

parMExp ∷ (PRIV_C p) ⇒ PRIV_W p → Parser Token (MExp RExp)
parMExp mode = mixfixParser $ concat
  [ mix $ MixTerminal $ const EmptyME ^$ parLit "[]"
  , mix $ MixPrefix 6 $ do
      τ ← parType mode
      parLit "∷"
      return $ \ me → ConsME τ me
  , mix $ MixInfixL 3 $ do
      parLit "⧺"
      return AppendME
  , mix $ MixTerminal $ do
      r ← parRExp
      parLit "↦"
      τ ← parType mode
      return $ RexpME r τ
  , mix $ MixTerminal $ VarME ^$ parVar
  ]

parTLExp ∷ (PRIV_C p) ⇒ PRIV_W p → Parser Token (TLExp RExp)
parTLExp mode = mixfixParserWithContext "tlexp" $ concat
  [ mixF $ MixFTerminal $ VarTE ^$ parVar
  -- Type Stuff
  , mixF $ MixFTerminal $ do
      parLit "ℕ"
      parLit "["
      η ← parRExp
      parLit "]"
      return $ ℕˢTE η
  , mixF $ MixFTerminal $ do
      parLit "ℝ⁺"
      parLit "["
      η ← parRExp
      parLit "]"
      return $ ℝˢTE η
  , mixF $ MixFTerminal $ do
      parLit "⟨"
      η₁ ← parTLExp mode
      parLit ","
      η₂ ← parTLExp mode
      parLit "⟩"
      return $ PairTE η₁ η₂
  , mixF $ MixFTerminal $ const ℕTE ^$ parLit "ℕ"
  , mixF $ MixFTerminal $ const ℝTE ^$ parLit "ℝ"
  , mixF $ MixFTerminal $ const 𝔹TE ^$ parLit "𝔹"
  , mixF $ MixFTerminal $ const 𝕊TE ^$ parLit "𝕊"
  , mixF $ MixFTerminal $ do
      parLit "𝕀"
      parLit "["
      η ← parRExp
      parLit "]"
      return $ 𝕀TE η
  , mixF $ MixFTerminal $ do
      parLit "𝕄"
      parLit "["
      ℓ ← parNorm
      parLit ","
      c ← parClip
      parLit "|"
      ηₘ ← parRowsT
      parLit ","
      ηₙ ← parMExp mode
      parLit "]"
      return $ 𝕄TE ℓ c ηₘ ηₙ
  , mixF $ MixFTerminal $ do
      parLit "𝔻"
      return $ 𝔻TE $ Annotated null ℝTE
  , mixF $ MixFTerminal $ do
      parLit "℘"
      parLit "("
      τe ← parTLExp mode
      parLit ")"
      return $ SetTE τe
  -- TODO: support parsing sensitivity and clip
  , mixF $ MixFPrefix 6 $ const (𝔻TE) ^$ parLit "𝐝"
  , mixF $ MixFInfixL 3 $ const (:⊕♭:) ^$ parLit "+"
  , mixF $ MixFInfixL 4 $ const (:⊗♭:) ^$ parLit "×"
  , mixF $ MixFInfixL 4 $ const (:&♭:) ^$ parLit "&"
  , mixF $ MixFPrefix 2 $ do
      parLit "("
      x ← parVar
      parLit ":"
      τ₁ ← parTLExp mode
      parLit ")"
      parLit "⊸"
      σ ← parSEnv
      return $ \ τ₂ → (x :* τ₁) :⊸♭: (σ :* τ₂)
  , mixF $ MixFPrefix 2 $ do
      parLit "("
      x ← parVar
      parLit ":"
      τ₁ ← parTLExp mode
      parLit "⋅"
      s ← parSens
      parLit "⊸⋆"
      parLit ")"
      σ ← parPEnv mode
      return $ \ τ₂ → (x :* τ₁ :* s) :⊸⋆♭: (σ :* τ₂)
  , mixF $ MixFPrefix 2 $ do
      parLit "∀"
      α ← parVar
      parLit ":"
      κ ← parKind
      parLit "."
      return $ \ τ → ForallTE α κ τ
  , mixF $ MixFTerminal $ do
      parLit "<"
      xs ← pManySepBy (parLit ",") parProgramVar
      parLit ">"
      return $ CxtTE $ pow xs
  , mixF $ MixFPrefix 3 $ do
      parLit "box"
      parLit "["
      xηs ← pManySepBy (parLit ",") $ do
        x ← parVar
        parLit "@"
        η ← parRExp
        return (x :* η)
      parLit "]"
      return $ \ τ → BoxedTE (map ι $ assoc xηs) τ
  -- RExp Stuff
  , mixF $ MixFTerminal $ NatTE ^$ parNat
  , mixF $ MixFTerminal $ NNRealTE ^$ parNNDbl
  , mixF $ MixFInfixL 2 $ const MaxTE ^$ parLit "⊔"
  , mixF $ MixFInfixL 3 $ const MinTE ^$ parLit "⊓"
  , mixF $ MixFInfixL 4 $ const PlusTE ^$ parLit "+"
  , mixF $ MixFInfixL 5 $ const TimesTE ^$ parLit "⋅"
  , mixF $ MixFInfixL 6 $ const DivTE ^$ parLit "/"
  , mixF $ MixFPrefix 7 $ const RootTE ^$ parLit "√"
  , mixF $ MixFPrefix 7 $ const LogTE ^$ parLit "㏒"
  -- Matrix stuff
  -- , mixF $ MixFTerminal $ const EmptyTE ^$ parLit "[]"
  -- , mixF $ MixFPrefix 6 $ do
  --    τ ← parTLExp mode
  --    parLit "∷"
  --    return $ \ me → ConsTE τ me
  -- , mixF $ MixFInfixL 3 $ do
  --    parLit "⧺"
  --    return AppendTE
  -- , mixF $ MixFTerminal $ do
  --    r ← parTLExp mode
  --    parLit "↦"
  --    τ ← parTLExp mode
  --    return $ RexpTE r τ
  -- Quantity Stuff
  , mixF $ MixFTerminal $ do parLit "∞" ; return TopTE
  -- Privacy Stuff
  -- , mixF $ MixFTerminal $ -- ⟨ tle , tle ⟩
  ]

parSens ∷ Parser Token (Sens RExp)
parSens = do
  e ← parRExp
  return $ Sens e

parRExp ∷ Parser Token RExp
parRExp = mixfixParserWithContext "rexp" $ concat
  [ mixF $ MixFTerminal $ do
      parLit "("
      e ← parRExp
      parLit ")"
      return $ extract e
  , mixF $ MixFTerminal $ do
      x ← parVar
      return $ VarRE x
  , mixF $ MixFTerminal $ do
      parLit "∞"
      return $ ConstRE Top
  , mixF $ MixFTerminal $ ConstRE ∘ AddTop ^$ parNNDbl
  , mixF $ MixFInfixL 2 $ const MaxRE ^$ parLit "⊔"
  , mixF $ MixFInfixL 3 $ const MinRE ^$ parLit "⊓"
  , mixF $ MixFInfixL 4 $ const PlusRE ^$ parLit "+"
  , mixF $ MixFInfixL 5 $ const TimesRE ^$ parLit "⋅"
  , mixF $ MixFInfixL 6 $ const DivRE ^$ parLit "/"
  , mixF $ MixFPrefix 7 $ const (PowRE (rat 1 / rat 2)) ^$ parLit "√"
  -- TODO: add exp
  , mixF $ MixFPrefix 7 $ const LogRE ^$ parLit "㏒"
  ]

parNorm ∷ Parser Token Norm
parNorm = tries
  [ do const L1 ^$ parLit "L1"
  , do const L2 ^$ parLit "L2"
  , do const LInf ^$ parLit "L∞"
  ]

parClip ∷ Parser Token Clip
parClip = tries
  [ do NormClip ^$ parNorm
  , do const UClip ^$ parLit "U"
  ]

parPriv ∷ (PRIV_C p) ⇒ PRIV_W p → Parser Token (Pr p RExp)
parPriv p = tries
  [ case p of
      ED_W → do
        parLit "⟨"
        ϵ ← parRExp
        parLit ","
        δ ← parRExp
        parLit "⟩"
        return $ EDPriv ϵ δ
      _ → abort
  , case p of
      ED_W → do
        parLit "⊥"
        return $ EDPriv (Annotated null $ ConstRE (AddTop 0.0)) (Annotated null $ ConstRE (AddTop 0.0))
      _ → abort
  , case p of
      ED_W → do
        parLit "⊤"
        return $ EDPriv (Annotated null $ ConstRE Top) (Annotated null $ ConstRE Top)
      _ → abort
  ]

parSpace ∷ Parser Token ()
parSpace = pSkip (const False) $ void $ pOneOrMore $ tries
  [ pLit TokenComment
  , pLit TokenSpace
  ]

parTypeSource ∷ (PRIV_C p) ⇒ PRIV_W p → Parser Token (TypeSource RExp)
parTypeSource p = pWithContext "type" (parType p)

parType ∷ (PRIV_C p) ⇒ PRIV_W p → Parser Token (Type RExp)
parType mode = mixfixParser $ concat
  [ mix $ MixTerminal $ do
      parLit "("
      τ ← parType mode
      parLit ")"
      return τ
  , mix $ MixTerminal $ do
      parLit "ℕ"
      parLit "["
      η ← parRExp
      parLit "]"
      return $ ℕˢT η
  , mix $ MixTerminal $ do
      parLit "ℝ⁺"
      parLit "["
      η ← parRExp
      parLit "]"
      return $ ℝˢT η
  , mix $ MixTerminal $ const ℕT ^$ parLit "ℕ"
  , mix $ MixTerminal $ const ℝT ^$ parLit "ℝ"
  , mix $ MixTerminal $ const 𝔹T ^$ parLit "𝔹"
  , mix $ MixTerminal $ const 𝕊T ^$ parLit "𝕊"
  , mix $ MixTerminal $ VarT ^$ parVar
  , mix $ MixTerminal $ do
      parLit "𝕀"
      parLit "["
      η ← parRExp
      parLit "]"
      return $ 𝕀T η
  , mix $ MixTerminal $ do
      parLit "𝕄"
      parLit "["
      ℓ ← parNorm
      parLit ","
      c ← parClip
      parLit "|"
      ηₘ ← parRowsT
      parLit ","
      ηₙ ← parMExp mode
      parLit "]"
      return $ 𝕄T ℓ c ηₘ ηₙ
  , mix $ MixTerminal $ do
      parLit "𝔻"
      return $ 𝔻T ℝT
  , mix $ MixTerminal $ do
      parLit "℘"
      parLit "("
      τ ← parType mode
      parLit ")"
      return $ SetT τ
  -- TODO: support parsing sensitivity and clip
  , mix $ MixPrefix 6 $ const (𝔻T) ^$ parLit "𝐝"
  , mix $ MixInfixL 3 $ const (:⊕:) ^$ parLit "+"
  , mix $ MixInfixL 4 $ const (:⊗:) ^$ parLit "×"
  , mix $ MixInfixL 4 $ const (:&:) ^$ parLit "&"
  , mix $ MixInfixL 3 $ do
      σ₁ ← parSEnv
      parLit "⊞"
      σ₂ ← parSEnv
      return $ \ τ₁ τ₂ → (τ₁ :* σ₁) :⊞: (σ₂ :* τ₂)
  , mix $ MixInfixL 3 $ do
      σ₁ ← parSEnv
      parLit "⊠"
      σ₂ ← parSEnv
      return $ \ τ₁ τ₂ → (τ₁ :* σ₁) :⊠: (σ₂ :* τ₂)
  , mix $ MixPrefix 2 $ do
      parLit "("
      x ← parVar
      parLit ":"
      τ₁ ← parType mode
      parLit ")"
      parLit "⊸"
      σ ← parSEnv
      return $ \ τ₂ → (x :* τ₁) :⊸: (σ :* τ₂)
  , mix $ MixPrefix 2 $ do
      parLit "("
      x ← parVar
      parLit ":"
      τ₁ ← parType mode
      parLit "⋅"
      s ← parSens
      parLit ")"
      parLit "⊸⋆"
      σ ← parPEnv mode
      return $ \ τ₂ → (x :* τ₁ :* s) :⊸⋆: (σ :* τ₂)
  , mix $ MixPrefix 2 $ do
      parLit "∀"
      x ← parVar
      parLit ":"
      κ ← parKind
      xκs ← pMany $ do
        parLit ","
        x' ← parVar
        parLit ":"
        κ' ← parKind
        return $ x' :* κ'
      parLit "."
      return $ \ e →
        ForallT x κ $ foldr e (\ (x' :* κ') e' → ForallT x' κ' e') xκs
  , mix $ MixTerminal $ do
      parLit "<"
      xs ← pManySepBy (parLit ",") parProgramVar
      parLit ">"
      return $ CxtT $ pow xs
  , mix $ MixPrefix 3 $ do
      parLit "box"
      parLit "["
      xηs ← pManySepBy (parLit ",") $ do
        x ← parVar
        parLit "@"
        η ← parRExp
        return (x :* η)
      parLit "]"
      return $ \ τ → BoxedT (map ι $ assoc xηs) τ
  ]

parGrad ∷ Parser Token Grad
parGrad = tries
  [ const LR ^$ parLit "LR"
  ]

parSExp ∷ (PRIV_C p) ⇒ PRIV_W p → Parser Token (SExpSource p RExp)
parSExp p = mixfixParserWithContext "sexp" $ concat
  [ mixF $ MixFTerminal $ do
      parLit "("
      e ← parSExp p
      parLit ")"
      return $ extract e
  , mixF $ MixFTerminal $ do
      parLit "ℕ"
      parLit "["
      n ← parNat
      parLit "]"
      return $ ℕˢSE n
  , mixF $ MixFTerminal $ do
      parLit "ℝ⁺"
      parLit "["
      d ← parNNDbl
      parLit "]"
      return $ ℝˢSE d
  , mixF $ MixFTerminal $ do
      parLit "⟨"
      e₁ ← parSExp p
      parLit ","
      e₂ ← parSExp p
      parLit "⟩"
      return $ PairSE e₁ e₂
  , mixF $ MixFTerminal $ do
      parLit "fst"
      e ← parSExp p
      return $ FstSE e
  , mixF $ MixFTerminal $ do
      parLit "snd"
      e ← parSExp p
      return $ SndSE e
  , mixF $ MixFTerminal $ do
      parLit "inl"
      parLit "["
      τ ← parTypeSource p
      parLit "]"
      e ← parSExp p
      return $ InlSE τ e
  , mixF $ MixFTerminal $ do
      parLit "inr"
      parLit "["
      τ ← parTypeSource p
      parLit "]"
      e ← parSExp p
      return $ InrSE τ e
  , mixF $ MixFTerminal $ do
      parLit "case"
      e₁ ← parSExp p
      parLit "of"
      parLit "{"
      x₁ ← parVar
      parLit "⇒"
      e₂ ← parSExp p
      parLit "}"
      parLit "{"
      x₂ ← parVar
      parLit "⇒"
      e₃ ← parSExp p
      parLit "}"
      return $ CaseSE e₁ x₁ e₂ x₂ e₃
  , mixF $ MixFTerminal $ do
      parLit "true"
      return $ TrueSE
  , mixF $ MixFTerminal $ do
      parLit "false"
      return $ FalseSE
  , mixF $ MixFTerminal $ ℕSE ^$ parNat
  , mixF $ MixFTerminal $ ℝSE ^$ parDbl
  , mixF $ MixFTerminal $ VarSE ^$ parVar
  , mixF $ MixFPrefix 1 $ do
      parLit "let"
      tries
        [ do x ← parVar
             parLit "="
             e₁ ← parSExp p
             parLit "in"
             return $ \ e₂ → LetSE x e₁ e₂
        ]
  , mixF $ MixFInfixL 10 $ do
      parSpace
      xsO ← pOptional $ do
        parLit "<"
        xs ← pManySepBy (parLit ",") $ parProgramVar
        parLit ">"
        return xs
      return $ \ e₁ e₂ → AppSE e₁ xsO e₂
  , mixF $ MixFPrefix 1 $ do
      parLit "sλ"
      xsO ← pOptional $ do
        parLit "<"
        xs ← pManySepBy (parLit ",") $ parProgramVar
        parLit ">"
        return xs
      x ← parVar
      parLit ":"
      τ ← parTypeSource p
      xτs ← pMany $ do
        parLit ","
        xsO' ← pOptional $ do
          parLit "<"
          xs ← pManySepBy (parLit ",") $ parProgramVar
          parLit ">"
          return xs
        x' ← parVar
        parLit ":"
        τ' ← parTypeSource p
        return $ xsO' :* x' :* τ'
      parLit "⇒"
      return $ \ e →
        let ecxt = annotatedTag e
        in SFunSE xsO x τ $ foldr e (\ (xsO' :* x' :* τ') e' → Annotated ecxt $ SFunSE xsO' x' τ' e') xτs
  , mixF $ MixFTerminal $ do
      parLit "pλ"
      xsO ← pOptional $ do
        parLit "<"
        xs ← pManySepBy (parLit ",") $ parProgramVar
        parLit ">"
        return xs
      x ← parVar
      parLit ":"
      τ ← parTypeSource p
      parLit "⋅"
      s ← parSens
      xτs ← pMany $ do
        parLit ","
        xsO' ← pOptional $ do
          parLit "<"
          xs ← pManySepBy (parLit ",") $ parProgramVar
          parLit ">"
          return xs
        x' ← parVar
        parLit ":"
        τ' ← parTypeSource p
        parLit "⋅"
        s' ← parSens
        return $ xsO' :* x' :* τ' :* s'
      parLit "⇒"
      e ← parPExp p
      return $
        let ecxt = annotatedTag e
        in PFunSE xsO x τ s $ foldr e (\ (xsO' :* x' :* τ' :* s') e' → Annotated ecxt $ ReturnPE $ Annotated ecxt $ PFunSE xsO' x' τ' s' e') xτs
  , mixF $ MixFPrefix 1 $ do
      parLit "∀"
      x ← parVar
      parLit ":"
      κ ← parKind
      xκs ← pMany $ do
        parLit ","
        x' ← parVar
        parLit ":"
        κ' ← parKind
        return $ x' :* κ'
      parLit "."
      return $ \ e →
        let ecxt = annotatedTag e
        in TAbsSE x κ $ foldr e (\ (x' :* κ') e' → Annotated ecxt $ TAbsSE x' κ' e') xκs
  , mixF $ MixFPostfix 10 $ do
      parLit "@"
      τ ← parTLExp p
      return $ \ e → TAppSE e τ
  ]

parPExp ∷ (PRIV_C p) ⇒ PRIV_W p → Parser Token (PExpSource p RExp)
parPExp p = pWithContext "pexp" $ tries
  [ do parLit "let"
       x ← parVar
       parLit "="
       e₁ ← parSExp p
       parLit "in"
       e₂ ← parPExp p
       return $ BindPE x (ReturnPE %⋅ e₁) e₂
  , do parLit "return"
       e ← parSExp p
       return $ ReturnPE e
  , do x ← parVar
       parLit "←"
       e₁ ← parPExp p
       parLit ";"
       e₂ ← parPExp p
       return $ BindPE x e₁ e₂
  , do e ← parSExp p
       case extract e of
         -- QUESTION: should AppPE have a SExp or PExp as its first argument?
         AppSE e₁ xs e₂ → do
           return $ AppPE e₁ xs e₂
         _ → abort
  , case p of
       ED_W → tries
         [ do parLit "ZCDP"
              parLit "["
              e₁ ← parSExp ED_W
              parLit "]"
              parLit "{"
              e₂ ← parPExp ZC_W
              parLit "}"
              return $ ConvertZCEDPE e₁ e₂
         , do parLit "RENYI"
              parLit "["
              e₁ ← parSExp ED_W
              parLit "]"
              parLit "{"
              e₂ ← parPExp RENYI_W
              parLit "}"
              return $ ConvertRENYIEDPE e₁ e₂
         ]
       ZC_W → tries
         [ do parLit "EPSDP"
              parLit "{"
              e₁ ← parPExp EPS_W
              parLit "}"
              return $ ConvertEPSZCPE e₁
         ]
       _ → abort
  ]

tokSkip ∷ Token → 𝔹
tokSkip = \case
  TokenSpace → True
  TokenComment → True
  _ → False
