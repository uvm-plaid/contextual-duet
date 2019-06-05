module Duet.Parser where

import Duet.UVMHS

import Duet.Syntax
import Duet.RNF2
import Duet.Quantity

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
  ,"∀","⊥","⊤","sens","priv","∞"
  ,"LR","L2","U"
  ,"real","bag","set","record", "unionAll"
  ,"partitionDF","addColDF","mapDF","join₁","joinDF₁","parallel"
  ,"chunks","mfold-row","mfilter","zip","AboveThreshold","mmap-col","mmap-row","pfld-rows","pmap-col"
  ,"matrix","mcreate","mclip","clip","∇","U∇","mmap","bmap","idx","℘","𝐝","conv","disc","∈"
  ,"aloop","loop","gauss","mgauss","bgauss","laplace","mlaplace","mconv","×","tr","mmapp"
  ,"rows","cols", "count","exponential","rand-resp","discf"
  ,"sample","rand-nat"
  ,"L1","L2","L∞","U"
  ,"dyn","real"
  ,"ZCDP","RENYI","EPSDP"
  ,"box","unbox","boxed"
  ,"if","then","else"
  ,"true","false"
  ,"CSVtoMatrix"
  ]

tokPunctuation ∷ 𝐿 𝕊
tokPunctuation = list
  ["=",":","@",".","⇒","→","←","#","↦","≡","⧼","⧽"
  ,"[","]","(",")","{","}","<",">",",",";","|","⟨","⟩"
  ,"⊔","⊓","+","⋅","/","√","㏒"
  ,"-","%","≟"
  ,"×","&","⊸","⊸⋆"
  ,"∧","∨"
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

parKind ∷ (PRIV_C p) ⇒ PRIV_W p → Parser Token Kind
parKind p = pNew "kind" $ tries
  [ do parLit "ℕ" ; return ℕK
  , do parLit "ℝ⁺" ; return ℝK
  , do parLit "☆" ; return TypeK
  ]

parPEnv ∷ (PRIV_C p) ⇒ PRIV_W p → Parser Token (PEnv RExp)
parPEnv mode = tries
  [ do
      parLit "["
      xprs ← pManySepBy (parLit ",") $ do
        x ← parVar
        parLit "⋅"
        pr ← parPriv mode
        return (x :* pr)
      parLit "]"
      return $ PEnv $ assoc xprs
  ]

parSEnv ∷ Parser Token (𝕏 ⇰ Sens RExp)
parSEnv = tries
  [ do
      parLit "["
      xsens ← pManySepBy (parLit ",") $ do
        x ← parVar
        parLit "⋅"
        sens ← parSens
        return (x :* sens)
      parLit "]"
      return $ assoc xsens
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
      parLit "⋅"
      τ ← parType mode
      return $ RexpME r τ
  , mix $ MixTerminal $ VarME ^$ parVar
  ]

parSTLExp ∷ (PRIV_C p) ⇒ PRIV_W p → Parser Token (STLExp RExp)
parSTLExp mode = mixfixParserWithContext "tlexp" $ concat
  [ mixF $ MixFTerminal $ VarSTE ^$ parVar
  -- Type Stuff
  , mixF $ MixFTerminal $ do
      parLit "ℕ"
      parLit "["
      η ← parRExp
      parLit "]"
      return $ ℕˢSTE η
  , mixF $ MixFTerminal $ do
      parLit "ℝ⁺"
      parLit "["
      η ← parRExp
      parLit "]"
      return $ ℝˢSTE η
  , mixF $ MixFTerminal $ do
      parLit "⟨"
      η₁ ← parSTLExp mode
      parLit ","
      η₂ ← parSTLExp mode
      parLit "⟩"
      return $ PairSTE η₁ η₂
  , mixF $ MixFTerminal $ const ℕSTE ^$ parLit "ℕ"
  , mixF $ MixFTerminal $ const ℝSTE ^$ parLit "ℝ"
  , mixF $ MixFTerminal $ const 𝔹STE ^$ parLit "𝔹"
  , mixF $ MixFTerminal $ const 𝕊STE ^$ parLit "𝕊"
  , mixF $ MixFTerminal $ do
      parLit "𝕀"
      parLit "["
      η ← parRExp
      parLit "]"
      return $ 𝕀STE η
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
      return $ 𝕄STE ℓ c ηₘ ηₙ
  -- , mixF $ MixFTerminal $ do
  --     parLit "𝔻"
  --     return $ 𝔻TE ℝTE
  , mixF $ MixFTerminal $ do
      parLit "℘"
      parLit "("
      τe ← parSTLExp mode
      parLit ")"
      return $ SetSTE τe
  -- TODO: support parsing sensitivity and clip
  , mixF $ MixFPrefix 6 $ const (𝔻STE) ^$ parLit "𝐝"
  , mixF $ MixFInfixL 3 $ const (:⊕♭♭:) ^$ parLit "+"
  , mixF $ MixFInfixL 4 $ const (:⊗♭♭:) ^$ parLit "×"
  , mixF $ MixFInfixL 4 $ const (:&♭♭:) ^$ parLit "&"
  , mixF $ MixFPrefix 2 $ do
      τ₁ ← parSTLExp mode
      parLit "⊸"
      parLit "["
      s ← parSens
      parLit "]"
      return $ \ τ₂ → τ₁ :⊸♭♭: (s :* τ₂)
  , mixF $ MixFPrefix 2 $ do
      x ← parVar
      parLit ":"
      τ₁ ← parSTLExp mode
      parLit "⊸⋆"
      parLit "["
      σ ← parPEnv mode
      parLit "]"
      return $ \ τ₂ → (x :* τ₁) :⊸⋆♭♭: (σ :* τ₂)
  , mixF $ MixFPrefix 2 $ do
      parLit "∀"
      α ← parVar
      parLit ":"
      κ ← parKind mode
      parLit "."
      return $ \ τ → ForallSTE α κ τ
  , mixF $ MixFPrefix 3 $ do
      parLit "box"
      parLit "["
      xηs ← pManySepBy (parLit ",") $ do
        x ← parVar
        parLit "@"
        η ← parRExp
        return (x :* η)
      parLit "]"
      return $ \ τ → BoxedSTE (map ι $ assoc xηs) τ
  -- RExp Stuff
  , mixF $ MixFTerminal $ NatSTE ^$ parNat
  , mixF $ MixFTerminal $ NNRealSTE ^$ parNNDbl
  , mixF $ MixFInfixL 2 $ const MaxSTE ^$ parLit "⊔"
  , mixF $ MixFInfixL 3 $ const MinSTE ^$ parLit "⊓"
  , mixF $ MixFInfixL 4 $ const PlusSTE ^$ parLit "+"
  , mixF $ MixFInfixL 5 $ const TimesSTE ^$ parLit "⋅"
  , mixF $ MixFInfixL 6 $ const DivSTE ^$ parLit "/"
  , mixF $ MixFPrefix 7 $ const RootSTE ^$ parLit "√"
  , mixF $ MixFPrefix 7 $ const LogSTE ^$ parLit "㏒"
  -- Quantity Stuff
  , mixF $ MixFTerminal $ do parLit "∞" ; return TopSTE
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
      parLit ")"
      parLit "⊸⋆"
      σ ← parPEnv mode
      return $ \ τ₂ → (x :* τ₁) :⊸⋆: (σ :* τ₂)
  , mix $ MixPrefix 2 $ do
      parLit "∀"
      x ← parVar
      parLit ":"
      κ ← parKind mode
      xκs ← pMany $ do
        parLit ","
        x' ← parVar
        parLit ":"
        κ' ← parKind mode
        return $ x' :* κ'
      parLit "."
      return $ \ e →
        ForallT x κ $ foldr e (\ (x' :* κ') e' → ForallT x' κ' e') xκs
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

parSExp ∷ (PRIV_C p) ⇒ PRIV_W p → Parser Token (SExpSource p)
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
      parLit "true"
      return $ TrueSE
  , mixF $ MixFTerminal $ do
      parLit "false"
      return $ FalseSE
  , mixF $ MixFPrefix 10 $ const DynSE ^$ parLit "dyn"
  , mixF $ MixFTerminal $ ℕSE ^$ parNat
  , mixF $ MixFTerminal $ ℝSE ^$ parDbl
  , mixF $ MixFPrefix 10 $ const RealSE ^$ parLit "real"
  , mixF $ MixFInfixL 3 $ const MaxSE ^$ parLit "⊔"
  , mixF $ MixFInfixL 4 $ const MinSE ^$ parLit "⊓"
  , mixF $ MixFInfixL 5 $ const PlusSE ^$ parLit "+"
  , mixF $ MixFInfixL 6 $ const TimesSE ^$ parLit "⋅"
  , mixF $ MixFInfixL 6 $ const MTimesSE ^$ parLit "×"
  , mixF $ MixFInfixL 7 $ const DivSE ^$ parLit "/"
  , mixF $ MixFPrefix 8 $ const RootSE ^$ parLit "√"
  , mixF $ MixFPrefix 8 $ const LogSE ^$ parLit "㏒"
  , mixF $ MixFInfixL 7 $ const ModSE ^$ parLit "%"
  , mixF $ MixFInfixL 5 $ const MinusSE ^$ parLit "-"
  , mixF $ MixFInfixL 2 $ const MinusSE ^$ parLit "≟"
  , mixF $ MixFInfixL 2 $ const EqualsSE ^$ parLit "≡"
  , mixF $ MixFInfixL 2 $ const MemberSE ^$ parLit "∈"
  , mixF $ MixFInfixL 1 $ const AndSE ^$ parLit "∧"
  , mixF $ MixFInfixL 1 $ const OrSE ^$ parLit "∨"
  , mixF $ MixFPostfix 10 $ do
      parLit "⧼"
      a ← parName
      parLit "⧽"
      return $ RecordColSE a
  , mixF $ MixFTerminal $ do
      parLit "mfilter"
      e₁ ← parSExp p
      parLit "{"
      x ← parVar
      parLit "⇒"
      e₂ ← parSExp p
      parLit "}"
      return $ MFilterSE e₁ x e₂
  , mixF $ MixFTerminal $ do
      parLit "mapDF"
      e₁ ← parSExp p
      parLit "{"
      x ← parVar
      parLit "⇒"
      e₂ ← parSExp p
      parLit "}"
      return $ DFMapSE e₁ x e₂
  , mixF $ MixFTerminal $ do
      parLit "join₁"
      parLit "["
      e₁ ← parSExp p
      parLit ","
      e₂ ← parSExp p
      parLit ","
      e₃ ← parSExp p
      parLit ","
      e₄ ← parSExp p
      parLit "]"
      return $ JoinSE e₁ e₂ e₃ e₄
  , mixF $ MixFPrefix 10 $ do
      parLit "addColDF"
      parLit "⧼"
      x ← parName
      parLit "⧽"
      return $ DFAddColSE x
  , mixF $ MixFTerminal $ do
      parLit "partitionDF"
      parLit "["
      e₁ ← parSExp p
      parLit ","
      a ← parName
      parLit ","
      e₂ ← parSExp p
      parLit "]"
      return $ DFPartitionSE e₁ a e₂
  , mixF $ MixFTerminal $ do
      parLit "joinDF₁"
      parLit "⧼"
      x ← parName
      parLit "⧽"
      parLit "["
      e₁ ← parSExp p
      parLit ","
      e₂ ← parSExp p
      parLit "]"
      return $ DFJoin1SE x e₁ e₂
  , mixF $ MixFTerminal $ do
      parLit "mcreate"
      parLit "["
      ℓ ← parNorm
      parLit "|"
      e₁ ← parSExp p
      parLit ","
      e₂ ← parSExp p
      parLit "]"
      parLit "{"
      x₁ ← parVar
      parLit ","
      x₂ ← parVar
      parLit "⇒"
      e₃ ← parSExp p
      parLit "}"
      return $ MCreateSE ℓ e₁ e₂ x₁ x₂ e₃
  -- , mixF $ MixFTerminal $ do
  --   parLit "CSVtoMatrix"
  --   parLit "("
  --   f ← parName
  --   parLit ","
  --   τ ← parTypeSource p
  --   parLit ")"
  --   return $ CSVtoMatrixSE f τ
  , mixF $ MixFPostfix 10 $ do
      parLit "#"
      parLit "["
      e₂ ← parSExp p
      parLit ","
      e₃ ← parSExp p
      e₄O ← pOptional $ do
        parLit "↦"
        parSExp p
      parLit "]"
      return $ case e₄O of
        None → \ e₁ → MIndexSE e₁ e₂ e₃
        Some e₄ → \ e₁ → MUpdateSE e₁ e₂ e₃ e₄
  , mixF $ MixFPrefix 10 $ const MRowsSE ^$ parLit "rows"
  , mixF $ MixFPrefix 10 $ const MColsSE ^$ parLit "cols"
  , mixF $ MixFPrefix 10 $ const MTransposeSE ^$ parLit "tr"
  , mixF $ MixFPrefix 10 $ const IdxSE ^$ parLit "idx"
  , mixF $ MixFPrefix 10 $ const DiscFSE ^$ parLit "discf"
  , mixF $ MixFPrefix 10 $ do
      parLit "mclip"
      parLit "["
      ℓ ← parNorm
      parLit "]"
      return $ MClipSE ℓ
  , mixF $ MixFTerminal $ do
      parLit "∇"
      parLit "["
      g ← parGrad
      parLit "|"
      e₁ ← parSExp p
      parLit ";"
      e₂ ← parSExp p
      parLit ","
      e₃ ← parSExp p
      parLit "]"
      return $ MLipGradSE g e₁ e₂ e₃
  , mixF $ MixFTerminal $ do
      parLit "U∇"
      parLit "["
      g ← parGrad
      parLit "|"
      e₁ ← parSExp p
      parLit ";"
      e₂ ← parSExp p
      parLit ","
      e₃ ← parSExp p
      parLit "]"
      return $ MUnbGradSE g e₁ e₂ e₃
  , mixF $ MixFTerminal $ do
      parLit "mmap"
      e₁ ← parSExp p
      e₂O ← pOptional $ do
        parLit ","
        e₂ ← parSExp p
        return e₂
      parLit "{"
      x₁ ← parVar
      e₂x₂O ← case e₂O of
        None → return None
        Some e₂ → do
          parLit ","
          x₂ ← parVar
          return $ Some $ e₂ :* x₂
      parLit "⇒"
      e₃ ← parSExp p
      parLit "}"
      return $ case e₂x₂O of
        None → MMapSE e₁ x₁ e₃
        Some (e₂ :* x₂) → MMap2SE e₁ e₂ x₁ x₂ e₃
  , mixF $ MixFTerminal $ do
      parLit "mmap-col"
      e₁ ← parSExp p
      parLit "{"
      x ← parVar
      parLit "⇒"
      e₂ ← parSExp p
      parLit "}"
      return $ MMapColSE e₁ x e₂
  , mixF $ MixFTerminal $ do
      parLit "mmap-col"
      e₁ ← parSExp p
      parLit ","
      e₂ ← parSExp p
      parLit "{"
      x₁ ← parVar
      parLit ","
      x₂ ← parVar
      parLit "⇒"
      e₃ ← parSExp p
      parLit "}"
      return $ MMapCol2SE e₁ e₂ x₁ x₂ e₃
  , mixF $ MixFTerminal $ do
      parLit "mmap-row"
      e₁ ← parSExp p
      parLit "{"
      x ← parVar
      parLit "⇒"
      e₂ ← parSExp p
      parLit "}"
      return $ MMapRowSE e₁ x e₂
  , mixF $ MixFTerminal $ do
      parLit "mfold-row"
      e₁ ← parSExp p
      parLit ","
      e₂ ← parSExp p
      parLit "{"
      x₁ ← parVar
      parLit ","
      x₂ ← parVar
      parLit "⇒"
      e₃ ← parSExp p
      parLit "}"
      return $ MFoldSE e₁ e₂ x₁ x₂ e₃
  , mixF $ MixFTerminal $ do
      parLit "bmap"
      e₁ ← parSExp p
      e₂O ← pOptional $ do
        parLit ","
        e₂ ← parSExp p
        return e₂
      parLit "{"
      x₁ ← parVar
      e₂x₂O ← case e₂O of
        None → return None
        Some e₂ → do
          parLit ","
          x₂ ← parVar
          return $ Some $ e₂ :* x₂
      parLit "⇒"
      e₃ ← parSExp p
      parLit "}"
      return $ case e₂x₂O of
        None → BMapSE e₁ x₁ e₃
        Some (e₂ :* x₂) → BMap2SE e₁ e₂ x₁ x₂ e₃
  , mixF $ MixFTerminal $ VarSE ^$ parVar
  , mixF $ MixFPrefix 1 $ do
      parLit "let"
      tries
        [ do x ← parVar
             parLit "="
             e₁ ← parSExp p
             parLit "in"
             return $ \ e₂ → LetSE x e₁ e₂
        , do parLit "⟨"
             x ← parVar
             parLit ","
             y ← parVar
             parLit "⟩"
             parLit "="
             e₁ ← parSExp p
             parLit "in"
             return $ \ e₂ → UntupSE x y e₁ e₂
        ]
  , mixF $ MixFInfixL 10 $ const (\ e₁ e₂ → AppSE e₁ e₂) ^$ parSpace
      -- ακs ← pManySepBy (parLit ",") $ do
      --   α ← parVar
      --   parLit ":"
      --   κ ← parKind p
      --   return $ α :* κ
      -- parLit "."
  , mixF $ MixFPrefix 1 $ do
      parLit "sλ"
      x ← parVar
      parLit ":"
      τ ← parTypeSource p
      xτs ← pMany $ do
        parLit ","
        x' ← parVar
        parLit ":"
        τ' ← parTypeSource p
        return $ x' :* τ'
      parLit "⇒"
      return $ \ e →
        let ecxt = annotatedTag e
        in SFunSE x τ $ foldr e (\ (x' :* τ') e' → Annotated ecxt $ SFunSE x' τ' e') xτs
  , mixF $ MixFTerminal $ do
      parLit "pλ"
      x ← parVar
      parLit ":"
      τ ← parTypeSource p
      parLit "⇒"
      e ← parPExp p
      return $ PFunSE x τ e
  -- , mixF $ MixFTerminal $ do
  --     parLit "pλ"
  --     x ← parVar
  --     parLit ":"
  --     τ ← parTypeSource p
  --     xτs ← pOneOrMoreSepBy (parLit ",") $ do
  --       x' ← parVar
  --       parLit ":"
  --       τ' ← parTypeSource p
  --       return $ x :* τ
  --     parLit "⇒"
  --     e ← parPExp p
  --     return $
  --       let ecxt = annotatedTag e
  --       in PFunSE x τ $ foldr e (\ (x' :* τ') e' → Annotated ecxt $ ReturnPE $ Annotated ecxt $ PFunSE x' τ' e') xτs
  , mixF $ MixFPrefix 1 $ do
      parLit "∀"
      x ← parVar
      parLit ":"
      κ ← parKind p
      xκs ← pMany $ do
        parLit ","
        x' ← parVar
        parLit ":"
        κ' ← parKind p
        return $ x' :* κ'
      parLit "."
      return $ \ e →
        let ecxt = annotatedTag e
        in TAbsSE x κ $ foldr e (\ (x' :* κ') e' → Annotated ecxt $ TAbsSE x' κ' e') xκs
  , mixF $ MixFPostfix 10 $ do
      parLit "@"
      τ ← parTypeSource p
      return $ \ e → TAppSE e τ
  , mixF $ MixFTerminal $ do
      parLit "℘"
      parLit "{"
      ses ← pManySepBy (parLit ",") $ parSExp p
      parLit "}"
      return $ SetSE ses
  , mixF $ MixFTerminal $ do
      parLit "unionAll"
      e ← parSExp p
      return $ UnionAllSE e
  , mixF $ MixFTerminal $ do
       parLit "⟨"
       e₁ ← parSExp p
       parLit ","
       e₂ ← parSExp p
       parLit "⟩"
       return $ TupSE e₁ e₂
  , mixF $ MixFTerminal $ do
       parLit "loop"
       e₂ ← parSExp p
       parLit "on"
       e₃ ← parSExp p
       parLit "{"
       x₁ ← parVar
       parLit ","
       x₂ ← parVar
       parLit "⇒"
       e₄ ← parSExp p
       parLit "}"
       return $ LoopSE e₂ e₃ x₁ x₂ e₄
  , mixF $ MixFTerminal $ do
       parLit "chunks"
       parLit "["
       e₁ ← parSExp p
       parLit ","
       e₂ ← parSExp p
       parLit "]"
       return $ ChunksSE e₁ e₂
  , mixF $ MixFTerminal $ do
       parLit "chunks"
       parLit "["
       e₁ ← parSExp p
       parLit ","
       e₂ ← parSExp p
       parLit ","
       e₃ ← parSExp p
       parLit "]"
       return $ Chunks2SE e₁ e₂ e₃
  , mixF $ MixFTerminal $ do
       parLit "zip"
       parLit "["
       e₁ ← parSExp p
       parLit ","
       e₂ ← parSExp p
       parLit "]"
       return $ MZipSE e₁ e₂
  , mixF $ MixFPrefix 10 $ const BoxSE ^$ parLit "box"
  , mixF $ MixFPrefix 10 $ const UnboxSE ^$ parLit "unbox"
  , mixF $ MixFPrefix 10 $ const ClipSE ^$ parLit "clip"
  , mixF $ MixFPrefix 10 $ const ConvSE ^$ parLit "conv"
  , mixF $ MixFPrefix 10 $ const MConvertSE ^$ parLit "mconv"
  , mixF $ MixFPrefix 10 $ const DiscSE ^$ parLit "disc"
  , mixF $ MixFPrefix 10 $ const CountSE ^$ parLit "count"
  ]

parPExp ∷ (PRIV_C p) ⇒ PRIV_W p → Parser Token (PExpSource p)
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
  , do parLit "mmapp"
       e₁ ← parSExp p
       parLit "{"
       x ← parVar
       parLit "⇒"
       e₂ ← parPExp p
       parLit "}"
       return $ MMapPE e₁ x e₂
  , do parLit "pmap-col"
       e₁ ← parSExp p
       parLit "{"
       x ← parVar
       parLit "⇒"
       e₂ ← parPExp p
       parLit "}"
       return $ PMapColPE e₁ x e₂
  , do parLit "pfld-rows"
       parLit "["
       e₁ ← parSExp p
       parLit ","
       e₂ ← parSExp p
       parLit ","
       e₃ ← parSExp p
       parLit ","
       e₄ ← parSExp p
       parLit ","
       e₅ ← parSExp p
       parLit "]"
       return $ PFldRows2PE e₁ e₂ e₃ e₄ e₅
  , do x ← parVar
       parLit "←"
       e₁ ← parPExp p
       parLit ";"
       e₂ ← parPExp p
       return $ BindPE x e₁ e₂
  , do parLit "if"
       e₁ ← parSExp p
       parLit "then"
       parLit "{"
       e₂ ← parPExp p
       parLit "}"
       parLit "else"
       parLit "{"
       e₃ ← parPExp p
       parLit "}"
       return $ IfPE e₁ e₂ e₃
  , do parLit "parallel"
       parLit "["
       e₁ ← parSExp p
       parLit ","
       e₂ ← parSExp p
       parLit "]"
       parLit "{"
       x₁ ← parVar
       parLit "⇒"
       e₃ ← parSExp p
       parLit "}"
       parLit "{"
       x₂ ← parVar
       parLit ","
       x₃ ← parVar
       parLit "⇒"
       e₄ ← parPExp p
       parLit "}"
       return $ ParallelPE e₁ e₂ x₁ e₃ x₂ x₃ e₄
  , case p of
      ED_W → do
        parLit "aloop"
        parLit "["
        e₁ ← parSExp p
        parLit "]"
        e₂ ← parSExp p
        parLit "on"
        e₃ ← parSExp p
        parLit "<"
        xs ← pManySepBy (parLit ",") parVar
        parLit ">"
        parLit "{"
        x₁ ← parVar
        parLit ","
        x₂ ← parVar
        parLit "⇒"
        e₄ ← parPExp p
        parLit "}"
        return $ EDLoopPE e₁ e₂ e₃ xs x₁ x₂ e₄
      _ → abort
  , do parLit "loop"
       e₂ ← parSExp p
       parLit "on"
       e₃ ← parSExp p
       parLit "<"
       xs ← pManySepBy (parLit ",") parVar
       parLit ">"
       parLit "{"
       x₁ ← parVar
       parLit ","
       x₂ ← parVar
       parLit "⇒"
       e₄ ← parPExp p
       parLit "}"
       return $ LoopPE e₂ e₃ xs x₁ x₂ e₄
  , case p of
      ED_W → do
        parLit "mgauss"
        parLit "["
        e₁ ← parSExp p
        parLit ","
        e₂ ← parSExp p
        parLit ","
        e₃ ← parSExp p
        parLit "]"
        parLit "<"
        xs ← pManySepBy (parLit ",") parVar
        parLit ">"
        parLit "{"
        e₄ ← parSExp p
        parLit "}"
        return $ MGaussPE e₁ (EDGaussParams e₂ e₃) xs e₄
      RENYI_W → do
        parLit "mgauss"
        parLit "["
        e₁ ← parSExp p
        parLit ","
        e₂ ← parSExp p
        parLit ","
        e₃ ← parSExp p
        parLit "]"
        parLit "<"
        xs ← pManySepBy (parLit ",") parVar
        parLit ">"
        parLit "{"
        e₄ ← parSExp p
        parLit "}"
        return $ MGaussPE e₁ (RenyiGaussParams e₂ e₃) xs e₄
      TC_W → do
        parLit "mgauss"
        parLit "["
        e₁ ← parSExp p
        parLit ","
        e₂ ← parSExp p
        parLit ","
        e₃ ← parSExp p
        parLit "]"
        parLit "<"
        xs ← pManySepBy (parLit ",") parVar
        parLit ">"
        parLit "{"
        e₄ ← parSExp p
        parLit "}"
        return $ MGaussPE e₁ (TCGaussParams e₂ e₃) xs e₄
      ZC_W → do
        parLit "mgauss"
        parLit "["
        e₁ ← parSExp p
        parLit ","
        e₂ ← parSExp p
        parLit "]"
        parLit "<"
        xs ← pManySepBy (parLit ",") parVar
        parLit ">"
        parLit "{"
        e₄ ← parSExp p
        parLit "}"
        return $ MGaussPE e₁ (ZCGaussParams e₂) xs e₄
      _ → abort
  , case p of
      ED_W → do
        parLit "bgauss"
        parLit "["
        e₁ ← parSExp p
        parLit ","
        e₂ ← parSExp p
        parLit ","
        e₃ ← parSExp p
        parLit "]"
        parLit "<"
        xs ← pManySepBy (parLit ",") parVar
        parLit ">"
        parLit "{"
        e₄ ← parSExp p
        parLit "}"
        return $ BGaussPE e₁ (EDGaussParams e₂ e₃) xs e₄
      RENYI_W → do
        parLit "bgauss"
        parLit "["
        e₁ ← parSExp p
        parLit ","
        e₂ ← parSExp p
        parLit ","
        e₃ ← parSExp p
        parLit "]"
        parLit "<"
        xs ← pManySepBy (parLit ",") parVar
        parLit ">"
        parLit "{"
        e₄ ← parSExp p
        parLit "}"
        return $ BGaussPE e₁ (RenyiGaussParams e₂ e₃) xs e₄
      ZC_W → do
        parLit "bgauss"
        parLit "["
        e₁ ← parSExp p
        parLit ","
        e₂ ← parSExp p
        parLit "]"
        parLit "<"
        xs ← pManySepBy (parLit ",") parVar
        parLit ">"
        parLit "{"
        e₄ ← parSExp p
        parLit "}"
        return $ BGaussPE e₁ (ZCGaussParams e₂) xs e₄
      _ → abort
  , case p of
      EPS_W → do
        parLit "laplace"
        parLit "["
        e₁ ← parSExp p
        parLit ","
        e₂ ← parSExp p
        parLit "]"
        parLit "<"
        xs ← pManySepBy (parLit ",") parVar
        parLit ">"
        parLit "{"
        e₃ ← parSExp p
        parLit "}"
        return $ LaplacePE e₁ (EpsLaplaceParams e₂) xs e₃
      _ → abort
  , case p of
      ED_W → do
        parLit "gauss"
        parLit "["
        e₁ ← parSExp p
        parLit ","
        e₂ ← parSExp p
        parLit ","
        e₃ ← parSExp p
        parLit "]"
        parLit "<"
        xs ← pManySepBy (parLit ",") parVar
        parLit ">"
        parLit "{"
        e₄ ← parSExp p
        parLit "}"
        return $ GaussPE e₁ (EDGaussParams e₂ e₃) xs e₄
      RENYI_W → do
        parLit "gauss"
        parLit "["
        e₁ ← parSExp p
        parLit ","
        e₂ ← parSExp p
        parLit ","
        e₃ ← parSExp p
        parLit "]"
        parLit "<"
        xs ← pManySepBy (parLit ",") parVar
        parLit ">"
        parLit "{"
        e₄ ← parSExp p
        parLit "}"
        return $ GaussPE e₁ (RenyiGaussParams e₂ e₃) xs e₄
      ZC_W → do
        parLit "gauss"
        parLit "["
        e₁ ← parSExp p
        parLit ","
        e₂ ← parSExp p
        parLit "]"
        parLit "<"
        xs ← pManySepBy (parLit ",") parVar
        parLit ">"
        parLit "{"
        e₄ ← parSExp p
        parLit "}"
        return $ GaussPE e₁ (ZCGaussParams e₂) xs e₄
      _ → abort
  , case p of
      ED_W → do
        parLit "exponential"
        parLit "["
        e₁ ← parSExp p
        parLit ","
        e₂ ← parSExp p
        parLit "]"
        e₃ ← parSExp p
        parLit "<"
        xs ← pManySepBy (parLit ",") parVar
        parLit ">"
        parLit "{"
        x ← parVar
        parLit "⇒"
        e₄ ← parSExp p
        parLit "}"
        return $ ExponentialPE e₁ (EDExponentialParams e₂) e₃ xs x e₄
      _ → abort
  , case p of
      EPS_W → do
        parLit "AboveThreshold"
        parLit "["
        e₁ ← parSExp p
        parLit ","
        e₂ ← parSExp p
        parLit ","
        e₃ ← parSExp p
        parLit "]"
        parLit "<"
        xs ← pManySepBy (parLit ",") parVar
        parLit ">"
        parLit "{"
        e₄ ← parSExp p
        parLit "}"
        return $ SVTPE (EPSSVTParams e₁) e₂ e₃ xs e₄
      ED_W → do
        parLit "AboveThreshold"
        parLit "["
        e₁ ← parSExp p
        parLit ","
        e₂ ← parSExp p
        parLit ","
        e₃ ← parSExp p
        parLit "]"
        parLit "<"
        xs ← pManySepBy (parLit ",") parVar
        parLit ">"
        parLit "{"
        e₄ ← parSExp p
        parLit "}"
        return $ SVTPE (EDSVTParams e₁) e₂ e₃ xs e₄
      _ → abort
  , case p of
      ED_W → do
        parLit "rand-resp"
        parLit "["
        e₁ ← parSExp p
        parLit ","
        e₂ ← parSExp p
        parLit "]"
        parLit "<"
        xs ← pManySepBy (parLit ",") parVar
        parLit ">"
        parLit "{"
        e₃ ← parSExp p
        parLit "}"
        return $ RRespPE e₁ e₂ xs e₃
      _ → abort
  , case p of
      ED_W → do
        parLit "sample"
        parLit "["
        e₁ ← parSExp p
        parLit "]"
        e₂ ← parSExp p
        parLit ","
        e₃ ← parSExp p
        parLit "{"
        x₁ ← parVar
        parLit ","
        x₂ ← parVar
        parLit "⇒"
        e₄ ← parPExp p
        parLit "}"
        return $ EDSamplePE e₁ e₂ e₃ x₁ x₂ e₄
      RENYI_W → do
        parLit "sample"
        parLit "["
        e₁ ← parSExp p
        parLit "]"
        e₂ ← parSExp p
        parLit ","
        e₃ ← parSExp p
        parLit "{"
        x₁ ← parVar
        parLit ","
        x₂ ← parVar
        parLit "⇒"
        e₄ ← parPExp p
        parLit "}"
        return $ RenyiSamplePE e₁ e₂ e₃ x₁ x₂ e₄
      TC_W → do
        parLit "sample"
        parLit "["
        e₁ ← parSExp p
        parLit "]"
        e₂ ← parSExp p
        parLit ","
        e₃ ← parSExp p
        parLit "{"
        x₁ ← parVar
        parLit ","
        x₂ ← parVar
        parLit "⇒"
        e₄ ← parPExp p
        parLit "}"
        return $ TCSamplePE e₁ e₂ e₃ x₁ x₂ e₄
      _ → abort
  , do parLit "rand-nat"
       parLit "["
       e₁ ← parSExp p
       parLit ","
       e₂ ← parSExp p
       parLit "]"
       return $ RandNatPE e₁ e₂
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
  , do e ← parSExp p
       case extract e of
         -- QUESTION: should AppPE have a SExp or PExp as its first argument?
         AppSE e₁ e₂ → return $ AppPE e₁ e₂
         _ → abort
  ]

tokSkip ∷ Token → 𝔹
tokSkip = \case
  TokenSpace → True
  TokenComment → True
  _ → False

  -- [ mix $ MixTerminal $ do
  --     void $ pSatisfies "lparen" $ shape eTLParenL
  --     x ← parseExp
  --     void $ pSatisfies "rparen" $ shape eTRParenL
  --     return x
  -- , mix $ MixTerminal  $ EAtom ∘ ASymbol ^$ pShaped "symbol" $ view eTSymbolL
  -- , mix $ MixTerminal  $ EAtom ∘ ANatural ^$ pShaped "natural" $ view eTNaturalL
  -- , mix $ MixInfixR  5 $ const ESum ^$ surroundWhitespace $ pShaped "plus" $ view eTPlusL
  -- , mix $ MixInfixR  6 $ const EProduct ^$ surroundWhitespace $ pShaped "times" $ view eTTimesL
  -- , mix $ MixInfixL  7 $ const EExpo ^$ surroundWhitespace $ pShaped "power" $ view eTPowerL
  -- , mix $ MixPostfix 7 $ const EFact ^$ preWhitespace $ pShaped "fact" $ view eTFactL
  -- , mix $ MixPrefix  8 $ const ENegate ^$ postWhitespace $ pShaped "neg" $ view eTNegativeL
  -- , mix $ MixInfix   5 $ const EEquality ^$ surroundWhitespace $ pShaped "equal" $ view eTEqualL
  -- ]
  -- where
  --   surroundWhitespace ∷ Parser ExpToken a → Parser ExpToken a
  --   surroundWhitespace xM = do
  --     void $ pOptional $ pSatisfies "whitespace" $ shape eTWhitespaceL
  --     x ← xM
  --     void $ pOptional $ pSatisfies "whitespace" $ shape eTWhitespaceL
  --     return x
  --   preWhitespace ∷ Parser ExpToken a → Parser ExpToken a
  --   preWhitespace xM = do
  --     void $ pOptional $ pSatisfies "whitespace" $ shape eTWhitespaceL
  --     xM
  --   postWhitespace ∷ Parser ExpToken a → Parser ExpToken a
  --   postWhitespace xM = do
  --     x ← xM
  --     void $ pOptional $ pSatisfies "whitespace" $ shape eTWhitespaceL
  --     return x
