module Duet.Pretty where

import UVMHS

import Duet.Syntax
import Duet.Quantity

instance (Pretty e) ⇒ Pretty (Quantity e) where
  pretty Zero = ppKeyPun "⊥"
  pretty (Quantity e) = pretty e
  pretty Inf = ppKeyPun "⊤"

instance (Pretty r) ⇒ Pretty (RowsT r) where
  pretty = \case
    RexpRT r → pretty r
    StarRT → ppKeyPun "★"

instance (Pretty r) ⇒ Pretty (MExp r) where
  pretty = \case
    EmptyME → ppKeyPun "[]"
    VarME x → pretty x
    ConsME τ m → ppAtLevel 6 $ ppSeparated $ list
      [ ppAlign $ pretty τ
      , ppKeyPun "∷"
      , ppAlign $ pretty m
      ]
    AppendME n m → ppAtLevel 3 $ ppSeparated $ list
      [ ppAlign $ pretty n
      , ppKeyPun "⧺"
      , ppBump $ ppAlign $ pretty m
      ]
    RexpME r τ → ppAtLevel 8 $ ppSeparated $ list
      [ ppAlign $ pretty r
      , ppKeyPun "⋅"
      , ppAlign $ pretty τ
      ]

instance Pretty Kind where
  pretty = \case
    ℕK → ppKeyPun "ℕ"
    ℝK → ppKeyPun "ℝ⁺"
    TypeK → ppKeyPun "☆"
    CxtK → ppKeyPun "cxt"

instance Pretty ProgramVar where
  pretty = \case
    TMVar x → concat[ppKeyPun "𝕏ₚₗ",ppPun "[",pretty x,ppPun "]"]
    TLVar x → concat[ppKeyPun "𝕏ₜₗ",ppPun "[",pretty x,ppPun "]"]

instance Pretty Norm where
  pretty = \case
    L1 → ppKeyPun "L1"
    L2 → ppKeyPun "L2"
    LInf → ppKeyPun "L∞"

instance Pretty Clip where
  pretty = \case
    NormClip ℓ → pretty ℓ
    UClip → ppKeyPun "U"

deriving instance (Pretty r) ⇒ Pretty (Sens r)

instance (Pretty r) ⇒ Pretty (Pr p r) where
  pretty = \case
    EpsPriv r → pretty r
    EDPriv r₁ r₂ → pretty $ pretty r₁ :* pretty r₂
    RenyiPriv r₁ r₂ → pretty $ pretty r₁ :* pretty r₂
    ZCPriv r  → pretty r
    TCPriv r₁ r₂ → pretty $ pretty r₁ :* pretty r₂

instance (Pretty r) ⇒ Pretty (Type r) where
  pretty = \case
    ℝˢT r → concat[ppKeyPun "ℝ⁺",ppPun "[",pretty r,ppPun "]"]
    ℕˢT r → concat[ppKeyPun "ℕ",ppPun "[",pretty r,ppPun "]"]
    ℕT → ppKeyPun "ℕ"
    ℝT → ppKeyPun "ℝ"
    𝔹T → ppKeyPun "𝔹"
    𝕊T → ppKeyPun "𝕊"
    𝔻T ℝT → ppKeyPun "𝔻 "
    𝕀T r → concat[ppKeyPun "𝕀",ppPun "[",pretty r,ppPun "]"]
    -- 𝔻𝔽T as → ppAtLevel 2 $ ppSeparated $ list
    --          [ ppKeyPun "𝔻𝔽"
    --          , ppPun "["
    --          , ppAlign $ ppSeparated $ list $ inbetween (ppPun ",") $ mapOn as $ \ (n :* t) →
    --              ppBotLevel $ concat [ppAlign $ ppPun n,ppPun ":",ppAlign $ pretty t]
    --          , ppPun "]"
    --          ]
    -- BagT ℓ c (RecordT as) → ppAtLevel 2 $ ppSeparated $ list
    --          [ ppKeyPun "𝔻𝔽"
    --          , ppPun "["
    --          , ppAlign $ pretty ℓ
    --          , ppSpace 1
    --          , ppAlign $ pretty c
    --          , ppPun "]"
    --          , ppPun "["
    --          , ppAlign $ ppSeparated $ list $ inbetween (ppPun ",") $ mapOn as $ \ (n :* t) →
    --              ppBotLevel $ concat [ppAlign $ ppPun n,ppPun ":",ppAlign $ pretty t]
    --          , ppPun "]"
    --          ]
    -- BagT ℓ c τ → ppAtLevel 5 $ ppSeparated $ list
    --   [ ppKeyPun "Bag"
    --   , ppPun "["
    --   , ppAlign $ pretty ℓ
    --   , ppSpace 1
    --   , ppAlign $ pretty c
    --   , ppPun "]"
    --   , ppBump $ pretty τ
    --   ]
    SetT τ → ppAtLevel 5 $ ppSeparated $ list
      [ ppKeyPun "℘"
      , ppPun "{"
      , ppAlign $ pretty τ
      , ppPun "}"
      ]
    𝔻T τ → ppAtLevel 5 $ ppSeparated $ list
      [ ppKeyPun "𝐝"
      , ppBump $ pretty τ
      ]
    -- RecordT as → ppAtLevel 2 $ ppSeparated $ list
    --          [ ppKeyPun "Record"
    --          , ppPun "["
    --          , ppAlign $ ppSeparated $ list $ inbetween (ppPun ",") $ mapOn as $ \ (n :* t) →
    --              ppBotLevel $ concat [ppAlign $ ppPun n,ppPun ":",ppAlign $ pretty t]
    --          , ppPun "]"
    --          ]
    𝕄T ℓ c ηₘ ηₙ → ppAtLevel 10 $ ppSeparated $ list
      [ concat
        [ ppKeyPun "𝕄 "
        , ppPun "["
        , ppAlign $ pretty ℓ
        , ppPun ","
        , ppAlign $ pretty c
        , ppPun "|"
        , ppAlign $ pretty ηₘ
        , ppPun ","
        , ppAlign $ pretty ηₙ
        , ppPun "]"
        ]
      ]
    τ₁ :⊕: τ₂ → ppAtLevel 5 $ ppSeparated $ list
      [ pretty τ₁
      , ppPun "+"
      , ppBump $ pretty τ₂
      ]
    τ₁ :⊗: τ₂ → ppAtLevel 6 $ ppSeparated $ list
      [ pretty τ₁
      , ppPun "×"
      , ppBump $ pretty τ₂
      ]
    τ₁ :&: τ₂ → ppAtLevel 6 $ ppSeparated $ list
      [ pretty τ₁
      , ppPun "&"
      , ppBump $ pretty τ₂
      ]
    τ₁ :⊸: (ς :* τ₂) → ppAtLevel 2 $ ppSeparated $ list
        -- concat
        -- [ ppPun "∀"
        -- , ppSpace 1
        -- , ppAlign $ ppSeparated $ list $ inbetween (ppPun ",") $ mapOn ακs $ \ (α :* κ) →
        --     ppBotLevel $ concat [ppAlign $ pretty α,ppPun ":",ppAlign $ pretty κ]
        -- ]
        -- , ppPun "."
      [ pretty τ₁
      , ppBotLevel $ concat [ppPun "⊸[",ppAlign $ pretty ς,ppPun "]"]
      , pretty τ₂
      ]
    (x :* τ₁) :⊸⋆: (PEnv pσ :* τ₂) → ppAtLevel 2 $ ppSeparated $ list
      [ ppParens $ ppSeparated $ list [pretty x,ppPun ":",pretty τ₁]
      , ppBotLevel $ concat [ppPun "⊸⋆[",ppAlign $ pretty pσ,ppPun "]"]
      , pretty τ₂
      ]
    ForallT α κ τ → ppAtLevel 2 $ ppSeparated $ list
      [ concat
        [ ppPun "∀"
        , ppSpace 1
        , pretty α
        , ppPun ":"
        , pretty κ
        , ppPun "."
        ]
      , ppNest 2 $ ppAlign $ pretty τ
      ]
    CxtT xs → pretty xs
    BoxedT σ τ → ppAtLevel 5 $ ppSeparated $ list
      [ concat [ ppKeyPun "□" , ppPun "[" ]
      , ppSeparated $ list $ inbetween (ppPun ",") $ mapOn (iter σ) $ \ (x :* Sens q) →
          ppBotLevel $ concat [ppAlign $ pretty x,ppKeyPun "@",ppAlign $ pretty q]
      , ppPun "]"
      , ppBump $ pretty τ
      ]
    VarT x → pretty x
