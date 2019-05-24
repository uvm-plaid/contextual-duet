module Duet.UVMHS
  ( module UVMHS
  , module Duet.UVMHS
  ) where

import UVMHS

import qualified Prelude as HS
import qualified GHC.Stats  as HS
import qualified System.Mem as HS
import qualified Data.Time.Clock as Time

infixl 3 ⨺,⨹

type Time = Time.UTCTime
type TimeD = Time.NominalDiffTime

secondsTimeD ∷ TimeD → 𝔻
secondsTimeD = HS.realToFrac

instance Zero TimeD where {zero = HS.fromIntegral 0}
instance Plus TimeD where {(+) = (HS.+)}
instance Additive TimeD
instance One TimeD where {one = HS.fromIntegral 1}
instance Times TimeD where {(×) = (HS.*)}
instance Multiplicative TimeD

(⨺) ∷ Time → Time → TimeD
(⨺) = Time.diffUTCTime

(⨹) ∷ Time → TimeD → Time
(⨹) = flip Time.addUTCTime

now ∷ IO Time
now = Time.getCurrentTime

gc ∷ IO ()
gc = HS.performGC

time ∷ (a → b) → a → IO (b ∧ TimeD)
time f x = do
  gc
  t₁ ← now
  let y = f x
  t₂ ← now
  return $ (y :* t₂ ⨺ t₁)

timeIO ∷ IO a → IO (a ∧ TimeD)
timeIO xM = do
  gc
  t₁ ← now
  x ← xM
  t₂ ← now
  return $ (x :* t₂ ⨺ t₁)

profile ∷ (a → b) → a → IO (TimeD,𝔻)
profile f x = do
  gc
  s₁ ← HS.getRTSStats
  let (n₁,u₁) = (HS.major_gcs s₁,HS.cumulative_live_bytes s₁)
  t₁ ← now
  let _ = f x
  t₂ ← now
  s₂ ← HS.getRTSStats
  let (n₂,u₂) = (HS.major_gcs s₂,HS.cumulative_live_bytes s₂)
  return (t₂ ⨺ t₁,dbl (HS.fromIntegral u₂ - HS.fromIntegral u₁ ∷ ℕ) / dbl (HS.fromIntegral n₂ - HS.fromIntegral n₁ ∷ ℕ))

triplesWith ∷ (ToStream a t₁,ToStream b t₂,ToStream c t₃) ⇒ (a → b → c → d) → t₁ → t₂ → t₃ → 𝑆 d
triplesWith f (stream → 𝑆 s₁₀ g₁) (stream → 𝑆 s₂₀ g₂) (stream → 𝑆 s₃₀ g₃) =
  𝑆 (s₁₀ :* s₂₀ :* s₃₀) $ \ (s₁ :* s₂ :* s₃) → do
    (x :* s₁') ← g₁ s₁
    (y :* s₂') ← g₂ s₂
    (z :* s₃') ← g₃ s₃
    return $ f x y z :* (s₁' :* s₂' :* s₃')

triples ∷ (ToStream a t₁,ToStream b t₂,ToStream c t₃) ⇒ t₁ → t₂ → t₃ → 𝑆 (a ∧ b ∧ c)
triples = triplesWith cons3

cons3 ∷ a → b → c → (a ∧ b ∧ c)
cons3 a b c = a :* b :* c

add3 ∷ (Plus a) ⇒ a → a → a → a
add3 a b c = (a + b) + c

deriving instance (Show a) ⇒ Show (AddTop a)
deriving instance (Show a) ⇒ Show (AddBot a)
deriving instance (Show a) ⇒ Show (AddBT a)

instance (One a) ⇒ One (AddTop a) where
  one = AddTop one
instance (One a) ⇒ One (AddBot a) where
  one = AddBot one

instance (Zero a) ⇒ Zero (AddTop a) where
  zero = AddTop zero
instance (Plus a) ⇒ Plus (AddTop a) where
  Top + _ = Top
  _ + Top = Top
  AddTop x + AddTop y = AddTop $ x + y
instance (Additive a) ⇒ Additive (AddTop a)

instance (Plus a) ⇒ Plus (AddBot a) where
  Bot + y = y
  x + Bot = x
  AddBot x + AddBot y = AddBot $ x + y
instance (Times a) ⇒ Times (AddTop a) where
  Top × _ = Top
  _ × Top = Top
  AddTop x × AddTop y = AddTop $ x × y
instance (Times a) ⇒ Times (AddBot a) where
  Bot × _ = Bot
  _ × Bot = Bot
  AddBot x × AddBot y = AddBot $ x × y
instance (Divide a) ⇒ Divide (AddBot a) where
  Bot / _ = Bot
  _ / Bot = Bot
  AddBot x / AddBot y = AddBot $ x / y
instance (Divide a) ⇒ Divide (AddTop a) where
  Top / _ = Top
  _ / Top = Top
  AddTop x / AddTop y = AddTop $ x / y
instance (Exponential a) ⇒ Exponential (AddBot a) where
  Bot ^ _ = Bot
  _ ^ Bot = Bot
  AddBot x ^ AddBot y = AddBot $ x ^ y
instance (Exponential a) ⇒ Exponential (AddTop a) where
  Top ^ _ = Top
  _ ^ Top = Top
  AddTop x ^ AddTop y = AddTop $ x ^ y
instance (ExponentialFn a) ⇒ ExponentialFn (AddBot a) where
  exp Bot = Bot
  exp (AddBot x) = AddBot $ exp x
instance (ExponentialFn a) ⇒ ExponentialFn (AddTop a) where
  exp Top = Top
  exp (AddTop x) = AddTop $ exp x
instance (Log a) ⇒ Log (AddBot a) where
  log Bot = Bot
  log (AddBot x) = AddBot $ log x
instance (Log a) ⇒ Log (AddTop a) where
  log Top = Top
  log (AddTop x) = AddTop $ log x

instance Zero 𝔹 where zero = False
instance Plus 𝔹 where (+) = (⩔)
instance One 𝔹 where one = True
instance Times 𝔹 where (×) = (⩓)
instance Additive 𝔹
instance Multiplicative 𝔹

instance (Zero a,Zero b) ⇒ Zero (a ∧ b) where zero = zero :* zero
instance (Plus a,Plus b) ⇒ Plus (a ∧ b) where (x₁ :* y₁) + (x₂ :* y₂) = (x₁ + x₂) :* (y₁ + y₂)
instance (One a,One b) ⇒ One (a ∧ b) where one = one :* one
instance (Times a,Times b) ⇒ Times (a ∧ b) where (x₁ :* y₁) × (x₂ :* y₂) = (x₁ × x₂) :* (y₁ × y₂)
instance (Additive a,Additive b) ⇒ Additive (a ∧ b)
instance (Multiplicative a,Multiplicative b) ⇒ Multiplicative (a ∧ b)

truncate ∷ 𝔻 → ℤ
truncate = HS.truncate

abs ∷ ℤ → ℕ
abs = natΩ ∘ HS.abs

ratAbs ∷ ℚ → 𝕋
ratAbs q = rio (abs (ratNum q)) / rio (ratDen q)

fp ∷ (Eq a) ⇒ a → (a → a) → a
fp x f =
  let x' = f x
  in case x' ≡ x of
    True → x' 
    False → fp x' f

instance ToNatO 𝔻 where
  natO d = do
    let z = truncate d
    guard (dbl z ≡ d)
    natO z

instance Show FullContext where show = chars ∘ ppshow

instance Null FullContext where null = FullContext null null null
