module Bee2.Crypto.Belt where

open import Data.ByteString
open import Data.ByteVec
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Agda.Builtin.TrustMe using (primTrustMe)

{-# FOREIGN GHC import qualified Bee2.Defs    #-}
{-# FOREIGN GHC import qualified Data.ByteString    #-}
postulate
  SizeT : Set
{-# COMPILE GHC SizeT = type (Bee2.Defs.Size) #-}

Password = ByteString Strict
Salt = ByteString Strict
Key = ByteVec {Strict} 16 -- >= 16
-- type EKey = ByteString -- sizeof key + 16
Header = ByteVec {Strict} 16
Kek = ByteVec {Strict} 32

{-# FOREIGN GHC import qualified Bee2.Crypto.Belt    #-}
postulate
  beltPBKDF′ : ByteString Strict → SizeT → ByteString Strict → ByteString Strict
  fromℕ : ℕ → SizeT

{-# COMPILE GHC beltPBKDF′ =
    ( Bee2.Crypto.Belt.beltPBKDF'bs ) #-}
{-# COMPILE GHC fromℕ =
    ( Prelude.fromIntegral ) #-}

beltPBKDF : Password → ℕ → Salt → Kek
beltPBKDF p n s = (beltPBKDF′ p (fromℕ n) s) , primTrustMe
