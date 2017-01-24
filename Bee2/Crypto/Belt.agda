module Bee2.Crypto.Belt where

open import Data.ByteString
open import Data.ByteVec
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Agda.Builtin.TrustMe using (primTrustMe)

postulate
  SizeT : Set
{-# COMPILED_TYPE SizeT (Int) #-}

Password = ByteString Strict
Salt = ByteString Strict
Key = ByteVec {Strict} 16 -- >= 16
-- type EKey = ByteString -- sizeof key + 16
Header = ByteVec {Strict} 16
Kek = ByteVec {Strict} 32

{-# IMPORT Bee2.Crypto.Belt    #-}
postulate
  beltPBKDF′ : ByteString Strict → SizeT → ByteString Strict → ByteString Strict
  fromℕ : ℕ → SizeT

{-# COMPILED beltPBKDF′ 
    ( Bee2.Crypto.Belt.beltPBKDF'bs ) #-}
{-# COMPILED fromℕ 
    ( Prelude.fromIntegral ) #-}

beltPBKDF : Password → ℕ → Salt → Kek
beltPBKDF p n s = (beltPBKDF′ p (fromℕ n) s) , primTrustMe
