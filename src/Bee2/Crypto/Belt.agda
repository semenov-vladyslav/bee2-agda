module Bee2.Crypto.Belt where

open import Data.ByteString
open import Data.ByteVec
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Agda.Builtin.TrustMe using (primTrustMe)

import Bee2.Crypto.Defs
open Bee2.Crypto.Defs
open Bee2.Crypto.Defs using (Hash) public

{-# FOREIGN GHC import qualified Bee2.Crypto.Belt    #-}
{-# FOREIGN GHC import qualified Data.ByteString    #-}

Password = ByteString Strict
Salt = ByteString Strict
Key = ByteVec {Strict} 32
Header = ByteVec {Strict} 16
Kek = ByteVec {Strict} 32

{-# FOREIGN GHC import qualified Bee2.Crypto.Belt    #-}
postulate
  primBeltPBKDF : ByteString Strict → SizeT → ByteString Strict → ByteString Strict
  primBeltHash : ByteString Strict → ByteString Strict

{-# COMPILE GHC primBeltPBKDF =
    ( Bee2.Crypto.Belt.beltPBKDF'bs ) #-}
{-# COMPILE GHC primBeltHash =
    ( Bee2.Crypto.Belt.beltHash'bs ) #-}

beltPBKDF : Password → ℕ → Salt → Kek
beltPBKDF p n s = (primBeltPBKDF p (SizeFromℕ n) s) , primTrustMe

beltHash : ByteString Strict → Hash
beltHash bs = primBeltHash bs , primTrustMe
