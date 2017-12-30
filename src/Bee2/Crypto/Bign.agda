module Bee2.Crypto.Bign where

open import Data.ByteString
open import Data.ByteVec
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Agda.Builtin.TrustMe using (primTrustMe)

{-# FOREIGN GHC import qualified Bee2.Defs    #-}
{-# FOREIGN GHC import qualified Bee2.Crypto.Belt    #-}
{-# FOREIGN GHC import qualified Bee2.Crypto.Bign    #-}
{-# FOREIGN GHC import qualified Data.ByteString    #-}

postulate
  SizeT : Set
  -- bignstd128-pri [32] → belt-hash [32] → bign-sig [48]
  bignSign2 : ByteString Strict → ByteString Strict → ByteString Strict
  -- bignstd128-pri [32] → bignstd128-pub [64]
  bignCalcPubkey : ByteString Strict → ByteString Strict

{-# COMPILE GHC SizeT = type (Bee2.Defs.Size) #-}
{-# COMPILE GHC bignSign2 =
    ( \pri hash -> Bee2.Crypto.Bign.bignSign2'bs 128 pri Bee2.Crypto.Belt.hbelt_oid hash ) #-}
{-# COMPILE GHC bignCalcPubkey =
    ( \pri -> Bee2.Crypto.Bign.bignCalcPubkey'bs 128 pri ) #-}
