module Bee2.Crypto.Bign where

open import Data.ByteString
open import Data.ByteVec
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Agda.Builtin.TrustMe using (primTrustMe)

open import Bee2.Crypto.Defs

{-# FOREIGN GHC import qualified Bee2.Crypto.Bign    #-}
{-# FOREIGN GHC import qualified Data.ByteString    #-}

postulate
  -- bignstd128-pri [32] → belt-hash [32] → bign-sig [48]
  primBignSign2 : ByteString Strict → ByteString Strict → ByteString Strict
  -- bignstd128-pri [32] → bignstd128-pub [64]
  primBignCalcPubkey : ByteString Strict → ByteString Strict

{-# COMPILE GHC primBignSign2 =
    ( \pri hash -> Bee2.Crypto.Bign.bignSign2'bs 128 pri Bee2.Crypto.Belt.hbelt_oid hash ) #-}
{-# COMPILE GHC primBignCalcPubkey =
    ( \pri -> Bee2.Crypto.Bign.bignCalcPubkey'bs 128 pri ) #-}

Pri = ByteVec {Strict} 32
Pub = ByteVec {Strict} 64 -- TODO: add IsValid
Sig = ByteVec {Strict} 48

bignSign2 : Pri → Hash → Sig
bignSign2 (pri , _) (hash , _) = primBignSign2 pri hash , primTrustMe

bignCalcPubkey : Pri → Pub
bignCalcPubkey (pri , _) = primBignCalcPubkey pri , primTrustMe
