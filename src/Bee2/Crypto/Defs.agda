module Bee2.Crypto.Defs where

open import Data.ByteString
open import Data.ByteVec
open import Agda.Builtin.Nat renaming (Nat to ℕ)

{-# FOREIGN GHC import qualified Bee2.Defs    #-}
postulate
  SizeT : Set
  SizeFromℕ : ℕ → SizeT
{-# COMPILE GHC SizeT = type (Bee2.Defs.Size) #-}
{-# COMPILE GHC SizeFromℕ =
    ( Prelude.fromIntegral ) #-}

Hash = ByteVec {Strict} 32

data SecurityLevel : Set where
  l128 l192 l256 : SecurityLevel
