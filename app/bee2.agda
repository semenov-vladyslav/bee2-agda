module bee2 where

open import Bee2.Crypto.Belt

open import Data.ByteString.Utf8
open import Data.ByteString.IO
open import Data.String using (toList)
open import Data.Product using (proj₁)
open import IO

-- beltPBKDF : Password → ℕ → Salt → Kek

main = run (writeBinaryFile "pbkdf2" (proj₁ (beltPBKDF (packStrict "zed") 1000 (packStrict "salt"))))

