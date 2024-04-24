{-# OPTIONS --without-K --safe --guardedness --overlapping-instances #-}
module Examples.Programs.BankAccountBalanceRec where

open import Common.Injectable using ()
open import Common.Program using (Program; free; ⦗_⦘; impure)
open import Data.Bool using (true; false)
open import Data.Product using (_,_)
open import Data.Unit using (⊤)
open import Examples.Programs.Effect using (effect; inputS; loginS; logoutS)

bankAccountBalanceRec : Program effect ⊤
free bankAccountBalanceRec = impure (inputS effect , λ where
  (x , n) → ⦗ impure (loginS effect x n , λ where
    true → ⦗ impure (logoutS effect , λ _ → bankAccountBalanceRec) ⦘
    false → bankAccountBalanceRec) ⦘)
