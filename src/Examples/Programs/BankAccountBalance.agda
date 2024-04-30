{-# OPTIONS --without-K --safe --guardedness --overlapping-instances #-}
module Examples.Programs.BankAccountBalance where

open import Common.Injectable using ()
open import Common.Program using (Program; free; ⦗_⦘; impure)
open import Data.Bool using (true; false)
open import Data.Product using (_,_)
open import Data.Unit using (⊤)
open import Examples.Programs.Effect using (effect; getCredentialsS; loginS; showBalanceS; logoutS; exceptionP)

bankAccountBalance : Program effect ⊤
free bankAccountBalance = impure (getCredentialsS effect , λ where
  (x , n) → ⦗ impure (loginS effect x n , λ where
    true → ⦗ impure (showBalanceS effect , λ _ → ⦗ impure (logoutS effect , λ _ → bankAccountBalance) ⦘) ⦘
    false → exceptionP) ⦘)
