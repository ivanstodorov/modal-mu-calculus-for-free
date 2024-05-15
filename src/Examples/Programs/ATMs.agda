{-# OPTIONS --without-K --safe --guardedness --overlapping-instances #-}
module Examples.Programs.ATMs where

open import Common.Injectable using ()
open import Common.Program using (Program; free; impure; ⦗_⦘)
open import Data.Bool using (true; false)
open import Data.Product using (_,_)
open import Data.Unit using (⊤)
open import Examples.Programs.Effect using (effect⁺; getPINˢ; verifyPINˢ; showBalanceˢ; throwExceptionᵖ)

ATMˢ : Program effect⁺ ⊤
free ATMˢ = impure (getPINˢ effect⁺ , λ where
  n → ⦗ impure (verifyPINˢ effect⁺ n , λ where
    true → ⦗ impure (showBalanceˢ effect⁺ , λ _ → ATMˢ) ⦘
    false → throwExceptionᵖ) ⦘)
