{-# OPTIONS --without-K --safe --guardedness --overlapping-instances #-}
module Examples.Programs.ATM+rec where

open import Common.Injectable using ()
open import Common.Program using (Program; free; impure; ⦗_⦘)
open import Data.Bool using (true; false)
open import Data.Product using (_,_)
open import Data.Unit using (⊤)
open import Examples.Programs.Effect using (effect⁺; getPINˢ; verifyPINˢ; showBalanceˢ)

ATM⁺rec : Program effect⁺ ⊤
free ATM⁺rec = impure (getPINˢ effect⁺ , λ where
  n → ⦗ impure (verifyPINˢ effect⁺ n , λ where
    true → ⦗ impure (showBalanceˢ effect⁺ , (λ _ → ATM⁺rec)) ⦘
    false → ATM⁺rec) ⦘)
