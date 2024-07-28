{-# OPTIONS --without-K --safe --guardedness --overlapping-instances #-}
module Examples.Programs.ATMs-rec where

open import Common.Injectable using (inj)
open import Common.Program using (Program; free; impure; ⦗_⦘)
open import Data.Bool using (false; true)
open import Data.Product using (_,_)
open import Data.Unit using (⊤)
open import Examples.Programs.Effect using (effect⁺; IOShape; VerificationShape; ExceptionShape)

open IOShape
open VerificationShape
open ExceptionShape

ATMˢ-rec : Program effect⁺ ⊤
free ATMˢ-rec = impure (inj getPIN effect⁺ , λ where
  n → ⦗ impure (inj (correctPIN n) effect⁺ , λ where
    false → ATMˢ-rec
    true → ⦗ impure (inj showBalance effect⁺ , λ _ → ATMˢ-rec) ⦘) ⦘)
