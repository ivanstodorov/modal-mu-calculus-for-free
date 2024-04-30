{-# OPTIONS --without-K --safe --guardedness --overlapping-instances #-}
module Examples.ActionFormulas where

open import Common.Injectable using ()
open import Common.RegularFormulas using (ActionFormula)
open import Data.Sum using (inj₂)
open import Examples.Programs.BankAccountBalance using (bankAccountBalance)
open import Examples.Programs.Effect using (effect; getCredentialsS)
open import ModalLogics.ActionFormulas.Base using (Formula; _⊩_)
open import Relation.Binary.PropositionalEquality using (refl)

open ActionFormula renaming (¬_ to ¬ᵃᶠ_)
open Formula

property : Formula effect
property = [ ¬ᵃᶠ act getCredentialsS effect ] false

test : property ⊩ bankAccountBalance
test = inj₂ λ h → h refl
