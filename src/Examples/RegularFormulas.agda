{-# OPTIONS --without-K --safe --guardedness #-}
module Examples.RegularFormulas where

open import Common.RegularFormulas using (ActionFormula; RegularFormula)
open import Data.Container using (Shape)
open import Examples.FixedPoints using (proof₄; proof₅)
open import Examples.Programs.ATMs using (ATMˢ)
open import Examples.Programs.ATMs-rec using (ATMˢ-rec)
open import Examples.Programs.Effect using (effect⁺)
open import ModalLogics.RegularFormulas.Base using (Formula; _⊨_)

open ActionFormula
open RegularFormula
open Formula

property : Formula (Shape effect⁺)
property = [ actF true * ] ⟨ actF true ⟩ true

proof₁ : ATMˢ ⊨ ~ property
proof₁ = proof₄

proof₂ : ATMˢ-rec ⊨ property
proof₂ = proof₅
