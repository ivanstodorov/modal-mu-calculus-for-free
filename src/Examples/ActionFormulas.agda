{-# OPTIONS --without-K --safe --guardedness --overlapping-instances #-}
module Examples.ActionFormulas where

open import Common.Injectable using (inj)
open import Common.RegularFormulas using (ActionFormula)
open import Data.Container using (Shape)
open import Data.Empty using () renaming (⊥-elim to ⊥₀-elim)
open import Examples.Programs.ATMs using (ATMˢ)
open import Examples.Programs.Effect using (effect⁺; IOShape)
open import ModalLogics.ActionFormulas.Base using (Formula; _⊨_)
open import Relation.Binary.PropositionalEquality using (refl)

open ActionFormula
open IOShape
open Formula

property : Formula (Shape effect⁺)
property = [ act inj getPIN effect⁺ ᶜ ] false

proof : ATMˢ ⊨ property
proof h = ⊥₀-elim (h refl)
