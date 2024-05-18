{-# OPTIONS --without-K --safe --guardedness --overlapping-instances #-}
module Examples.ActionFormulas where

open import Common.Injectable using ()
open import Common.RegularFormulas using (ActionFormula)
open import Data.Empty using () renaming (⊥-elim to ⊥₀-elim)
open import Data.Sum using (inj₂)
open import Examples.Programs.ATMs using (ATMˢ)
open import Examples.Programs.Effect using (effect⁺; getPINˢ)
open import ModalLogics.ActionFormulas.Base using (Formula; _⊨_)
open import Relation.Binary.PropositionalEquality using (refl)

open ActionFormula
open Formula

property : Formula effect⁺
property = [ act getPINˢ effect⁺ ᶜ ] false

proof : ATMˢ ⊨ property
proof h = ⊥₀-elim (h refl)
