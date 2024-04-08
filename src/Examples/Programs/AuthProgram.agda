{-# OPTIONS --without-K --safe --overlapping-instances #-}
module Examples.Programs.AuthProgram where

open import Common.Injectable using ()
open import Common.Program using (Program)
open import Data.Bool using (if_then_else_)
open import Data.Container.FreeMonad using (_>>=_)
open import Data.Nat using (ℕ)
open import Data.Unit using () renaming (⊤ to ⊤₀)
open import Examples.Programs.Effect using (loginF; logoutF; exceptionF; effect)
open import Function using (const)

authProgram : Program effect ℕ (const ⊤₀)
authProgram n = do
  b ← loginF n
  ( if b
    then logoutF
    else exceptionF )

open import Data.Bool using (true; false)
open import Data.Container using (Shape)
open import Data.Empty using () renaming (⊥-elim to ⊥₀-elim)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using () renaming (tt to tt₀)
open import Data.Unit.Polymorphic using (tt)
open import Examples.Programs.Effect using (login; logout; loginS; logoutS; exceptionS)
open import ModalLogics.HennessyMilnerLogic.Base using (Formula; _⊩_〔_〕)
open import Relation.Binary.PropositionalEquality using (refl; _≢_)

open ℕ
open Formula

property₁ : Formula effect
property₁ = [ logoutS effect ] false

test₁ : property₁ ⊩ authProgram 〔 0 〕
test₁ = tt

property₂ : Formula effect
property₂ = ⟨ loginS effect 0 ⟩ ⟨ logoutS effect ⟩ true

test₂ : property₂ ⊩ authProgram 〔 0 〕
test₂ = true , tt₀ , tt

property₃ : Formula effect
property₃ = ⟨ loginS effect 0 ⟩ [ loginS effect 0 ] true

test₃ : property₃ ⊩ authProgram 〔 0 〕
test₃ = false , tt

property₄ : Formula effect
property₄ = ⟨ loginS effect 0 ⟩ [ logoutS effect ] false

test₄ : property₄ ⊩ authProgram 〔 0 〕
test₄ = false , tt

property₅ : Formula effect
property₅ = [ loginS effect 0 ] [ exceptionS effect ] false

test₅ : property₅ ⊩ authProgram 〔 0 〕
test₅ false = ⊥₀-elim
test₅ true = tt

property₆ : Formula effect
property₆ = [ loginS effect 0 ] [ exceptionS effect ] true

test₆ : property₆ ⊩ authProgram 〔 0 〕
test₆ false = ⊥₀-elim
test₆ true = tt

property₇ : ℕ → Formula effect
property₇ n = [ loginS effect n ] false

test₇ : ∀ (n : ℕ) → n ≢ 0 → property₇ n ⊩ authProgram 〔 0 〕
test₇ zero h = ⊥₀-elim (h refl)
test₇ (suc _) h = tt

property₈ : Shape effect → Formula effect
property₈ c = ⟨ loginS effect 0 ⟩ ([ c ] true ∧ [ c ] false)

test₈ : ∀ c → property₈ c ⊩ authProgram 〔 0 〕
test₈ (inj₁ (login _)) = false , tt , tt
test₈ (inj₁ logout) = false , tt , tt
test₈ (inj₂ _) = false , ⊥₀-elim , ⊥₀-elim
