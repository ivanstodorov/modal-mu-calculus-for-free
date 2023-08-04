module Common.Effect where

open import Data.Bool hiding (_≟_)
open import Data.Sum

record Effect : Set₁ where
  field
    C : Set
    R : C → Set

open Effect

record Decide (e : Effect) : Set₁ where
  field
    _≟_ : C e → C e → Bool

open Decide ⦃ ... ⦄

_⊕_ : Effect → Effect → Effect
C (e₁ ⊕ e₂) = C e₁ ⊎ C e₂
R (e₁ ⊕ e₂) = [ R e₁ , R e₂ ]

instance
  DecidePlus : {e₁ e₂ : Effect} ⦃ _ : Decide e₁ ⦄ ⦃ _ : Decide e₂ ⦄ → Decide (e₁ ⊕ e₂)
  Decide._≟_ DecidePlus (inj₁ l) (inj₁ r) = l ≟ r
  Decide._≟_ DecidePlus (inj₁ _) (inj₂ _) = false
  Decide._≟_ DecidePlus (inj₂ _) (inj₁ _) = false
  Decide._≟_ DecidePlus (inj₂ l) (inj₂ r) = l ≟ r
