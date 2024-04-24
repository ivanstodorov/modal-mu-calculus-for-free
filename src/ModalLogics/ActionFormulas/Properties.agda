{-# OPTIONS --without-K --guardedness #-}
module ModalLogics.ActionFormulas.Properties where

open import Common.Program using (Program; ParameterizedProgram)
open import Data.Container using (Container)
open import Level using (Level)
open import ModalLogics.ActionFormulas.Base using (Formula; _⊩_; _⊩_〔_〕)
open import Relation.Nullary using (Dec; _because_)

open Dec ⦃...⦄

private variable
  ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
  C : Container ℓ₁ ℓ₂
  α : Set ℓ₃

postulate
  ⊩-dec : (f : Formula C) → (x : Program C α) → Dec (f ⊩ x)

⊩-decᵖ : {I : Set ℓ₃} → {O : I → Set ℓ₄} → (f : Formula C) → (x : ParameterizedProgram C I O) → (i : I) → Dec (f ⊩ x 〔 i 〕)
does ⦃ ⊩-decᵖ f x i ⦄ with ⊩-dec f (x i)
... | does because _ = does
proof ⦃ ⊩-decᵖ f x i ⦄ with ⊩-dec f (x i)
... | _ because proof = proof
