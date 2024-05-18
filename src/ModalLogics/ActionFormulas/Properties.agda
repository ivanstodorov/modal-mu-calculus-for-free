{-# OPTIONS --without-K --guardedness #-}
module ModalLogics.ActionFormulas.Properties where

open import Common.Program using (Program; ParameterizedProgram)
open import Data.Container using (Container)
open import Level using (Level)
open import ModalLogics.ActionFormulas.Base using (Formula; _⊨_; _▷_⊨_)
open import Relation.Nullary using (Dec; _because_)

open Dec ⦃...⦄

private variable
  ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
  C : Container ℓ₁ ℓ₂
  α : Set ℓ₃

postulate
  ⊨-dec : (x : Program C α) → (f : Formula C) → Dec (x ⊨ f)

⊨-decᵖ : {I : Set ℓ₃} → {O : I → Set ℓ₄} → (i : I) → (x : ParameterizedProgram C I O) → (f : Formula C) → Dec (i ▷ x ⊨ f)
does ⦃ ⊨-decᵖ i x f ⦄ with ⊨-dec (x i) f
... | does because _ = does
proof ⦃ ⊨-decᵖ i x f ⦄ with ⊨-dec (x i) f
... | _ because proof = proof
