module Common.Effect where

open import Data.Bool using (false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Relation.Binary.PropositionalEquality.Core using (refl)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (does; proof; yes; no; ofʸ; ofⁿ; _because_)

record Effect : Set₁ where
  field
    C : Set
    R : C → Set

open Effect

emptyEffect : Effect
C emptyEffect = ⊥
R emptyEffect c = ⊥-elim c

record Eq (α : Set) : Set where
  field
    _==_ : DecidableEquality α

open Eq ⦃...⦄

instance
  emptyEffectEq : Eq (Effect.C emptyEffect)
  _==_ ⦃ emptyEffectEq ⦄ ()

_:+:_ : Effect → Effect → Effect
C (ε₁ :+: ε₂) = C ε₁ ⊎ C ε₂
R (ε₁ :+: ε₂) = [ R ε₁ , R ε₂ ]

instance
  effectSumEq : {ε₁ ε₂ : Effect} → ⦃ Eq (Effect.C ε₁) ⦄ → ⦃ Eq (Effect.C ε₂) ⦄ → Eq (Effect.C (ε₁ :+: ε₂))
  does (_==_ ⦃ effectSumEq ⦄ (inj₁ c₁) (inj₁ c₂)) with c₁ == c₂
  ... | eq because _ = eq
  proof (_==_ ⦃ effectSumEq ⦄ (inj₁ c₁) (inj₁ c₂)) with c₁ == c₂
  ... | no ¬p = ofⁿ λ {refl → ¬p refl}
  ... | yes refl = ofʸ refl
  does (_==_ ⦃ effectSumEq ⦄ (inj₁ _) (inj₂ _)) = false
  proof (_==_ ⦃ effectSumEq ⦄ (inj₁ _) (inj₂ _)) = ofⁿ λ ()
  does (_==_ ⦃ effectSumEq ⦄ (inj₂ _) (inj₁ _)) = false
  proof (_==_ ⦃ effectSumEq ⦄ (inj₂ _) (inj₁ _)) = ofⁿ λ ()
  does (_==_ ⦃ effectSumEq ⦄ (inj₂ c₁) (inj₂ c₂)) with c₁ == c₂
  ... | eq because _ = eq
  proof (_==_ ⦃ effectSumEq ⦄ (inj₂ c₁) (inj₂ c₂)) with c₁ == c₂
  ... | no ¬p = ofⁿ λ {refl → ¬p refl}
  ... | yes refl = ofʸ refl
