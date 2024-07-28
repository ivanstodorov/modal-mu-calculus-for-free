{-# OPTIONS --without-K --guardedness --overlapping-instances #-}
module Examples.EffectHandlers where

open import Common.Program using (Program; free; pure; impure; ⦗_⦘)
open import Data.Container using (Container)
open import Data.Empty using () renaming (⊥-elim to ⊥₀-elim)
open import Data.Fin using (zero)
open import Data.List using (List; _∷ʳ_; reverse)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ; _>_; pred; z≤n; s≤s)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using () renaming (⊤ to ⊤₀; tt to tt₀)
open import Data.Unit.Polymorphic using (tt)
open import Level using (Level; 0ℓ; lift)
open import ModalLogics.DataParameters.Base using (Formula; Formulaⁱ; Quantifiedⁱ; Parameterizedⁱ; Nu; nuᶜ; []; _∷_; _⊨_)
open import ModalLogics.DataParameters.RegularFormulas using (ActionFormula; RegularFormula)
open import Relation.Binary.PropositionalEquality using (_≡_)

open Container
open List
open Maybe
open ℕ
open Formulaⁱ
open Quantifiedⁱ
open Parameterizedⁱ
open Nu
open ActionFormula renaming (val_ to valᵃᶠ_; ∃〔_〕_ to ∃ᵃᶠ〔_〕_)
open RegularFormula
open _≡_

private variable
  ℓ : Level

data CommunicationShape : Set where
  send : String → CommunicationShape
  receive : CommunicationShape

communicationEffect : Container 0ℓ 0ℓ
Shape communicationEffect = CommunicationShape
Position communicationEffect (send _) = ⊤₀
Position communicationEffect receive = String

program : List String → Program communicationEffect ⊤₀
free (program []) = pure tt₀
free (program (i ∷ is)) = impure (send i , λ _ → ⦗ impure (receive , λ _ → program is) ⦘)

property₁ : Formula (Shape communicationEffect) 0ℓ []
property₁ = formula ν ℕ ↦ (λ n → quantified formula [ actF ((∃ᵃᶠ〔 String 〕 λ x → act send x) ∪ act receive) ᶜ ] ref zero ． (n ∷ []) ∧ [ actF ∃ᵃᶠ〔 String 〕 (λ x → act send x) ] ref zero ． (suc n ∷ []) ∧ [ actF act receive ] (val (n > 0) ∧ ref zero ． (pred n ∷ []))) ． (zero ∷ [])

proof₁ : (is : List String) → program is ⊨ property₁
nu (proof₁ []) = zero , (λ { refl → nuᶜ tt }) , (λ { refl → nuᶜ tt }) , (λ { refl → nuᶜ tt }) , λ { refl → nuᶜ tt }
nu (proof₁ (x ∷ is)) = zero , (λ h → ⊥₀-elim (h (inj₁ (x , lift refl)))) , (λ { _ _ refl → nuᶜ (zero , (λ h → ⊥₀-elim (h (inj₂ (lift refl)))) , (λ ()) , (λ { _ _ refl → nuᶜ (lift (s≤s z≤n)) }) , (λ { _ _ refl → proof₁ is })) }) , (λ ()) , λ ()

τ : Container 0ℓ 0ℓ
Shape τ = ⊤₀
Position τ _ = ⊤₀

handler : {α : Set ℓ} → Program communicationEffect α → Program τ (Maybe (α × List String))
handler p = handler' p [] []
  where
  handler' : {α : Set ℓ} → Program communicationEffect α → List String → List String → Program τ (Maybe (α × List String))
  free (handler' p sent received) with free p
  ... | pure a = pure (just (a , received))
  ... | impure (send x , c) = impure (tt₀ , λ _ → handler' (c tt₀) (sent ∷ʳ x) received)
  ... | impure (receive , c) with sent
  ...   | [] = pure nothing
  ...   | x ∷ sent = impure (tt₀ , λ _ → handler' (c x) sent (x ∷ received))

-- property₂ : (is : List String) →  handler (program is) ≡ ⦗ impure (tt₀ , λ _ → ⦗ impure (tt₀ , (λ _ → ⦗ pure (just (tt₀ , reverse is)) ⦘)) ⦘) ⦘
-- property₂ is = {!   !}
