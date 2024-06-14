{-# OPTIONS --without-K --guardedness --overlapping-instances #-}
module Examples.mCRL2 where

open import Codata.Guarded.Stream using (Stream; _∷_; _++_; repeat)
open import Common.Program using (Program; Programᵖ; free; ⦗_⦘; pure; impure)
open import Data.Container using (Container)
open import Data.Fin using (zero)
open import Data.List using (List; reverse; map)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ; suc; pred; _>_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (const)
open import Level using (0ℓ)
open import ModalLogics.DataParameters.Base using (Formula; Formulaⁱ; Quantifiedⁱ; Parameterizedⁱ; _⊨_; Arguments; M; mᶜ)
open import ModalLogics.DataParameters.RegularFormulas using (ActionFormula; RegularFormula)
open import Relation.Binary.PropositionalEquality using (_≡_)

open Container
open List
open Maybe
open Formulaⁱ
open Quantifiedⁱ hiding (∀〔_〕_)
open Parameterizedⁱ
open Arguments
open M
open ActionFormula hiding (val_)
open RegularFormula
open _≡_

data CommunicationShape : Set where
  send : String → CommunicationShape
  receive : CommunicationShape

communicationEffect : Container 0ℓ 0ℓ
Shape communicationEffect = CommunicationShape
Position communicationEffect (send _) = ⊤
Position communicationEffect receive = String

program : Programᵖ communicationEffect (List String) (const ⊤)
free (program []) = pure tt
free (program (i ∷ is)) = impure (send i , λ _ → ⦗ impure (receive , λ o → program is) ⦘)

-- property₁ : Formula communicationEffect 0ℓ []
-- property₁ = formula ν ℕ ↦ (λ n → quantified formula [ actF (∀〔 String 〕 λ x → (act send x ∪ act receive) ᶜ) ] ref zero ． (n ∷ []) ∧
--                                                     [ actF (∀〔 String 〕 λ x → act send x) ] ref zero ． (suc n ∷ []) ∧
--                                                     [ actF act receive ] (val (n > 0) ∧ ref zero ． (pred n ∷ []))) ． (0 ∷ [])

-- property₁ : Formula communicationEffect 0ℓ []
-- property₁ = formula ν ℕ ↦ (λ n → quantified formula [ actF (∀〔 String 〕 λ x → (act send x ∪ act receive) ᶜ) ] ref zero ． (n ∷ []) ∧
--                                                     [ actF (∀〔 String 〕 λ x → act send x) ] ref zero ． (suc n ∷ []) ∧
--                                                     [ actF act receive ] (val (n > 0) ∧ ref zero ． (pred n ∷ []))) ． (0 ∷ [])

-- -- proof₁ : ∀ {x i} → program (x , i) ⊨ property₁
-- -- Ni proof₁ = zero , {! λ _ _ → ?  !} , {!   !} , {!   !} , {!   !}

tau : Container 0ℓ 0ℓ
Shape tau = ⊤
Position tau _ = ⊤

handler : ∀ {α : Set} → Program communicationEffect α → Program tau (α × List (Maybe String))
handler p = handler' p []
  where
  handler' : ∀ {α} → Program communicationEffect α → List String → Program tau (α × List (Maybe String))
  free (handler' p acc) with free p
  ... | pure a = pure (a , {! acc  !})
  ... | impure (send x , p) = impure (tt , λ _ → handler' (p tt) (x ∷ acc))
  ... | impure (receive , p) with acc
  ...   | [] = {!   !}
  ...   | o ∷ acc = impure (tt , λ _ → handler' {!   !} acc)

-- property₂ : ∀ x i → (handler program) (x , i) ≡ ⦗ pure (reverse (map just i) ++ x) ⦘
-- property₂ x i = {!   !}



-- -- program : Programᵖ communicationEffect (List (Maybe String) × String) (const (List (Maybe String)))
-- -- free (program (x , i)) = impure (send i , λ _ → ⦗ impure (receive , λ o → ⦗ pure (o ∷ x) ⦘) ⦘)

-- -- handler : Programᵖ communicationEffect (List (Maybe String) × String) (const (List (Maybe String))) →
-- --           Programᵖ tau (List (Maybe String) × String) (const (List (Maybe String)))
-- -- handler p x = handler' (p x) []
-- --   where
-- --   handler' : Program communicationEffect (List (Maybe String)) →
-- --              List String → Program tau (List (Maybe String))
-- --   free (handler' p acc) with free p
-- --   ... | pure x = pure x
-- --   ... | impure (send x , p) = impure (tt , λ _ → handler' (p tt) (x ∷ acc))
-- --   ... | impure (receive , p) with acc
-- --   ...   | [] = impure (tt , λ _ → handler' (p nothing) [])
-- --   ...   | o ∷ acc = impure (tt , λ _ → handler' (p (just o)) acc)

-- -- property₂ : ∀ x i → (handler program) (x , i) ≡ ⦗ impure (tt , λ _ → ⦗ impure (tt , λ _ → ⦗ pure (just i ∷ x) ⦘) ⦘) ⦘
-- -- property₂ x i = {! refl  !}
 