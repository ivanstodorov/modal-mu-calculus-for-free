{-# OPTIONS --without-K --safe --overlapping-instances #-}
module Examples.Programs.AuthProgramRec where

open import Common.Injectable using ()
open import Common.Program using (RecursiveProgram; callF)
open import Data.Bool using (if_then_else_)
open import Data.Container.FreeMonad using (_>>=_)
open import Data.Nat using (ℕ; suc)
open import Data.Unit using () renaming (⊤ to ⊤₀)
open import Function using (const)
open import Examples.Programs.Effect using (loginF; logoutF; effect)

authProgramRec : RecursiveProgram effect ℕ (const ⊤₀)
authProgramRec n = do
  b ← loginF n
  ( if b
    then logoutF
    else callF (suc n) )
