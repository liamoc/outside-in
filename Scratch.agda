module Scratch where
  open import OutsideIn.Prelude
  open import OutsideIn.X
  open import OutsideIn.Instantiations.Simple
  import OutsideIn
  data NoDCs : ℕ → Set where

  open OutsideIn(Simple NoDCs)

