open import OutsideIn.Prelude
open import OutsideIn.X
module OutsideIn.Inference.Solver(x : X) where  
  import OutsideIn.Inference.Separator as S
  import OutsideIn.Expressions as E
  open E(x)
  open S(x)
  open X(x)


  -- TODO deal with implications, not obviously structurally recursive, will probably need to alter SeparatedConstraint.
  solver : ∀ {x : Set} → (n : ℕ) → AxiomScheme →  QConstraint (x ⨁ n) →  SeparatedConstraint (x ⨁ n)
                       → Ⓢ (∃ (λ m → QConstraint (x ⨁ m) × (x ⨁ n → Type (x ⨁ m))))
  solver n axioms given (SC simpl imps)  = let (m , Qr , theta) = simplifier n axioms given simpl 
                                            in suc (m , Qr , theta )