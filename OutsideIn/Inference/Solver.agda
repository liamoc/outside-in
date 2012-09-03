open import OutsideIn.Prelude
open import OutsideIn.X
module OutsideIn.Inference.Solver(x : X) where  
  import OutsideIn.Inference.Separator as S
  import OutsideIn.Expressions as E
  import OutsideIn.Constraints as C
  open import Data.Bool renaming (_∧_ to _and_)
  open E(x)
  open S(x)
  open X(x)
  open C(x)

  private module PlusN-m {n} = Monad (PlusN-is-monad {n})
          module QC-f = Functor (qconstraint-is-functor)
          module Ax-f = Functor (axiomscheme-is-functor)
          module Type-f = Functor (type-is-functor)
          module Type-m = Monad (type-is-monad)



  solver′ : {x : Set}{s : Shape} → Eq x 
         → (n : ℕ) → AxiomScheme (x ⨁ n) →  QConstraint (x ⨁ n) →  SeparatedConstraint (x ⨁ n) s
         → Bool
  solveImps : {x : Set}{s : Shape} → Eq x → AxiomScheme x →  QConstraint x → Implications x s
            → Bool
  solver′ {x} eq n axioms given (SC simpl imps) with simplifier′ eq n axioms given simpl 
  ... | suc (m , solved .ε θ) = solveImps (PlusN-eq {m} eq) 
                                   (ax-substitute θ axioms) 
                                   (qc-substitute θ given) 
                                   (substituteImp θ imps) 
  ... | zero = false
  solveImps eq axioms given (imp-ε) = true
  solveImps eq axioms given (imp (∃ n · Q ⊃ C)) = solver′ eq n (Ax-f.map (PlusN-m.unit {n}) axioms )
                                                          (QC-f.map (PlusN-m.unit {n}) 
                                                                     given 
                                                           ∧ Q) 
                                                          C
  solveImps eq axioms given (a imp-∧ b) = solveImps eq axioms given a 
                                      and solveImps eq axioms given b 


  solver : {x : Set}{s : Shape} → Eq x 
         → (n : ℕ) → AxiomScheme (x ⨁ n) →  QConstraint (x ⨁ n) →  SeparatedConstraint (x ⨁ n) s
         → Ⓢ (SimplifierResult x n)
  solver {x} eq n axioms given (SC simpl imps) with simplifier eq n axioms given simpl
  ... | m , Qr , solved .Qr θ = if solveImps (PlusN-eq {m} eq) 
                                         (ax-substitute θ axioms) 
                                         (Qr ∧ qc-substitute θ given) 
                                         (substituteImp θ imps) 
                                 then suc (m , Qr , solved Qr θ)
                                 else zero