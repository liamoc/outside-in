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
         → (n : ℕ) → AxiomScheme x →  QConstraint x →  SeparatedConstraint (x ⨁ n) s
         → Bool
  solveImps : {x : Set}{n : ℕ}{s : Shape} → Eq x → AxiomScheme x →  QConstraint x → Implications (x ⨁ n) s
            → Bool
  solver′ {x} eq n axioms given (SC simpl imps) with simplifier′ eq n axioms given simpl 
  ... | suc (m , solved .ε θ) = solveImps {n = m} eq axioms given (substituteImp θ imps) 
  ... | zero = false
  solveImps eq axioms given (imp-ε) = true
  solveImps {x}{m}{Unary s} eq axioms given (imp (∃ n · Q ⊃ C)) = solver′ {x ⨁ m}{s} (PlusN-eq {m} eq) n (Ax-f.map (PlusN-m.unit {m}) axioms )
                                                          (QC-f.map (PlusN-m.unit {m}) given ∧ Q) 
                                                          C
  solveImps {x}{n} eq axioms given (a imp-∧ b) = solveImps {x} {n} eq axioms given a 
                                          and solveImps {x} {n} eq axioms given b 


  solver : {x : Set}{s : Shape} → Eq x 
         → (n : ℕ) → AxiomScheme x →  QConstraint x →  SeparatedConstraint (x ⨁ n) s
         → Ⓢ (SimplifierResult x n)
  solver {x} eq n axioms given (SC simpl imps) with simplifier eq n axioms given simpl
  ... | m , Qr , solved .Qr θ = if solveImps {n = 0} (PlusN-eq {m} eq) 
                                         (Ax-f.map (PlusN-m.unit {m}) axioms) 
                                         (Qr ∧ QC-f.map (PlusN-m.unit {m}) given) 
                                         (substituteImp θ imps) 
                                 then suc (m , Qr , solved Qr θ)
                                 else zero