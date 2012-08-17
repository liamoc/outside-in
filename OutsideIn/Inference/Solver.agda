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
          module Type-f = Functor (type-is-functor)
          module Type-m = Monad (type-is-monad)

  solver : {x : Set}{s : Shape} 
         → (n : ℕ) → AxiomScheme →  QConstraint (x ⨁ n) →  SeparatedConstraint (x ⨁ n) s
         → Ⓢ (SimplifierResult x n)
  solveImps : {x : Set}{s : Shape} → AxiomScheme →  QConstraint x → Implications x s
            → Bool
  solver {x} n axioms given (SC simpl imps) with simplifier n axioms given simpl
  ... | Solved θ = if solveImps axioms (qc-substitute θ given) (substituteImp θ imps) 
                    then suc (Solved θ) 
                    else zero
  ... | Unsolved {m = m} Qr θ = if solveImps axioms (Qr ∧ qc-substitute θ given) 
                                                    (substituteImp θ imps) 
                                 then suc (Unsolved {m = m} Qr θ) 
                                 else zero
  solveImps axioms given (imp-ε) = true
  solveImps axioms given (imp (∃ n · Q ⊃ C)) with solver n 
                                                         axioms 
                                                         (QC-f.map (PlusN-m.unit {n}) given ∧ Q) 
                                                         C
  ... | suc (Solved θ) = true
  ... | suc (Unsolved Qr θ) = false
  ... | zero = false
  solveImps axioms given (a imp-∧ b) = solveImps axioms given a 
                                   and solveImps axioms given b 