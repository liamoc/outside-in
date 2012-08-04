open import OutsideIn.Prelude
open import OutsideIn.X
module OutsideIn.Inference(x : X) where
  import OutsideIn.TopLevel as TL
  import OutsideIn.TypeSchema as TS
  import OutsideIn.Expressions as E
  import OutsideIn.Constraints as C
  import OutsideIn.Inference.Solver as S
  import OutsideIn.Inference.Prenexer as P
  import OutsideIn.Inference.Separator as SP
  import OutsideIn.Inference.ConstraintGen as CG
  open S(x)
  open P(x)
  open SP(x)
  open CG(x)
  open X(x)
  open TL(x)
  open TS(x)
  open E(x)
  open C(x)


  module PlusN-m {n} = Monad(PlusN-is-monad {n})
  module QC-f = Functor(qconstraint-is-functor)
  module Exp-f {ev}{s} = Functor(expression-is-functor₂ {ev}{s})
  module TS-f {x} = Functor(type-schema-is-functor {x})
  module Type-m  = Monad(type-is-monad)
  generate : {ev : Set}{tv : Set}{r : Shape}(Γ : ∀ {x} → Name ev x → TypeSchema tv x)(e : Expression ev tv r)(τ : Type tv) 
               → ∃ (λ m → ∃ (SeparatedConstraint (tv ⨁ m))) 
  generate Γ e τ with prenex (genConstraint Γ e τ)
  ... | m , c = m , separate c

  solve : {x : Set} → (n : ℕ) → AxiomScheme →  QConstraint (x ⨁ n) →  ∃ (λ m → ∃ (SeparatedConstraint ((x ⨁ n )⨁ m)))
                    → Ⓢ (∃ (λ m → SimplifierResult (x ⨁ n) m))
  solve n axioms given (m , s , c) with solver m axioms ( QC-f.map (PlusN-m.unit {m}) given ) c
  ... | zero = zero
  ... | suc v = suc (m , v)

  _↑Γ : {x : NameType} {ev tv : Set} → (Name ev x → TypeSchema tv x) → (Name ev x → TypeSchema (Ⓢ tv) x)
  Γ ↑Γ = TS-f.map suc ∘ Γ


  data _,_⊢_ {ev tv : Set}(Q : AxiomScheme)(Γ : ∀ {x} →  Name ev x → TypeSchema tv x){s : Shape} : Program ev tv → Set where
    Empty : Q , Γ ⊢ end 
    BindA : ∀ {s}{n}{e : Expression ev (tv ⨁ n) s}{prog}{Qc}{τ}{m}{θ} 
          → solve n Q Qc (generate (TS-f.map (PlusN-m.unit {n}) ∘ Γ) e τ) ≡ suc (m , Solved θ) 
          → Q , {!!} ⊢ prog
          → Q , Γ ⊢ (bind₂ n · e ∷ Qc ⇒ τ , prog)

    Bind₁ :  ∀ {s}{e : Expression ev tv s}{prog}{Qc}{m}{θ}  
          → solve 0 Q (QC-f.map suc Qc) (generate (Γ ↑Γ) (Exp-f.map suc e) (Type-m.unit zero)) ≡ suc (m , Solved θ)  
          → Q , ? ⊢ prog
          → Q , Γ ⊢ (bind₁ e , prog)