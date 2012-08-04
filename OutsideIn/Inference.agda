open import OutsideIn.Prelude
open import OutsideIn.X
module OutsideIn.Inference(x : X) where
  import OutsideIn.TopLevel as TL
  import OutsideIn.TypeSchema as TS
  import OutsideIn.Expressions as E
  import OutsideIn.Environments as V
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
  open V(x)
  open C(x)

  private
    module PlusN-m {n} = Monad(PlusN-is-monad {n})
    module QC-f = Functor(qconstraint-is-functor)
    module Exp-f {ev}{s} = Functor(expression-is-functor₂ {ev}{s})
    module TS-f {x} = Functor(type-schema-is-functor {x})
    module Type-m  = Monad(type-is-monad) 
    module Type-f  = Functor(type-is-functor)

    generate : {ev : Set}{tv : Set}{r : Shape}(Γ : ∀ {x} → Name ev x → TypeSchema tv x)(e : Expression ev tv r)(τ : Type tv)  
                 → ∃ (λ m → ∃ (SeparatedConstraint (tv ⨁ m))) 
    generate Γ e τ with prenex (genConstraint Γ e τ)
    ... | m , c = m , separate c

    generate′ : {ev : Set}{tv : Set}{r : Shape}(Γ : Environment ev tv)(e : Expression ev tv r)
                 → ∃ (λ m → Type (tv ⨁ m) × ∃ (SeparatedConstraint (tv ⨁ m))) 
    generate′ Γ e with prenex (genConstraint (Γ ↑Γ) (Exp-f.map suc e) (Type-m.unit zero))
    ... | m , c = suc m , Type-f.map (PlusN-m.unit {m}) (Type-m.unit zero) , separate c


    solve : ∀ {x : Set}(m : ℕ) → AxiomScheme →  QConstraint x → ∃ (SeparatedConstraint (x ⨁ m)) → Ⓢ (SimplifierResult x m)
    solve {x} m axioms given (s , c) = solver m axioms ( QC-f.map (PlusN-m.unit {m}) given ) c



  open Type-m
  open import Data.Bool

  go :  {ev tv : Set}(Q : AxiomScheme)(Γ : Environment ev tv) → Program ev tv → Bool
  go Q Γ end = true
  go Q Γ (bind₂ n · e ∷ Qc ⇒ τ , prog) with generate (TS-f.map (PlusN-m.unit {n}) ∘ Γ) e τ 
  ... | fuv , C with solve fuv Q Qc C
  ...     | suc (Solved θ) =  go Q (⟨ ∀′ n · Qc ⇒ τ ⟩, Γ) prog
  ...     | _ =  false
  go Q Γ (bind₁ e , prog) with generate′ Γ e  
  ... | fuv , τ , C with solve fuv Q tautologyConstraint C
  ...     | suc (Solved θ) = go Q (⟨ ∀′ 0 · tautologyConstraint ⇒ (τ >>= θ) ⟩, Γ) prog
  ...     | suc (Unsolved {r} Qr θ) = go Q (⟨ ∀′ r · Qr ⇒ (τ >>= θ)⟩, Γ) prog
  ...     | zero = false

 