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
    module Ax-f = Functor(axiomscheme-is-functor)
    module Exp-f {ev}{s} = Functor(expression-is-functor₂ {ev}{s})
    module TS-f {x} = Functor(type-schema-is-functor {x})
    module Type-m  = Monad(type-is-monad) 
    module Type-f  = Functor(type-is-functor)
  
  open Type-m

  data _,_►_ {x ev : Set}⦃ eq : Eq x ⦄(Q : AxiomScheme x)(Γ : Environment ev x) : Program ev x → Set where
    Empty : Q , Γ ► end
    BindA : ∀ {r}{m}{e : Expression ev (x ⨁ m) r}{prog : Program (Ⓢ ev) x}{τ}{C : Constraint (x ⨁ m) Extended}{Qc}{f}{f′}
              {C′ : Constraint ((x ⨁ m) ⨁ f) Flat}{r}{C′′ : SeparatedConstraint ((x ⨁ m) ⨁ f) r}{θ : (x ⨁ m) ⨁ f → Type ((x ⨁ m) ⨁ f′)}
         → TS-f.map (PlusN-m.unit {m}) ∘ Γ ► e ∶ τ ↝ C
         → C prenex: f , C′
         → C′ separate: r , C′′
         → let eq′ = PlusN-eq {m} eq in Ax-f.map (PlusN-m.unit {m}) Q , Qc , f solv► C′′ ↝ f′ , ε , θ
         → Q , ⟨ ∀′ m · Qc ⇒ τ ⟩, Γ ► prog
         → Q , Γ ► bind₂ m · e  ∷ Qc ⇒ τ , prog 
    Bind :  ∀{r}{e : Expression ev x r}{prog : Program (Ⓢ ev) x}{C : Constraint (Ⓢ x) Extended}{f}{C′ : Constraint (x ⨁ suc f) Flat}
             {r′}{C′′ : SeparatedConstraint (x ⨁ suc f) r′}{n}{θ : x ⨁ suc f → Type (x ⨁ n)}{Qr}
         → TS-f.map (suc) ∘ Γ ► Exp-f.map suc e ∶ unit zero  ↝ C
         → C prenex: f , C′ 
         → C′ separate: r′ , C′′ 
         → Q , ε , suc f solv► C′′ ↝ n , Qr , θ
         → Q , ⟨ ∀′ n · Qr ⇒ (θ (PlusN-m.unit {f} zero)) ⟩, Γ ► prog
         → Q , Γ ► bind₁ e , prog



  go :  {ev tv : Set}(Q : AxiomScheme tv)(Γ : Environment ev tv) → (eq : Eq tv) → (p : Program ev tv) → Ⓢ (Q , Γ ► p)
  go Q Γ eq (end) = suc Empty
  go {ev}{tv} Q Γ eq (bind₁ e , prog) 
                       with genConstraint {ev}{Ⓢ tv} (TS-f.map suc ∘ Γ) (Exp-f.map suc e) (unit zero) 
  ... | C , prf₁       with prenex C 
  ... | f , C′ , prf₂  with separate C′ 
  ... | r , C′′ , prf₃ with solver eq (suc f) Q ε C′′ 
  ... | zero = zero
  ... | suc (m , Qr , θ , prf₄) with go Q (⟨ ∀′ m · Qr ⇒ (θ (PlusN-m.unit {f} zero)) ⟩, Γ) eq prog
  ... | zero = zero
  ... | suc prf₅ = suc (Bind prf₁ prf₂ prf₃ prf₄ prf₅)
  go Q Γ eq (bind₂ m · e ∷ Qc ⇒ τ , prog) 
                       with genConstraint (TS-f.map (PlusN-m.unit {m}) ∘ Γ) e τ 
  ... | C , prf₁       with prenex C
  ... | f , C′ , prf₂  with separate C′ 
  ... | r , C′′ , prf₃ with solver (PlusN-eq {m} eq) f (Ax-f.map (PlusN-m.unit {m}) Q) Qc C′′ 
  ... | zero = zero
  ... | suc (f′ , Qr , θ , prf₄) with is-ε Qr
  ... | no _ = zero
  ... | yes prf₄′                with go Q (⟨ ∀′ m · Qc ⇒ τ ⟩, Γ) eq prog
  ... | zero = zero
  ... | suc prf₅ = let 
         eq′ =  PlusN-eq {m} eq 
        in suc (BindA prf₁ prf₂ prf₃ (subst (λ Qr → Ax-f.map (PlusN-m.unit {m}) Q , Qc , f solv► C′′ ↝ f′ , Qr , θ  ) prf₄′ prf₄) prf₅)
