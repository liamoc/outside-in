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


  mutual
    data _,_solvI►_ {x : Set}⦃ eq : Eq x ⦄(Q : AxiomScheme x)(Qg : QConstraint x) : {s : Shape} → Implications x s → Set where
      I-ε : Q , Qg solvI► imp-ε
      I-∧ : ∀ {r₁ r₂}{a : Implications x r₁}{b : Implications x r₂} 
          → Q , Qg solvI► a → Q , Qg solvI► b → Q , Qg solvI► (a imp-∧ b)
      I-i : ∀ {r}{n}{Qv}{C : SeparatedConstraint _ r}{n′}{θ}
          → ( let peq = (PlusN-eq {n} eq) in  Q , Qg ∧ Qv , n solv► C ↝ n′ , ε , θ)
          → Q , Qg solvI► imp (∃ n · Qv ⊃ C)
     
    data _,_,_solv►_↝_,_,_ {x : Set}⦃ eq : Eq x ⦄(Q : AxiomScheme x)(Qg : QConstraint x)(n : ℕ) : {s : Shape} → 
                        (SeparatedConstraint (x ⨁ n) s) → (m : ℕ) → (Qr : QConstraint (x ⨁ m)) → (θ : x ⨁ n → Type (x ⨁ m)) → Set where
      SOLVE : ∀ {s}{simpl}{imps : Implications _ s}{m}{Qr}{θ} 
            → simplifier eq n Q Qg simpl ≡ m , Qr , solved Qr θ
            → let peq = (PlusN-eq {m} eq) in (Ax-f.map (PlusN-m.unit {m}) Q) , (Qr ∧ QC-f.map (PlusN-m.unit {m}) Qg) solvI► substituteImp θ imps
            → Q , Qg , n solv► SC simpl imps ↝ m , Qr , θ 

  solveImps : {x : Set}{s : Shape} → (eq : Eq x) → (Q : AxiomScheme x) → (Qg : QConstraint x) → (C : Implications x s)
            → Ⓢ (Q , Qg solvI► C)
  solver′ : {x : Set}{s : Shape} → (eq : Eq x)
          → (n : ℕ) → (Q : AxiomScheme x) → (Qg : QConstraint x) →  (C : SeparatedConstraint (x ⨁ n) s)
          → Ⓢ (∃ (λ m → ∃ (λ θ →  Q , Qg , n solv► C ↝ m , ε , θ)))
  solver′  eq n axioms given (SC simpl imps) with simplifier eq n axioms given simpl | inspect (simplifier eq n axioms given) simpl 
  ... | m , ε? , solved .ε? θ | iC prf with is-ε ε? 
  solver′  eq n axioms given (SC simpl imps) 
      | m , .ε , solved .ε θ | iC prf | yes refl = solveImps (PlusN-eq {m} eq)  
                                                             (Ax-f.map (PlusN-m.unit {m}) axioms) 
                                                             ( ε ∧ QC-f.map (PlusN-m.unit {m}) given) 
                                                             (substituteImp θ imps) 
                                               >>= λ impP →  suc (m , θ , SOLVE prf impP)
       where open Monad(Ⓢ-is-monad)
  ...                        | no isntε = zero 
  solveImps eq Q Qg imp-ε = suc I-ε
  solveImps eq Q Qg (a imp-∧ b) = solveImps eq Q Qg a 
                       >>= λ a′ → solveImps eq Q Qg b
                       >>= λ b′ → suc (I-∧ a′ b′)           
       where open Monad(Ⓢ-is-monad)
  solveImps eq Q Qg (imp (∃ n · Qv ⊃ C)) = solver′ eq n Q (Qg ∧ Qv) C >>= λ { (m , θ , prf) → suc (I-i prf) }
       where open Monad(Ⓢ-is-monad)

  solver : {x : Set}{s : Shape} → (eq : Eq x)
         → (n : ℕ) → (Q : AxiomScheme x) → (Qg : QConstraint x) →  (C : SeparatedConstraint (x ⨁ n) s)
         → Ⓢ (∃ (λ m → ∃ (λ Qr → ∃ (λ θ →  Q , Qg , n solv► C ↝ m , Qr , θ))))
  solver eq n Q Qg (SC simpl imps) with simplifier eq n Q Qg simpl | inspect (simplifier eq n Q Qg) simpl
  ... | m , Qr , solved .Qr θ | iC prf = solveImps (PlusN-eq {m} eq) 
                                                   (Ax-f.map (PlusN-m.unit {m}) Q) 
                                                   (Qr ∧ QC-f.map (PlusN-m.unit {m}) Qg) 
                                                   (substituteImp θ imps) 
                                     >>= λ prf′ → suc (m , Qr , θ , SOLVE prf prf′) 
       where open Monad(Ⓢ-is-monad)