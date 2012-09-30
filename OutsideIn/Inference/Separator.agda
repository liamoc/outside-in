open import OutsideIn.Prelude
open import OutsideIn.X
module OutsideIn.Inference.Separator(x : X) where
  import OutsideIn.Constraints as C
  open C(x)
  open X(x)
  open import Data.List hiding (map)

  mutual
    data SeparatedConstraint (n : Set) : Shape → Set where
      SC : ∀ {s} → QConstraint n → Implications n s → SeparatedConstraint n s
    data Implications (n : Set) : Shape → Set where
      imp-ε : Implications n Nullary
      imp : ∀ {s} → Implication (λ n → SeparatedConstraint n s) n → Implications n (Unary s)
      _imp-∧_ : ∀ {s₁ s₂} →  Implications n s₁ → Implications n s₂ →  Implications n (Binary s₁ s₂)

  mutual
    data _simpl:_ {n : Set} : Constraint n Flat → QConstraint n → Set where
       Simpl-QC : ∀ {c} → QC c simpl: c
       Simpl-∧  : ∀ {a b}{a′ b′} → a simpl: a′ → b simpl: b′ → (a ∧′ b) simpl: (a′ ∧ b′)
       Simpl-Imp : ∀ {i} → Imp i simpl: ε
    data _separate:_,_ {n : Set} : Constraint n Flat → (r : Shape) → SeparatedConstraint n r → Set where
       Separate : ∀ {C}{Q}{r}{I} → C simpl: Q → C implic: r , I → C separate: r , SC Q I
    data _implic:_,_ {n : Set} : Constraint n Flat → (r : Shape) → Implications n r → Set where
       Implic-Qc : ∀ {c} → QC c implic: Nullary , imp-ε
       Implic-∧ : ∀{a b}{r₁ r₂}{a′}{b′} → a implic: r₁ , a′ → b implic: r₂ , b′ → (a ∧′ b) implic: Binary r₁ r₂ , (a′ imp-∧ b′)
       Implic-I : ∀{n}{Q}{C}{s}{v} → C separate: s , v → Imp (∃ n · Q ⊃ C) implic: Unary s , imp (∃ n · Q ⊃ v)
  
  simpl : ∀ {n} → (C : Constraint n Flat) → ∃ (λ Q → C simpl: Q)
  simpl (QC c) = _ , Simpl-QC
  simpl (a ∧′ b) with simpl a | simpl b
  ... | q₁ , p₁ | q₂ , p₂ = _ , Simpl-∧ p₁ p₂
  simpl (Imp _) = _ , Simpl-Imp 

  separate : ∀ {n} → (C : Constraint n Flat) → ∃ (λ r → ∃ (λ S → C separate: r , S))
  implic : ∀ {n} → (C : Constraint n Flat) → ∃ (λ r → ∃ (λ I →  C implic: r , I ))
  separate c with implic c | simpl c
  ... | s , v , p | q , p′ = _ , _ , Separate p′ p
  implic (QC c) = _ , _ , Implic-Qc 
  implic (a ∧′ b) with implic a | implic b
  ... | s , v , p | s′ , v′ , p′ = _ , _ , Implic-∧ p p′
  implic (Imp (∃ n · Q ⊃ C)) with separate C
  ... | s , v , p = _ , _ , Implic-I p

  -- Substitution for separated constraints
  substituteSep : ∀ {s}{a b} → (a → Type b) → SeparatedConstraint a s → SeparatedConstraint b s
  substituteImp : ∀ {s}{a b} → (a → Type b) → Implications a s → Implications b s
  substituteSep f (SC qc imps) = SC (qc-substitute f qc) (substituteImp f imps)
    where open Monad (type-is-monad)
          open Functor (type-is-functor)
  substituteImp f (imp-ε) = imp-ε
  substituteImp {Unary s} f (imp (∃ n · Q ⊃ C)) = imp (∃ n · constraint-types (join ∘ map f) Q
                                                           ⊃ substituteSep f′ C) 
    where module PlusN-f = Functor (Monad.is-functor (PlusN-is-monad {n})) 
          open Monad (type-is-monad)
          open Functor (type-is-functor)
          f′ = sequence-PlusN {n = n} ⦃ type-is-monad ⦄ ∘ PlusN-f.map f

  substituteImp f (a imp-∧ b) = substituteImp f a imp-∧ substituteImp f b
