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

  simpl : ∀ {n} → Constraint n Flat → QConstraint n
  simpl (QC c) = c
  simpl (a ∧′ b) = conjConstraint (simpl a) (simpl b)
  simpl (Imp _) = tautologyConstraint

  separate : ∀ {n} → Constraint n Flat → ∃ (SeparatedConstraint n)
  implic : ∀ {n} → Constraint n Flat → ∃ (Implications n)
  implic (QC c) = Nullary , imp-ε
  implic (a ∧′ b) with implic a | implic b
  ... | s₁ , v₁ | s₂ , v₂  = Binary s₁ s₂ , (v₁ imp-∧ v₂)
  implic (Imp (∃ n · Q ⊃ C)) with separate C
  ... | s , v = Unary s , imp (∃ n · Q ⊃ v) 
  separate c with implic c 
  ... | s , v = s , SC (simpl c) v

  sequence-Ⓢ : ∀ {m}{b} → ⦃ monad : Monad m ⦄ →  Ⓢ (m b) → m (Ⓢ b)
  sequence-Ⓢ ⦃ m ⦄ (suc n) = map suc n
    where open Functor (Monad.is-functor m)
  sequence-Ⓢ ⦃ m ⦄ (zero) = unit zero
    where open Monad (m)

  sequence-PlusN : ∀ {m}{n}{b} → ⦃ monad : Monad m ⦄ → (m b) ⨁ n → m (b ⨁ n)
  sequence-PlusN {n = zero} x = x
  sequence-PlusN {n = suc n} ⦃ m ⦄ x = sequence-PlusN {n = n}⦃ m ⦄ (PlusN-f.map (sequence-Ⓢ ⦃ m ⦄) x)
    where module PlusN-f = Functor (Monad.is-functor (PlusN-is-monad {n}))

  -- Substitution for separated constraints
  substitute : ∀ {s}{a b} → (a → Type b) → SeparatedConstraint a s → SeparatedConstraint b s
  substituteImp : ∀ {s}{a b} → (a → Type b) → Implications a s → Implications b s
  substitute f (SC qc imps) = SC (constraint-types (join ∘ map f) qc) (substituteImp f imps)
    where open Monad (type-is-monad)
          open Functor (type-is-functor)
  substituteImp f (imp-ε) = imp-ε
  substituteImp {Unary s}{a}{b} f (imp (∃ n · Q ⊃ C)) = imp (∃ n · constraint-types (join ∘ map f′) Q ⊃ substitute f′ C) 
    where module PlusN-f = Functor (Monad.is-functor (PlusN-is-monad {n})) 
          open Monad (type-is-monad)
          open Functor (type-is-functor)
          f′ = sequence-PlusN {n = n} ⦃ type-is-monad ⦄ ∘ PlusN-f.map f

  substituteImp f (a imp-∧ b) = substituteImp f a imp-∧ substituteImp f b
