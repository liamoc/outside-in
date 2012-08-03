open import OutsideIn.Prelude
open import OutsideIn.X
module OutsideIn.Inference.Separator(x : X) where
  import OutsideIn.Constraints as C
  open C(x)
  open X(x)
  open import Data.List

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
