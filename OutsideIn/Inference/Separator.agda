open import OutsideIn.Prelude
open import OutsideIn.X
module OutsideIn.Inference.Separator(x : X) where
  import OutsideIn.Constraints as C
  open C(x)
  open X(x)
  open import Data.List

  data SeparatedConstraint (n : Set) : Set where
    SC : QConstraint n → List (Implication SeparatedConstraint n) → SeparatedConstraint n

  simpl : ∀ {n} → Constraint n Flat → QConstraint n
  simpl (QC c) = c
  simpl (a ∧′ b) = conjConstraint (simpl a) (simpl b)
  simpl (Imp _) = tautologyConstraint

  separate : ∀ {n} → Constraint n Flat → SeparatedConstraint n
  implic : ∀ {n} → Constraint n Flat → List (Implication SeparatedConstraint n)
  implic (QC c) = []
  implic (a ∧′ b) = implic a ++ implic b
  implic (Imp (∃ n · Q ⊃ C)) = (∃ n · Q ⊃ separate C) ∷ []
  separate c = SC (simpl c) (implic c) 

