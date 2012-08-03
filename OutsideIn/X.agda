open import OutsideIn.Prelude
module OutsideIn.X where
   open import Data.Product public hiding (map) 
   record X : Set₁ where
      field dc : ℕ → Set

      field Type : Set → Set
            type-is-monad : Monad Type
            funType : ∀ {n} → Type n → Type n → Type n
            appType : ∀ {n} → Type n → Type n → Type n


      field QConstraint : Set → Set
            qconstraint-is-functor : Functor QConstraint
            eqConstraint : ∀ {n} → Type n → Type n → QConstraint n
            conjConstraint : ∀ {n} → QConstraint n → QConstraint n → QConstraint n
            tautologyConstraint : ∀ {n} → QConstraint n
            constraint-types : ∀ {a b} → (Type a → Type b) → QConstraint a → QConstraint b 

      field AxiomScheme : Set 

      field simplifier : ∀ {x : Set} → (n : ℕ) → AxiomScheme →  QConstraint (x ⨁ n) →  QConstraint (x ⨁ n) 
                                     → ∃ (λ m → QConstraint (x ⨁ m) × (x ⨁ n → Type (x ⨁ m)))
      type-is-functor = Monad.is-functor type-is-monad
