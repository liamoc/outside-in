open import OutsideIn.Prelude
module OutsideIn.X where
   record X : Set₁ where
      field dc : ℕ → Set
      field QConstraint : Set → Set
      field Type : Set → Set
      field qconstraint-is-functor : Functor QConstraint
      field type-is-functor : Functor Type
      field type-is-monad : Monad Type
      field eqConstraint : ∀ {n} → Type n → Type n → QConstraint n
      field conjConstraint : ∀ {n} → Type n → Type n → QConstraint n
      field tautologyConstraint : ∀ {n} → QConstraint n
      field funType : ∀ {n} → Type n → Type n → Type n
      field appType : ∀ {n} → Type n → Type n → Type n
