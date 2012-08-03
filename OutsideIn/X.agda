open import OutsideIn.Prelude
module OutsideIn.X where
   open import Data.Product public hiding (map) 


   private
     module SimpRes(QConstraint : Set → Set)(Type : Set → Set) where
       data SimplifierResult (x : Set)( n : ℕ ) : Set where
         Solved : (x ⨁ n → Type x) → SimplifierResult x n
         Unsolved : ∀ {m} → QConstraint (x ⨁ m) → (x ⨁ n → Type (x ⨁ m))  → SimplifierResult x n

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

      open SimpRes(QConstraint)(Type) 

      field simplifier : ∀ {x : Set} → (n : ℕ) → AxiomScheme →  QConstraint (x ⨁ n) →  QConstraint (x ⨁ n) 
                                     → SimplifierResult x n
      open SimpRes(QConstraint)(Type) public

      type-is-functor = Monad.is-functor type-is-monad
      qc-substitute : ∀{a b} →  (a → Type b) → (QConstraint a → QConstraint b)
      qc-substitute f =  constraint-types (join ∘ map f)
         where open Monad (type-is-monad)
               open Functor (type-is-functor)
   