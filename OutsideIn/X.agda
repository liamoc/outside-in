open import OutsideIn.Prelude
module OutsideIn.X where
   open import Data.Product public hiding (map) 


   
   module SimpRes(QConstraint : Set → Set)(Type : Set → Set) where

     data SimplifierResult (x : Set)( n : ℕ ) : Set where
       Solved : ∀ {m} → (x ⨁ n → Type (x ⨁ m)) → SimplifierResult x n
       Unsolved : ∀ {m} → QConstraint (x ⨁ m) → (x ⨁ n → Type (x ⨁ m))  
                → SimplifierResult x n

   record X : Set₁ where
      field dc : ℕ → Set

      field Type : Set → Set
            type-is-monad : Monad Type
            funType : ∀ {n} → Type n → Type n → Type n
            appType : ∀ {n} → Type n → Type n → Type n


      field QConstraint : Set → Set
            qconstraint-is-functor : Functor QConstraint
            _∼_ : ∀ {n} → Type n → Type n → QConstraint n
            _∧_ : ∀ {n} → QConstraint n → QConstraint n → QConstraint n
            ε : ∀ {n} → QConstraint n
            constraint-types : ∀ {a b} → (Type a → Type b) → QConstraint a → QConstraint b 


      field AxiomScheme : Set → Set
            axiomscheme-is-functor : Functor AxiomScheme
            axiomscheme-types : ∀ {a b} → (Type a → Type b) → AxiomScheme a → AxiomScheme b 


      open Monad (type-is-monad)
      open Functor (is-functor)
      field _,_⊩_ : ∀ {n} → AxiomScheme n → QConstraint n → QConstraint n → Set
            ent-refl : ∀ {n}{Q : AxiomScheme n}{q q′ : QConstraint n}
                     → Q , (q ∧ q′) ⊩ q′
            ent-trans : ∀ {n}{Q : AxiomScheme n}{q q₁ q₂ q₃ : QConstraint n}
                      → Q , (q ∧ q₁) ⊩ q₂ → Q , (q ∧ q₂) ⊩ q₃ → Q , (q ∧ q₁) ⊩ q₃
            ent-subst : ∀ {a b}{θ : a → Type b}{Q : AxiomScheme a}{q q₁ q₂ : QConstraint a}
                      → Q , (q ∧ q₁) ⊩ q₂ → axiomscheme-types (join ∘ map θ) Q 
                                          , constraint-types (join ∘ map θ) (q ∧ q₁)
                                          ⊩ constraint-types (join ∘ map θ) q₂
            ent-typeq-refl : ∀ {n}{Q : AxiomScheme n}{q : QConstraint n}{τ : Type n}
                           → Q , q ⊩ (τ ∼ τ)
            ent-typeq-sym : ∀ {n}{Q : AxiomScheme n}{q : QConstraint n}{τ₁ τ₂ : Type n}
                          → Q , q ⊩ (τ₁ ∼ τ₂) → Q , q ⊩ (τ₂ ∼ τ₁)
            ent-typeq-trans : ∀ {n}{Q : AxiomScheme n}{q : QConstraint n}{τ₁ τ₂ τ₃ : Type n}
                            → Q , q ⊩ (τ₁ ∼ τ₂) → Q , q ⊩ (τ₂ ∼ τ₃) → Q , q ⊩ (τ₁ ∼ τ₃)
            ent-typeq-subst : ∀ {a b}{Q : AxiomScheme a}{q : QConstraint a}{τ₁ τ₂ : Type a}{θ : a → Type b}
                          → Q , q ⊩ (τ₁ ∼ τ₂) → axiomscheme-types (join ∘ map θ) Q 
                                              , constraint-types (join ∘ map θ) q 
                                              ⊩ ((join ∘ map θ) τ₁ ∼ (join ∘ map θ) τ₂)
            ent-conj : ∀ {n}{Q : AxiomScheme n}{q q₁ q₂ : QConstraint n}
                            → Q , q ⊩ q₁ → Q , q ⊩ q₂ → Q , q ⊩ (q₁ ∧ q₂)

      type-is-functor = Monad.is-functor type-is-monad
      qc-substitute : ∀{a b} →  (a → Type b) → (QConstraint a → QConstraint b)
      qc-substitute f =  constraint-types (join ∘ map f)

      ax-substitute : ∀{a b} →  (a → Type b) → (AxiomScheme a → AxiomScheme b)
      ax-substitute f =  axiomscheme-types (join ∘ map f)



      open SimpRes(QConstraint)(Type) 

      field simplifier : ∀ {x : Set} → Eq x → (n : ℕ) → AxiomScheme (x ⨁ n) 
                       → QConstraint (x ⨁ n) → QConstraint (x ⨁ n) → SimplifierResult x n

      open SimpRes(QConstraint)(Type) public
   