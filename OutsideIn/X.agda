open import OutsideIn.Prelude
module OutsideIn.X where
   open import Data.Product public hiding (map) 
   open import Relation.Nullary

   record Types : Set₁ where
     field Type : Set → Set
           type-is-monad : Monad Type
           funType : ∀ {n} → Type n → Type n → Type n
           appType : ∀ {n} → Type n → Type n → Type n
     type-is-functor = Monad.is-functor type-is-monad

   record QConstraints ⦃ types : Types ⦄ : Set₁ where
     open Types(types)
     field QConstraint : Set → Set
           qconstraint-is-functor : Functor QConstraint
           _∼_ : ∀ {n} → Type n → Type n → QConstraint n
           _∧_ : ∀ {n} → QConstraint n → QConstraint n → QConstraint n
           ε : ∀ {n} → QConstraint n
           constraint-types : ∀ {a b} → (Type a → Type b) → QConstraint a → QConstraint b 
           is-ε : ∀ {n} (x : QConstraint n) → Dec (x ≡ ε)
     open Monad   (type-is-monad)
     open Functor (is-functor)
     qc-substitute : ∀{a b} →  (a → Type b) → (QConstraint a → QConstraint b)
     qc-substitute f =  constraint-types (join ∘ map f)

   record AxiomSchemes ⦃ types : Types ⦄ : Set₁ where
     open Types(types)
     field AxiomScheme : Set → Set
           axiomscheme-is-functor : Functor AxiomScheme
           axiomscheme-types : ∀ {a b} → (Type a → Type b) → AxiomScheme a → AxiomScheme b
     open Monad   (type-is-monad)
     open Functor (is-functor)
     ax-substitute : ∀{a b} →  (a → Type b) → (AxiomScheme a → AxiomScheme b)
     ax-substitute f =  axiomscheme-types (join ∘ map f)

   record Entailment ⦃ types : Types ⦄ ⦃ axiomschemes : AxiomSchemes ⦄ ⦃ qconstraints : QConstraints ⦄ : Set₁ where
     open Types(types)
     open AxiomSchemes(axiomschemes)
     open QConstraints(qconstraints)

     open Monad(type-is-monad)
     open Functor(type-is-functor)

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
                                             , constraint-types (join ∘ map θ) q  ⊩ ((join ∘ map θ) τ₁ ∼ (join ∘ map θ) τ₂)
           ent-conj : ∀ {n}{Q : AxiomScheme n}{q q₁ q₂ : QConstraint n}
                           → Q , q ⊩ q₁ → Q , q ⊩ q₂ → Q , q ⊩ (q₁ ∧ q₂)

   module SimplificationPrelude ⦃ types : Types ⦄
                                ⦃ axiomschemes : AxiomSchemes ⦄
                                ⦃ qconstraints : QConstraints ⦄
                                ⦃ entailment   : Entailment   ⦄ where
     open Types(types)
     open AxiomSchemes(axiomschemes)
     open QConstraints(qconstraints)
     open Entailment(entailment)

     data SimplifierResult′ (x : Set)( n m : ℕ ) : QConstraint (x ⨁ m) → Set where
       solved : (q : QConstraint (x ⨁ m)) → (x ⨁ n → Type (x ⨁ m)) → SimplifierResult′ x n m q

     SimplifierResult : Set → ℕ → Set 
     SimplifierResult x n = ∃ (λ m → ∃ (SimplifierResult′ x n m))

     SimplifierResultNoResidual : Set → ℕ → Set
     SimplifierResultNoResidual x n = ∃ (λ m → SimplifierResult′ x n m ε)

     IsSound′ : ∀ {x : Set}{n m : ℕ}{Qr : QConstraint (x ⨁ m)}
                  (Q : AxiomScheme (x ⨁ m))(Qg : QConstraint (x ⨁ m))
                  (Qw : QConstraint (x ⨁ n))(s : SimplifierResult′ x n m Qr) → Set
     IsSound′ Q Qg Qw (solved Qr θ) = Q , Qg ∧ Qr ⊩ qc-substitute θ Qw

     IsSound : ∀ {x : Set}{n : ℕ}
                 (Q : AxiomScheme x)(Qg : QConstraint x)
                 (Qw : QConstraint (x ⨁ n))(s : SimplifierResult x n) → Set
     IsSound {x}{n} Q Qg Qw (m , .Qr , solved Qr θ) = IsSound′ {n = n}{m = m} (Ax-f.map pm-m.unit Q) (Qc-f.map pm-m.unit Qg) Qw (solved Qr θ)
        where module Ax-f = Functor(axiomscheme-is-functor)
              module Qc-f = Functor(qconstraint-is-functor)
              module pm-m = Monad(PlusN-is-monad {m})

   record Simplification ⦃ types : Types ⦄
                         ⦃ axiomschemes : AxiomSchemes ⦄
                         ⦃ qconstraints : QConstraints ⦄
                         ⦃ entailment   : Entailment   ⦄ : Set₁ where
     open Types(types)
     open AxiomSchemes(axiomschemes)
     open QConstraints(qconstraints)
     open Entailment(entailment)
     open SimplificationPrelude

     field simplifier : ∀ {x : Set} → Eq x → (n : ℕ) → AxiomScheme x 
                      → QConstraint x → QConstraint (x ⨁ n) → SimplifierResult x n

     field simplifier-sound : ∀ {x : Set}{n : ℕ}{eq : Eq x}
                 (Q : AxiomScheme x)(Qg : QConstraint x)
                 (Qw : QConstraint (x ⨁ n)) → IsSound Q Qg Qw (simplifier eq n Q Qg Qw) 

     simplifier′ : ∀ {x : Set} → Eq x → (n : ℕ) → AxiomScheme x 
                 → QConstraint x → QConstraint (x ⨁ n) → Ⓢ (SimplifierResultNoResidual x n)
     simplifier′ eq n ax g e with simplifier eq n ax g e 
     simplifier′ eq n ax g e | m , Qr , result with is-ε Qr
     simplifier′ eq n ax g e | m , .ε , result | yes refl = suc (m , result)
     simplifier′ eq n ax g e | m , Qr , result | no  p = zero


   record X : Set₂ where
     field dc : ℕ → Set 
     field types : Types
     field axiom-schemes : AxiomSchemes
     field qconstraints : QConstraints
     field entailment : Entailment
     field simplification : Simplification
     open Types(types) public
     open AxiomSchemes(axiom-schemes) public
     open QConstraints(qconstraints) public
     open Entailment(entailment) public
     open Simplification(simplification) public
     open SimplificationPrelude public
