open import OutsideIn.Prelude
open import OutsideIn.X
module OutsideIn.Proof.Soundness(x : X) where
  open X(x)
  import OutsideIn.Environments as EV
  import OutsideIn.Expressions as E
  import OutsideIn.TypeSchema as TS
  import OutsideIn.TopLevel as TL
  open EV(x)
  open E(x)
  open TS(x)
  open TL(x)
  

  module Ax-f = Functor(axiomscheme-is-functor)
  module QC-f = Functor(qconstraint-is-functor)
  module Exp-f {r}{s} = Functor(expression-is-functor₂ {r}{s})
  module TS-f {n} = Functor(type-schema-is-functor {n})
  module pn-m {n} = Monad(PlusN-is-monad{n})


  type-substitute : ∀{a b} → (a → Type b) → Type a → Type b
  type-substitute f t = (join ∘ map f) t 
      where open Monad(type-is-monad)
            open Functor(is-functor)

  applyAll : ∀{tv}(n : ℕ) → Type tv → Type (tv ⨁ n)
  applyAll zero x = x
  applyAll (suc n) x = applyAll n (appType (map suc x) (unit zero))
     where open Monad(type-is-monad)
           open Functor(is-functor)

  constraint-substitute : ∀{a b} → (a → Type b) → QConstraint a → QConstraint b
  constraint-substitute f t = constraint-types (type-substitute f) t 


  open Monad(type-is-monad)
  open Functor(is-functor)
  data _,_,_⊢_∶_ {ev tv : Set}(Q : AxiomScheme tv)(Qg : QConstraint tv)(Γ : Environment ev tv): {r : Shape} → Expression ev tv r →  Type tv → Set where
    TyEq : ∀ {τ₁ τ₂}{r}{e : Expression ev tv r} 
         → Q , Qg , Γ ⊢ e ∶ τ₁ 
         → Q , Qg ⊩ (τ₁ ∼ τ₂) 
         → Q , Qg , Γ ⊢ e ∶ τ₂ 
    Abst : ∀ {τ₁ τ₂}{r}{e : Expression (Ⓢ ev) tv r} 
         → Q , Qg , (⟨ ∀′ 0 · ε ⇒ τ₁ ⟩, Γ) ⊢ e ∶ τ₂ 
         → Q , Qg , Γ ⊢ λ′ e ∶ funType τ₁ τ₂
    Appl : ∀ {τ₁ τ₂}{r₁ r₂}{e₁ : Expression ev tv r₁}{e₂ : Expression ev tv r₂} 
         → Q , Qg , Γ ⊢ e₁ ∶ funType τ₁ τ₂ 
         → Q , Qg , Γ ⊢ e₂ ∶ τ₁ 
         → Q , Qg , Γ ⊢ (e₁ · e₂) ∶ τ₂
    Let1 : ∀ {τ₁ τ₂}{r₁ r₂}{e₁ : Expression ev tv r₁}{e₂ : Expression (Ⓢ ev) tv r₂} 
         → Q , Qg , Γ ⊢ e₁ ∶ τ₁
         → Q , Qg , (⟨ ∀′ 0 · ε ⇒ τ₁ ⟩, Γ) ⊢ e₂ ∶ τ₂
         → Q , Qg , Γ ⊢ (let₁ e₁ in′ e₂) ∶ τ₂
    Let2 : ∀ {τ₁ τ₂}{r₁ r₂}{e₁ : Expression ev tv r₁}{e₂ : Expression (Ⓢ ev) tv r₂} 
         → Q , Qg , Γ ⊢ e₁ ∶ τ₁
         → Q , Qg , (⟨ ∀′ 0 · ε ⇒ τ₁ ⟩, Γ) ⊢ e₂ ∶ τ₂
         → Q , Qg , Γ ⊢ (let₂ e₁ ∷ τ₁ in′ e₂) ∶ τ₂
    Let3 : ∀ {n}{τ₁ τ₂}{r₁ r₂}{Qv}{e₁ : Expression ev (tv ⨁ n) r₁}{e₂ : Expression (Ⓢ ev) tv r₂} 
         → Ax-f.map (pn-m.unit {n}) Q , QC-f.map (pn-m.unit {n}) Qg ∧ Qv , TS-f.map (pn-m.unit {n}) ∘ Γ ⊢ e₁ ∶ τ₁
         → Q , Qg , (⟨ ∀′ n · Qv ⇒ τ₁ ⟩, Γ) ⊢ e₂ ∶ τ₂
         → Q , Qg , Γ ⊢ (let₃ n · e₁ ∷ Qv ⇒ τ₁ in′ e₂) ∶ τ₂
    VarN : ∀ {n}{v}{τ}{Qv}
         → (θ : (tv ⨁ n) → Type tv)
         → Γ v ≡ ∀′ n · Qv ⇒ τ
         → Q , Qg ⊩ constraint-substitute θ Qv 
         → Q , Qg , Γ ⊢ (Var {_}{_}{Regular} v) ∶ type-substitute θ τ 
    DCn1 : ∀ {n}{l}{v}{K}{args}
         → (θ : (tv ⨁ n) → Type tv)
         → Γ v ≡ (DC∀ n · args ⟶ K)
         → Q , Qg , Γ ⊢ (Var {_}{_}{Datacon l} v) ∶ type-substitute θ (applyAll n (unit K)) 
    DCn2 : ∀ {a b}{l}{v}{K}{args}{Qv}
         → (θ : (tv ⨁ a) ⨁ b → Type tv)
         → Γ v ≡ (DC∀′ a , b · Qv ⇒ args ⟶ K)
         → Q , Qg ⊩ constraint-substitute θ Qv       
         → Q , Qg , Γ ⊢ (Var {_}{_}{Datacon l} v) ∶ type-substitute θ (map (pn-m.unit {b}) (applyAll a (unit K)))
    -- CASE

  data _,_,_⊢′_ {ev tv : Set}(Q : AxiomScheme tv)(Qg : QConstraint tv)(Γ : Environment ev tv):  Program ev tv → Set where
    Empty : Q , Qg , Γ ⊢′ end
    Bind1 : {r : Shape}{n : ℕ}{e : Expression ev tv r}{p : Program (Ⓢ ev) tv}{Qv Q₁ : QConstraint (tv ⨁ n)}{τ : Type (tv ⨁ n)}
          → let Q′  = Ax-f.map (pn-m.unit {n}) Q 
                Qg′ = QC-f.map (pn-m.unit {n}) Qg 
                e′  = Exp-f.map (pn-m.unit {n}) e 
         in Q′ , Qv ∧ Qg′ ⊩ Q₁ 
          → Q′ , Q₁ , (TS-f.map (pn-m.unit {n}) ∘ Γ) ⊢ e′ ∶ τ
          → Q , Qg , (⟨ ∀′ n · Qv ⇒ τ  ⟩, Γ) ⊢′ p
          → Q , Qg , Γ ⊢′ bind₁ e , p 
    Bind2 : {r : Shape}{n : ℕ}{e : Expression ev (tv ⨁ n) r}{p : Program (Ⓢ ev) tv}{Qv Q₁ : QConstraint (tv ⨁ n)}{τ : Type (tv ⨁ n)}
          → let Q′  = Ax-f.map (pn-m.unit {n}) Q 
                Qg′ = QC-f.map (pn-m.unit {n}) Qg 
         in Q′ , Qv ∧ Qg′ ⊩ Q₁ 
          → Q′ , Q₁ , (TS-f.map (pn-m.unit {n}) ∘ Γ) ⊢ e ∶ τ 
          → Q , Qg , (⟨ ∀′ n · Qv ⇒ τ ⟩, Γ) ⊢′ p 
          → Q , Qg , Γ ⊢′ bind₂ n · e ∷ Qv ⇒ τ , p     
