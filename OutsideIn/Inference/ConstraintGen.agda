open import OutsideIn.Prelude
open import OutsideIn.X
module OutsideIn.Inference.ConstraintGen(x : X) where
  import OutsideIn.Constraints as C
  import OutsideIn.TypeSchema as TS
  import OutsideIn.Expressions as E
  import OutsideIn.Environments as V
  open X(x) renaming (funType to _⟶_; appType to _··_)
  open C(x)
  open TS(x)
  open E(x)
  open V(x)
  open import Data.Vec

  private module PlusN-m n        = Monad (PlusN-is-monad {n})
          module PlusN-f n        = Functor (Monad.is-functor (PlusN-is-monad {n}))
          module TypeSchema-f {n} = Functor (type-schema-is-functor {n})
          module Type-f           = Functor (type-is-functor)
          module QC-f             = Functor (qconstraint-is-functor)
          module Exp-f₁ {tv} {r}  = Functor (expression-is-functor₁ {tv} {r})
          module Exp-f₂ {ev} {r}  = Functor (expression-is-functor₂ {ev} {r})
          module Constraint-f {s} = Functor (constraint-is-functor {s}) 
          module Vec-f {n}        = Functor (vec-is-functor {n}) 
          open Monad (type-is-monad) using () renaming (unit to TVar)


  private 

    upindex : {X : Set → Set}{tv : Set} → ⦃ is-functor : Functor X ⦄ → X tv → X (Ⓢ tv)
    upindex ⦃ is-functor ⦄ e = suc <$> e
      where open Functor (is-functor)

    _↑c : {tv : Set}{s : Strata} → (Constraint tv s) → (Constraint (Ⓢ tv) s)
    _↑c {s = s} = upindex ⦃ constraint-is-functor {s} ⦄

    _↑e : {ev tv : Set}{r : Shape} → (Expression ev tv r) → (Expression ev (Ⓢ tv) r)
    _↑e = upindex ⦃ expression-is-functor₂ ⦄

    _↑a : {ev tv : Set}{r : Shape} → (Alternatives ev tv r) → (Alternatives ev (Ⓢ tv) r)
    _↑a = upindex ⦃ alternatives-is-functor₂ ⦄

    _↑t : {tv : Set} → (Type tv) → (Type (Ⓢ tv))
    _↑t = upindex ⦃ type-is-functor ⦄ 

    _↑q : {tv : Set} → (QConstraint tv) → (QConstraint (Ⓢ tv))
    _↑q = upindex ⦃ qconstraint-is-functor ⦄ 
 
    infixr 7 _↑e
    infixr 7 _↑c
    infixr 7 _↑t
    infixr 7 _↑a

    applyAll : ∀{tv}(n : ℕ) → Type tv → Type (tv ⨁ n)
    applyAll zero x = x
    applyAll (suc n) x = applyAll n ((x ↑t) ·· (TVar zero))

    funType : ∀{tv}{n} → Vec (Type tv) n → Type tv → Type tv
    funType [] t = t
    funType (x ∷ xs) t = x ⟶ (funType xs t) 

  genConstraint : {ev : Set}{tv : Set}{r : Shape}
                  (Γ : Environment ev tv)(e : Expression ev tv r)(τ : Type tv) 
                → Constraint tv Extended
  genConstraintAlternative : {ev : Set}{tv : Set}{r : Shape}
                             (Γ : Environment ev tv)(e : Alternative ev tv r)(α β : Type tv) 
                           → Constraint tv Extended
  genConstraintAlternative {ev}{tv} Γ (v →′ e) α β with Γ v
  ... | DC∀ a · τs ⟶ T =  Ⅎ′ a · let C  = genConstraint (Γ′ (Vec-f.map (_↑t) τs) Γ↑) ((Exp-f₂.map (pa.unit) e) ↑e) δ
                                  in (Ⅎ  ((δ ∼′ ((Type-f.map (pa.unit) β) ↑t)) ∧′ C)) ∧′ (applyAll a (TVar T)) ∼′ (Type-f.map (pa.unit) α) 
    where module pa = PlusN-m a
          tv′ = Ⓢ (tv ⨁ a)
          Γ↑ : ∀ {x} → Name ev x → TypeSchema tv′ x
          Γ↑ = (TypeSchema-f.map (pa.unit) ∘ Γ) ↑Γ
          δ : Type tv′
          δ = TVar (zero)
          Γ′ : ∀{n}{ev}{tv} → Vec (Type tv) n → ( Environment ev tv) → Environment (ev ⨁ n) tv
          Γ′ [] Γ = Γ 
          Γ′ (τ ∷ τs) Γ = Γ′ τs (⟨ ∀′ 0 · ε ⇒ τ ⟩, Γ )
  ... |  DC∀′ a , b · Q ⇒ τs ⟶ T = Ⅎ′ a · Ⅎ′ b · let C  = genConstraint (Γ′ (Vec-f.map (_↑t) τs) Γ↑) e↑ δ
                                                  in (Imp (∃ 1 · (Q ↑q) ⊃ (C ∧′ δ ∼′ β↑))) ∧′ 
                                                     Tγ ∼′ α↑ 
    where module pa = PlusN-m a
          module pb = PlusN-m b
          tv′ = Ⓢ ((tv ⨁ a) ⨁ b)             
          Tγ : Type ((tv ⨁ a) ⨁ b)
          Tγ = (Type-f.map pb.unit (applyAll a (TVar T)))
          
          β↑ : Type tv′
          β↑ = (Type-f.map (pb.unit ∘ pa.unit) β) ↑t
          α↑ : Type ((tv ⨁ a) ⨁ b)             
          α↑ = (Type-f.map (pb.unit ∘ pa.unit) α)
          e↑ : Expression _ tv′ _
          e↑ = (Exp-f₂.map (pb.unit ∘ pa.unit) e) ↑e
          Γ↑ : ∀ {x} → Name ev x → TypeSchema tv′ x
          Γ↑ = (TypeSchema-f.map (pb.unit ∘ pa.unit) ∘ Γ) ↑Γ
          δ : Type tv′
          δ = TVar (zero)
          Γ′ : ∀{n}{ev}{tv} → Vec (Type tv) n → ( Environment ev tv) → Environment (ev ⨁ n) tv
          Γ′ [] Γ = Γ 
          Γ′ (τ ∷ τs) Γ = Γ′ τs (⟨ ∀′ 0 · ε ⇒ τ ⟩, Γ ) 
   
  genConstraintAlternatives : {ev : Set}{tv : Set}{r : Shape}
                              (Γ : Environment ev tv)(e : Alternatives ev tv r)(α β : Type tv) 
                            → Constraint tv Extended
  genConstraintAlternatives Γ (esac) α β = ε′
  genConstraintAlternatives Γ (a ∣ as) α β = genConstraintAlternative  Γ a  α β 
                                          ∧′ genConstraintAlternatives Γ as α β
  genConstraint {tv = tv} Γ (Var (DC d)) τ with Γ (DC d)
  ... | DC∀ a · τs ⟶ k = let τ′ = funType τs (applyAll a (TVar k)) 
                           in Ⅎ′ a · Type-f.map (pa.unit) τ ∼′ τ′
   where module pa = PlusN-m a
  ... | DC∀′ a , b · q ⇒ τs ⟶ k = let τ′ = funType τs (Type-f.map (pb.unit) (applyAll a (TVar k))) 
                                    in Ⅎ′ a · Ⅎ′ b · QC q ∧′ Type-f.map (pb.unit ∘ pa.unit) τ ∼′ τ′
   where module pa = PlusN-m a
         module pb = PlusN-m b

  genConstraint Γ (Var (N v)) τ with Γ (N v)
  ... | ∀′ n · q ⇒ t = Ⅎ′ n · QC q ∧′ Type-f.map pn.unit τ ∼′ t
   where module pn = PlusN-m n

  genConstraint Γ (e₁ · e₂) τ = let C₁ = genConstraint (Γ ↑Γ ↑Γ ↑Γ) (e₁ ↑e ↑e ↑e) α₀ 
                                    C₂ = genConstraint (Γ ↑Γ ↑Γ ↑Γ) (e₂ ↑e ↑e ↑e) α₁
                                 in Ⅎ Ⅎ Ⅎ C₁ ∧′ C₂ ∧′ α₀ ∼′ (α₁ ⟶ α₂) ∧′ (τ ↑t ↑t ↑t) ∼′ α₂
    where α₀ = TVar (zero)
          α₁ = TVar (suc zero)
          α₂ = TVar (suc (suc zero))
  genConstraint {ev}{tv} Γ (λ′ e′) τ = let C = genConstraint Γ′ (e′ ↑e ↑e) α₁ 
                                        in Ⅎ Ⅎ C ∧′ (τ ↑t ↑t) ∼′ (α₀ ⟶ α₁)
    where α₀ = TVar (zero)
          α₁ = TVar (suc zero)
          Γ′ : Environment (Ⓢ ev) (tv ⨁ 2)
          Γ′ = ⟨ ∀′ 0 · ε ⇒ α₀ ⟩, Γ ↑Γ ↑Γ
  genConstraint {ev}{tv} Γ (let₁ x in′ y) τ = let C₁ = genConstraint (Γ ↑Γ ↑Γ) (x ↑e ↑e) α₀ 
                                                  C₂ = genConstraint Γ′ (y ↑e ↑e) α₁
                                               in Ⅎ Ⅎ C₁ ∧′ C₂ ∧′ (τ ↑t ↑t) ∼′ α₁
    where α₀ = TVar (zero)
          α₁ = TVar (suc zero)
          Γ′ : Environment (Ⓢ ev) (tv ⨁ 2)
          Γ′ = ⟨ ∀′ 0 · ε ⇒ α₀ ⟩, Γ ↑Γ ↑Γ
  genConstraint {ev}{tv} Γ (let₂ x ∷ t in′ y) τ = let C₁ = genConstraint (Γ ↑Γ ↑Γ) (x ↑e ↑e) α₀
                                                      C₂ = genConstraint Γ′ (y ↑e ↑e) α₁
                                                   in Ⅎ Ⅎ C₁ ∧′ C₂ ∧′ (τ ↑t ↑t) ∼′ α₁ ∧′ 
                                                          α₀ ∼′ (t ↑t ↑t)
    where α₀ = TVar zero
          α₁ = TVar (suc zero)
          Γ′ : Environment (Ⓢ ev) (tv ⨁ 2)
          Γ′ = ⟨ ∀′ 0 · ε ⇒ α₀ ⟩, Γ ↑Γ ↑Γ
  genConstraint {ev}{tv} Γ (let₃ n · x ∷ Q ⇒ t in′ y) τ = let 
                                                            C  = genConstraint ((Γ ↑Γ ↑Γ) ↑nΓ) x′ α₀
                                                            C₂ = genConstraint Γ′ ((y ↑e ↑e) ↑ne) α₁
                                                            C₁ = Imp (∃ 0 · Q′ ⊃ (C ∧′ α₀ ∼′ t′))
                                                          in Ⅎ Ⅎ Ⅎ′ n · C₁ ∧′ C₂ ∧′ 
                                                                        ((τ ↑t ↑t) ↑nt) ∼′ α₁
    where module p2m = PlusN-m 2
          module p2f = PlusN-f 2
          module pnf = PlusN-f n
          module pnm = PlusN-m n
          _↑nΓ : {x : NameType} {ev tv : Set} 
               → (Name ev x → TypeSchema tv x) → (Name ev x → TypeSchema (tv ⨁ n) x)
          _↑nΓ = _∘_ (TypeSchema-f.map pnm.unit)
          _↑ne = Exp-f₂.map pnm.unit
          _↑nt = Type-f.map pnm.unit
          Q′ = (QC-f.map (pnf.map p2m.unit) Q)
          t′ = Type-f.map (pnf.map p2m.unit) t
          x′ = Exp-f₂.map (pnf.map p2m.unit) x
          α₀ : Type ((tv ⨁ 2) ⨁ n)
          α₀ = Type-f.map pnm.unit (TVar zero)
          α₁ : Type ((tv ⨁ 2) ⨁ n)
          α₁ = Type-f.map pnm.unit (TVar (suc zero))
          Γ′ : Environment (Ⓢ ev) ((tv ⨁ 2) ⨁ n)
          Γ′ = TypeSchema-f.map (pnm.unit ∘ p2m.unit) ∘  ⟨ ∀′ n · Q ⇒  t ⟩, Γ
  genConstraint {ev}{tv} Γ (case x of alts)  τ = let C = genConstraint (Γ ↑Γ ↑Γ) (x ↑e ↑e) α₀ 
                                                  in Ⅎ Ⅎ (C ∧′ α₁ ∼′ (τ ↑t ↑t) 
                                                       ∧′ genConstraintAlternatives (Γ ↑Γ ↑Γ) 
                                                                                    (alts ↑a ↑a) 
                                                                                    α₀ α₁)
       where α₀ : Type (tv ⨁ 2)
             α₀ = TVar zero
             α₁ : Type (tv ⨁ 2)
             α₁ = TVar (suc zero)

