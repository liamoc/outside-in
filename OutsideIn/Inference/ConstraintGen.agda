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

    upType : ∀ {n}{tv} → Type tv → Type (tv ⨁ n)
    upType {n} t = Type-f.map (Monad.unit (PlusN-is-monad {n})) t 
    upGamma : ∀ {n}{ev}{tv} → Environment ev tv → Environment ev (tv ⨁ n)
    upGamma {n} Γ = TypeSchema-f.map (Monad.unit (PlusN-is-monad {n})) ∘ Γ 
    upExp : ∀ {n}{ev}{tv}{r} → Expression ev tv r → Expression ev (tv ⨁ n) r
    upExp {n} e = Exp-f₂.map (Monad.unit (PlusN-is-monad {n})) e
    upAlts : ∀ {n}{ev}{tv}{r} → Alternatives ev tv r → Alternatives ev (tv ⨁ n) r
    upAlts {n} e = Functor.map alternatives-is-functor₂ (Monad.unit (PlusN-is-monad {n})) e

  mutual

    syntax alternativeConstraintGen Γ α₀ α₁ alt C = Γ ►′ alt ∶ α₀ ⟶ α₁ ↝ C
    data alternativeConstraintGen {ev : Set}{tv : Set}(Γ : Environment ev tv)(α₀ α₁ : Type tv) : 
                                   {r : Shape} → Alternative ev tv r → Constraint tv Extended → Set where
      Simple : ∀ {r}{n}{v : Name ev (Datacon n)}{e : Expression _ _ r}{a}{τs}{T}{C}             
             → let δ = TVar zero
            in Γ v ≡ DC∀ a · τs ⟶ T
             → addAll (Vec-f.map (_↑t) τs) (upGamma {a} Γ ↑Γ) ► (upExp {a} e ↑e) ∶ δ ↝ C 
             → Γ ►′ v →′ e ∶ α₀ ⟶ α₁ ↝ Ⅎ′ a · (Ⅎ δ ∼′ (upType {a} α₁ ↑t) ∧′ C) ∧′ applyAll a (TVar T) ∼′ upType {a} α₀
      GADT : ∀ {r}{n}{v : Name ev (Datacon n)}{e : Expression _ _ r}{a}{b}{Q}{τs}{T}{C}             
           → let δ = TVar zero
          in Γ v ≡ DC∀′ a , b · Q ⇒ τs ⟶ T
           →   addAll (Vec-f.map (_↑t) τs) (upGamma {b} (upGamma {a} Γ) ↑Γ) 
             ► (upExp {b} (upExp {a} e) ↑e) ∶ δ ↝ C 
           → Γ ►′ v →′ e ∶ α₀ ⟶ α₁ ↝ Ⅎ′ a · Ⅎ′ b · (Imp′ Q (Ⅎ (C ∧′ δ ∼′ (upType {b} (upType {a} α₁) ↑t))))
                                                  ∧′ upType {b} (upType {a} α₀) ∼′ Type-f.map (PlusN-m.unit b) (applyAll a (TVar T))
      
    syntax alternativesConstraintGen Γ α₀ α₁ alts C = Γ ►► alts ∶ α₀ ⟶ α₁ ↝ C
    data alternativesConstraintGen {ev : Set}{tv : Set}(Γ : Environment ev tv)(α₀ α₁ : Type tv) : 
                                   {r : Shape} → Alternatives ev tv r → Constraint tv Extended → Set where
      NoAlternative : Γ ►► esac ∶ α₀ ⟶ α₁ ↝ ε′ 
      AnAlternative : ∀ {r₁ r₂}{a : Alternative _ _ r₁}{as : Alternatives _ _ r₂}{C₁}{C₂} 
                    → Γ ►′ a      ∶ α₀ ⟶ α₁ ↝ C₁
                    → Γ ►► as     ∶ α₀ ⟶ α₁ ↝ C₂ 
                    → Γ ►► a ∣ as ∶ α₀ ⟶ α₁ ↝ C₂  

    syntax constraintGen a c b d = a ► b ∶ c ↝ d
    data constraintGen {ev : Set}{tv : Set}
                       (Γ : Environment ev tv)(τ : Type tv) : {r : Shape} → 
                       Expression ev tv r → Constraint tv Extended → Set where
      VarCon₁ : ∀ {v}{n}{q}{t} 
              → Γ (N v) ≡ ∀′ n · q ⇒ t 
              → Γ ► Var (N v) ∶ τ ↝ Ⅎ′ n · QC q ∧′ upType {n} τ ∼′ t
      VarCon₂ : ∀ {n}{d}{a}{τs : Vec _ n}{k}
              → Γ (DC d) ≡ DC∀ a · τs ⟶ k
              → Γ ► Var (DC d) ∶ τ ↝ Ⅎ′ a · upType {a} τ ∼′ funType τs (applyAll a (TVar k))
      VarCon₃ : ∀ {n}{d}{a}{b}{Q}{τs : Vec _ n}{k}
              → Γ (DC d) ≡ DC∀′ a , b · Q ⇒ τs ⟶ k
              → Γ ► Var (DC d) ∶ τ ↝ Ⅎ′ a · Ⅎ′ b ·
                                       QC Q ∧′ upType {b} (upType {a} τ) ∼′ funType τs (upType {b} (applyAll a (TVar k)))  
      App     : ∀ {r₁}{r₂}{e₁ : Expression _ _ r₁}{e₂ : Expression _ _ r₂}{C₁}{C₂}
              → let α₀ = TVar zero
                    α₁ = TVar (suc zero)
                    α₂ = TVar (suc (suc zero))
                 in upGamma {3} Γ ► upExp {3} e₁ ∶ α₀ ↝ C₁
                  → upGamma {3} Γ ► upExp {3} e₂ ∶ α₁ ↝ C₂
                  → Γ ► e₁ · e₂ ∶ τ ↝ Ⅎ Ⅎ Ⅎ C₁ ∧′ C₂ ∧′ α₀ ∼′ (α₁ ⟶ α₂) ∧′ upType {3} τ ∼′ α₂
      Abs :  ∀ {r}{e : Expression _ _ r}{C}
              → let α₀ = TVar zero
                    α₁ = TVar (suc zero)
                 in ⟨ ∀′ 0 · ε ⇒ α₀ ⟩, upGamma {2} Γ ► upExp {2} e ∶ α₁ ↝ C
                  → Γ ► λ′ e ∶ τ ↝ Ⅎ Ⅎ C ∧′ upType {2} τ ∼′ (α₀ ⟶ α₁)
      Let : ∀{r₁}{r₂}{x : Expression _ _ r₁}{y : Expression _ _ r₂}{C₁}{C₂}
          → let α₀ = TVar zero
                α₁ = TVar (suc zero)
             in                    upGamma {2} Γ ► upExp {2} x ∶ α₀ ↝ C₁ 
              → ⟨ ∀′ 0 · ε ⇒ α₀ ⟩, upGamma {2} Γ ► upExp {2} y ∶ α₁ ↝ C₂
              → Γ ► let₁ x in′ y ∶ τ ↝ Ⅎ Ⅎ C₁ ∧′ C₂ ∧′ upType {2} τ ∼′ α₁
      LetA : ∀{r₁}{r₂}{x : Expression _ _ r₁}{y : Expression _ _ r₂}{t}{C₁}{C₂}
           → let α₀ = TVar zero
                 α₁ = TVar (suc zero)
              in                    upGamma {2} Γ ► upExp {2} x ∶ α₀ ↝ C₁ 
               → ⟨ ∀′ 0 · ε ⇒ α₀ ⟩, upGamma {2} Γ ► upExp {2} y ∶ α₁ ↝ C₂
               → Γ ► let₂ x ∷ t in′ y ∶ τ ↝ Ⅎ Ⅎ C₁ ∧′ C₂ ∧′ upType {2} τ ∼′ α₁ ∧′ upType {2} t ∼′ α₀
      GLetA : ∀{n}{r₁}{r₂}{x : Expression _ _ r₁}{y : Expression _ _ r₂}{Q}{t}{C}{C₂}
           → let α₀ = upType {n} (TVar zero)
                 α₁ = upType {n} (TVar (suc zero))
                 up2 = PlusN-f.map n (PlusN-m.unit 2)
              in                     upGamma {n} (upGamma {2} Γ) ► Exp-f₂.map up2 x ∶ α₀ ↝ C              
               → upGamma {n} (upGamma {2} (⟨ ∀′ n · Q ⇒ t ⟩, Γ)) ► upExp {n} (upExp {2} y) ∶ α₁ ↝ C₂
               → Γ ► let₃ n · x ∷ Q ⇒ t in′ y ∶ τ ↝ Ⅎ Ⅎ Ⅎ′ n · Imp′ (QC-f.map up2 Q)  (C ∧′ α₀ ∼′ Type-f.map up2 t)
                                                            ∧′ C₂ ∧′ upType {n} (upType {2} τ) ∼′ α₁
      Case : ∀{r₁}{r₂}{x : Expression _ _ r₁}{alts : Alternatives _ _ r₂}{C₁}{C₂}
           → let α₀ = TVar zero
                 α₁ = TVar (suc zero)
              in upGamma {2} Γ ► upExp {2} x ∶ α₀ ↝ C₁
               → upGamma {2} Γ ►► upAlts {2} alts ∶ α₀ ⟶ α₁ ↝ C₂ 
               → Γ ► case x of alts ∶ τ ↝ Ⅎ Ⅎ C₁ ∧′ C₂ 


  genConstraint : {ev : Set}{tv : Set}{r : Shape}
                  (Γ : Environment ev tv)(e : Expression ev tv r)(τ : Type tv) → ∃ (λ C → Γ ► e ∶ τ ↝ C)
  genConstraintAlternative : {ev : Set}{tv : Set}{r : Shape} (Γ : Environment ev tv)(a : Alternative ev tv r)(α₀ α₁ : Type tv)
                           → ∃ (λ C → Γ ►′ a ∶ α₀ ⟶ α₁ ↝ C)
  genConstraintAlternative Γ (n →′ e) α₀ α₁ with Γ n | inspect Γ n 
  ... | DC∀ a · τs ⟶ k | iC p with genConstraint (addAll (Vec-f.map _↑t τs) (upGamma {a} Γ ↑Γ)) (upExp {a} e ↑e) (TVar zero)
  ...                          | C , p₂ = _ , Simple p p₂
  genConstraintAlternative Γ (n →′ e) α₀ α₁ 
      | DC∀′ a , b · Q ⇒ τs ⟶ k | iC p with genConstraint (addAll (Vec-f.map _↑t τs) (upGamma {b} (upGamma {a} Γ) ↑Γ)) 
                                                           (upExp {b} (upExp {a} e) ↑e) 
                                                           (TVar zero) 
  ...                                   | C , p₂ = _ , GADT p p₂
  genConstraintAlternatives : {ev : Set}{tv : Set}{r : Shape} (Γ : Environment ev tv)(a : Alternatives ev tv r)(α₀ α₁ : Type tv)
                            → ∃ (λ C → Γ ►► a ∶ α₀ ⟶ α₁ ↝ C)
  genConstraintAlternatives Γ esac α₀ α₁ = _ , NoAlternative
  genConstraintAlternatives Γ (a ∣ as) α₀ α₁ with genConstraintAlternative Γ a α₀ α₁ | genConstraintAlternatives Γ as α₀ α₁ 
  ... | C₁ , p₁ | C₂ , p₂ = _ , AnAlternative p₁ p₂
  genConstraint  Γ (Var (N v)) τ with Γ (N v) | inspect Γ (N v)
  ... | ∀′ n · q ⇒ t | iC prf = _ , VarCon₁ prf 
  genConstraint  Γ (Var (DC d)) τ with Γ (DC d) | inspect Γ (DC d)
  ... | DC∀  a · τs ⟶ k         | iC prf = _ , VarCon₂ prf 
  ... | DC∀′ a , b · q ⇒ τs ⟶ k | iC prf = _ , VarCon₃ prf 
  genConstraint Γ (e₁ · e₂) τ with genConstraint (upGamma {3} Γ) (upExp {3} e₁) (TVar zero) 
                                 | genConstraint (upGamma {3} Γ) (upExp {3} e₂) (TVar (suc zero))
  ... | C₁ , p₁ | C₂ , p₂ = _ , App p₁ p₂
  genConstraint Γ (λ′ e′) τ with genConstraint (⟨ ∀′ 0 · ε ⇒ TVar zero ⟩, upGamma {2} Γ) (upExp {2} e′) (TVar (suc zero)) 
  ... | C , p = _ , Abs p
  genConstraint  Γ (let₁ x in′ y) τ with genConstraint (upGamma {2} Γ) (upExp {2} x) (TVar zero) 
                                       | genConstraint (⟨ ∀′ 0 · ε ⇒ TVar zero ⟩, upGamma {2} Γ) (upExp {2} y) (TVar (suc zero)) 
  ... | C₁ , p₁ | C₂ , p₂ = _ , Let p₁ p₂
  genConstraint Γ (let₂ x ∷ t in′ y) τ with genConstraint (upGamma {2} Γ) (upExp {2} x) (TVar zero) 
                                       | genConstraint (⟨ ∀′ 0 · ε ⇒ TVar zero ⟩, upGamma {2} Γ) (upExp {2} y) (TVar (suc zero)) 
  ... | C₁ , p₁ | C₂ , p₂ = _ , LetA p₁ p₂
  genConstraint Γ (let₃ n · x ∷ Q ⇒ t in′ y) τ with genConstraint (upGamma {n} (upGamma {2} Γ)) 
                                                                  (Exp-f₂.map (PlusN-f.map n (PlusN-m.unit 2)) x) 
                                                                  (upType {n} (TVar zero)) 
                                                  | genConstraint (upGamma {n} (upGamma {2} (⟨ ∀′ n · Q ⇒ t ⟩, Γ)))
                                                                  (upExp {n} (upExp {2} y))
                                                                  (upType {n} (TVar (suc zero)))   
  ... | C₁ , p₁ | C₂ , p₂ = _ , GLetA p₁ p₂
  genConstraint Γ (case x of alts) τ with genConstraint (upGamma {2} Γ) (upExp {2} x) (TVar zero) 
                                        | genConstraintAlternatives (upGamma {2} Γ) (upAlts {2} alts) (TVar zero) (TVar (suc zero))
  ... | C₁ , p₁ | C₂ , p₂ = _ , Case p₁ p₂ 
