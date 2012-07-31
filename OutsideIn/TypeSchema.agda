open import OutsideIn.Prelude
open import OutsideIn.X
module OutsideIn.TypeSchema(x : X) where
  open X(x)
  open import Data.Vec hiding (_>>=_)

  data NameType : Set where
    Regular : NameType
    Datacon : ℕ → NameType

  data TypeSchema ( n : Set) : NameType → Set where
    ∀′_·_⇒_ : (v : ℕ) → QConstraint (n ⨁ v) → Type (n ⨁ v) → TypeSchema n Regular
    DC∀′_,_·_⇒_⟶_ : (a b : ℕ){l : ℕ} → QConstraint ((n ⨁ a) ⨁ b) → Vec (Type ((n ⨁ a) ⨁ b)) l → n → TypeSchema n (Datacon l)

  private
    module PlusN-f n = Functor (Monad.is-functor (PlusN-is-monad {n}))
    module Vec-f {n} = Functor (vec-is-functor {n})
    module Type-f    = Functor (type-is-functor)
    module QC-f      = Functor (qconstraint-is-functor)

  private
    fmap-schema : {A B : Set}{x : NameType} → (A → B) → TypeSchema A x → TypeSchema B x
    fmap-schema f (∀′ n · Q ⇒ τ) = ∀′ n · QC-f.map (pn.map f) Q ⇒ Type-f.map (pn.map f) τ
        where module pn = PlusN-f n
    fmap-schema f (DC∀′ a , b · Q ⇒ τs ⟶ K) = DC∀′ a , b · QC-f.map (pb.map (pa.map f)) Q
                                                          ⇒ map (Type-f.map (pb.map (pa.map f))) τs 
                                                          ⟶ f K
        where module pa = PlusN-f a
              module pb = PlusN-f b


    fmap-schema-id : {A : Set}{x : NameType} {f : A → A} → isIdentity f → isIdentity (fmap-schema {A}{A}{x} f)
    fmap-schema-id isid {∀′ n · Q ⇒ τ} = cong₂ (∀′_·_⇒_ n) (QC-f.identity (pn.identity isid)) (Type-f.identity (pn.identity isid))
       where module pn = PlusN-f n
    fmap-schema-id isid {DC∀′ a , b · Q ⇒ τs ⟶ K} = cong₃ (DC∀′_,_·_⇒_⟶_ a b) 
                                                           (QC-f.identity (pb.identity (pa.identity isid))) 
                                                           (Vec-f.identity (Type-f.identity (pb.identity (pa.identity isid)))) 
                                                           isid
        where module pa = PlusN-f a
              module pb = PlusN-f b


    fmap-schema-comp :  {A B C : Set}{s : NameType} {f : A → B} {g : B → C} {x : TypeSchema A s}
                     → fmap-schema (g ∘ f) x ≡ fmap-schema g (fmap-schema f x)
    fmap-schema-comp {x = ∀′ n · Q ⇒ τ} = cong₂ (∀′_·_⇒_ n) (trans (cong (λ t → QC-f.map t Q)
                                                                         (extensionality (λ x → pn.composite)) )
                                                                   QC-f.composite)
                                                            (trans (cong (λ t → Type-f.map t τ)
                                                                         (extensionality (λ x → pn.composite)) )
                                                                   Type-f.composite)
        where module pn = PlusN-f n
    fmap-schema-comp {x = DC∀′ a , b · Q ⇒ τs ⟶ K} = cong₃ (DC∀′_,_·_⇒_⟶_ a b) 
                                                           (trans (cong (λ t → QC-f.map t Q) (extensionality (λ b → 
                                                                        trans (cong (λ t → pb.map t b) (extensionality (λ x → pa.composite)))
                                                                              pb.composite)))
                                                                  QC-f.composite) 
                                                           (trans (cong (λ t → map t τs) (extensionality (λ τ → 
                                                                        trans (cong (λ t → Type-f.map t τ) (extensionality (λ b → 
                                                                              trans (cong (λ t → pb.map t b) (extensionality (λ x → pa.composite)))
                                                                                    pb.composite)))
                                                                              Type-f.composite)))
                                                                  Vec-f.composite) 
                                                           refl
        where module pa = PlusN-f a
              module pb = PlusN-f b

  type-schema-is-functor : ∀{s} → Functor (λ x → TypeSchema x s)
  type-schema-is-functor = record { map       = fmap-schema
                                  ; identity  = fmap-schema-id
                                  ; composite = fmap-schema-comp
                                  }
