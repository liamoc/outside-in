open import OutsideIn.Prelude
open import OutsideIn.X
module OutsideIn.TopLevel(x : X) where
  import OutsideIn.Expressions as E 
  open E(x)
  open X(x)

  data Program (ev : Set)(tv : Set) : Set where
    end : Program ev tv
    bind₁_,_ : ∀ {s} → Expression ev tv s → Program (Ⓢ ev) tv → Program ev tv
    bind₂_·_∷_⇒_,_ : ∀ {s} → (n : ℕ) → Expression ev (tv ⨁ n) s 
                   → QConstraint (tv ⨁ n) → Type (tv ⨁ n) 
                   → Program (Ⓢ ev) tv → Program ev tv
