open import OutsideIn.Prelude
open import OutsideIn.X
module OutsideIn(x : X) where
  open X (x) public
  open import OutsideIn.Prelude public
  open import Data.Vec public hiding ([_]) 
  import OutsideIn.Constraints as C
  import OutsideIn.TypeSchema as TS
  import OutsideIn.Expressions as E
  import OutsideIn.Environments as V
  import OutsideIn.TopLevel as TL
  import OutsideIn.Inference as I
  open E (x) public
  open TL(x) public
  open TS(x) public
  open I (x) public
  open V (x) public
  open C (x)
