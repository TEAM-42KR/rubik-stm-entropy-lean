import RubikSTM.Proofs.OBTM.Periodic.NativeBookSupplyOfCoordinates
import RubikSTM.Definitions.OBTM.Global.RectangleCompiler
import RubikSTM.Definitions.OBTM.Periodic.CoordinateBounds
set_option autoImplicit false
open scoped Classical

theorem RubikOBTM.Periodic.native_book_supply_of_coordinates :
    ∀ (hT : 0 < RubikOBTM.Finite.period) (hC : RubikOBTM.Finite.nativeC.Nonempty)
    (θ ρ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hcoords : RubikOBTM.Periodic.CoordinateBounds hT RubikOBTM.Finite.nativeC hC
      RubikOBTM.Finite.periodicAct θ ρ), RubikOBTM.Global.BookSupply :=
  @proof_RubikOBTM_Periodic_native_book_supply_of_coordinates
