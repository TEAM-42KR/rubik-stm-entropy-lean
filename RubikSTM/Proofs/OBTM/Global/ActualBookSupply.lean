import RubikSTM.Definitions.OBTM.Global.RectangleCompiler
import RubikSTM.Lemmas.OBTM.Periodic.NativeBookSupplyOfCoordinates
import RubikSTM.Lemmas.OBTM.Spectral.ActualPeriodGaps
import RubikSTM.Lemmas.OBTM.Spectral.CoordinateBoundsOfPeriodGaps
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator

theorem proof_RubikOBTM_Global_actual_book_supply : RubikOBTM.Global.BookSupply := by
  obtain ⟨θ, η, hθ0, hθ1, hη0, hη1, hsingle, hdouble⟩ :=
    RubikOBTM.Spectral.actual_period_gaps
  obtain ⟨ρ, hρ0, hρ1, hcoordinates⟩ :=
    RubikOBTM.Spectral.coordinate_bounds_of_period_gaps
      RubikOBTM.Spectral.actualPeriodPositive RubikOBTM.Finite.nativeC
      RubikOBTM.Spectral.actualAlphabetNonempty RubikOBTM.Finite.periodicAct
      θ η hθ0 hθ1 hη0 hη1 hsingle hdouble
  exact RubikOBTM.Periodic.native_book_supply_of_coordinates
    RubikOBTM.Spectral.actualPeriodPositive RubikOBTM.Spectral.actualAlphabetNonempty
    θ ρ hθ0 hθ1 hρ0 hρ1 hcoordinates
