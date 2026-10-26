import RubikSTM.Proofs.Surface.SurfaceCover
import RubikSTM.Definitions.Surface.GenericRange
set_option autoImplicit false
open Rubik RubikGeometry RubikGlobal
open scoped Classical

theorem RubikGlobal.surface_cover :
    ∀ {n : ℕ} (s : Rubik.Sticker n), RubikCore.IsCore s ∨ (∃ i : RubikGlobal.I n, s ∈ RubikGlobal.WingRange i) ∨ (∃ i : RubikGlobal.I n, s ∈ RubikGlobal.DiagonalRange i) ∨ (∃ i : RubikGlobal.I n, s ∈ RubikGlobal.CrossRange i) ∨ (∃ p : RubikGlobal.Q n, s ∈ RubikGlobal.GenericRange p) :=
  @proof_RubikGlobal_surface_cover
