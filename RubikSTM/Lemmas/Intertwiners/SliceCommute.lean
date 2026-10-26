import RubikSTM.Proofs.Intertwiners.SliceCommute
import RubikSTM.Definitions.Intertwiners.SurfaceFlip
set_option autoImplicit false

theorem RubikIntertwiner.slice_commute :
    ∀ {n : ℕ} (b : Fin n) (hb : 0 < b.val ∧ b.val + 1 < n) (a : Rubik.Axis) (l : Fin n) (h₁ : l ≠ b) (h₂ : l ≠ b.rev), Commute (RubikIntertwiner.surfaceFlip b hb) (Rubik.sliceQuarter n a l) :=
  @proof_RubikIntertwiner_slice_commute
