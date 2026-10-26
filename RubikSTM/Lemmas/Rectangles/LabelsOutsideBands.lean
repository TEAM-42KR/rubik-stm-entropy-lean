import RubikSTM.Proofs.Rectangles.LabelsOutsideBands
import RubikSTM.Definitions.Rectangles.PayloadInterface
set_option autoImplicit false

theorem RubikRectangle.labels_outside_bands :
    ∀ {n : ℕ} {a b : Fin n} (hg : RubikGeometry.Generic n a b) (hb : 0 < b.val ∧ b.val + 1 < n) (H : Finset (Fin n)) (hH : ∀ c ∈ H, RubikPayload.Half c) (haH : a ∉ H) (hbH : b ∉ H) (i : Fin 24), ¬ RubikBand.Bands H (RubikGeometry.lab a b i) ∧ ¬ RubikBand.Bands H (RubikOrbit.minusLab a b hb i) :=
  @proof_RubikRectangle_labels_outside_bands
