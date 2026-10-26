import RubikSTM.Proofs.Payloads.BaselineAction
import Mathlib
import RubikSTM.Definitions.Payloads.Realizes
set_option autoImplicit false

theorem RubikPayload.baselineAction :
    ∀ {n : ℕ} {A Y : Finset (Fin n)} (h : RubikPayload.Admissible A Y)
  {a b : Fin n} (ha : a ∈ A) (hbY : b ∈ Y)
  (hb : 0 < b.val ∧ b.val + 1 < n) (i : Fin 24), RubikPayload.columnBaseline Y (RubikGeometry.lab a b i) = RubikGeometry.lab a b (RubikGeometry.gen7 i) ∧
  RubikPayload.columnBaseline Y (RubikOrbit.minusLab a b hb i) =
    RubikOrbit.minusLab a b hb (RubikOrbit.minusB i) :=
  @proof_RubikPayload_baselineAction
