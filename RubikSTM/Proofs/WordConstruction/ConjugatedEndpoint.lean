import Mathlib
import RubikSTM.Lemmas.WordConstruction.SameFrameTelescopes
set_option autoImplicit false

theorem proof_RubikCompiler_conjugatedEndpoint {G X : Type*} [Group G] [MulAction G X]
  (a : G) (Fs : List G) (x y : X)
  (hraw : Fs.reverse.prod • (a • x) = a • y) :
  (Fs.map (fun F => a⁻¹ * F * a)).reverse.prod • x = y := by
  rw [RubikCompiler.sameFrameTelescopes]
  simp only [mul_smul]
  rw [hraw]
  exact inv_smul_smul a y

#print axioms proof_RubikCompiler_conjugatedEndpoint
