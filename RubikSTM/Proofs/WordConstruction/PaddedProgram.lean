import Mathlib
import RubikSTM.Lemmas.WordConstruction.PaddedLayer
import RubikSTM.Lemmas.WordConstruction.SameFrameTelescopes
import RubikSTM.Lemmas.WordConstruction.ConjugatedEndpoint
set_option autoImplicit false

theorem proof_RubikCompiler_paddedProgram {G X : Type*} [Group G] [MulAction G X]
  (B : G) (hB : B ^ 4 = 1) (t j : ℕ)
  (hj : 1 ≤ j) (hjt : j ≤ t) (ht : t % 4 = 1)
  (Fs : List G) (x y : X)
  (hraw : Fs.reverse.prod • (B ^ ((j-1) % 4) • x) =
    B ^ ((j-1) % 4) • y) :
  (Fs.map (fun F => B ^ (t-j) * F * B ^ (j-1))).reverse.prod =
      (B ^ ((j-1) % 4))⁻¹ * Fs.reverse.prod * B ^ ((j-1) % 4) ∧
    (Fs.map (fun F => B ^ (t-j) * F * B ^ (j-1))).reverse.prod • x = y := by
  have heq : (fun F : G => B ^ (t-j) * F * B ^ (j-1)) =
      (fun F => (B ^ ((j-1) % 4))⁻¹ * F * B ^ ((j-1) % 4)) := by
    funext F
    exact RubikCompiler.paddedLayer B F hB t j hj hjt ht
  rw [heq]
  exact ⟨RubikCompiler.sameFrameTelescopes _ _,
    RubikCompiler.conjugatedEndpoint _ _ _ _ hraw⟩

#print axioms proof_RubikCompiler_paddedProgram
