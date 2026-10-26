import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.UniversalOwnProfile
import RubikSTM.Lemmas.OBTM.Compiler.OddRowFrame
import RubikSTM.Lemmas.WordConstruction.SameFrameTelescopes
import RubikSTM.Lemmas.WordConstruction.ConjugatedEndpoint
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_common_frame_program {G X : Type*} [Group G] [MulAction G X]
  (Q : G) (hQ : Q^2=1) (t j : ℕ) (hj : 1≤j) (hjt : j≤t) (ht : t%2=1)
  (Fs : List G) (x y : X)
  (hraw : Fs.reverse.prod • (Q^((j-1)%2) • x) = Q^((j-1)%2) • y) :
  (Fs.map (fun F => Q^(t-j)*F*Q^(j-1))).reverse.prod =
    (Q^((j-1)%2))⁻¹ * Fs.reverse.prod * Q^((j-1)%2) ∧
  (Fs.map (fun F => Q^(t-j)*F*Q^(j-1))).reverse.prod • x = y := by
  have he : (fun F : G => Q^(t-j)*F*Q^(j-1)) =
      (fun F => (Q^((j-1)%2))⁻¹*F*Q^((j-1)%2)) := by
    funext F
    exact RubikOBTMCompiler.odd_row_frame Q F hQ t j hj hjt ht
  rw [he]
  exact ⟨RubikCompiler.sameFrameTelescopes _ _,
    RubikCompiler.conjugatedEndpoint _ _ _ _ hraw⟩

#print axioms proof_RubikOBTMCompiler_common_frame_program
