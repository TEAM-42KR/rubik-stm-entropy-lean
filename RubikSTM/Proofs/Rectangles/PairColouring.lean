import RubikSTM.Definitions.Rectangles.PayloadInterface
import RubikSTM.Lemmas.WordConstruction.PhysicalWordColouring
set_option autoImplicit false

open RubikRectangle RubikPayload

theorem proof_RubikRectangle_pairColouring {n : ℕ} (a b : Fin n) (hb : 0 < b.val ∧ b.val + 1 < n)
    (w : List (Rubik.Move n)) (g : Pair) (h : ActsPair a b hb w g)
    (c : Rubik.Colouring n) :
    view (Rubik.applyWord w c) a b hb = rawAction g (view c a b hb) := by
  have hi (i : Fin 24) : (RubikBand.wordPerm w)⁻¹ (RubikGeometry.lab a b i) =
      RubikGeometry.lab a b (g.1⁻¹ i) := by
    apply (RubikBand.wordPerm w).injective
    simpa using (h.1 (g.1⁻¹ i)).symm
  have hj (i : Fin 24) : (RubikBand.wordPerm w)⁻¹ (RubikOrbit.minusLab a b hb i) =
      RubikOrbit.minusLab a b hb (g.2⁻¹ i) := by
    apply (RubikBand.wordPerm w).injective
    simpa using (h.2 (g.2⁻¹ i)).symm
  rw [RubikCompiler.physicalWordColouring]
  apply Prod.ext
  · funext i
    exact congrArg c (hi i)
  · funext i
    exact congrArg c (hj i)

#print axioms proof_RubikRectangle_pairColouring
